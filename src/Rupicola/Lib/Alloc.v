Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.Notations.

Local Open Scope Z_scope.

Section with_parameters.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

  (* To enable allocation of A terms via the predicate P, implement this class *)
  (* I is a type if indices to use if P can take additional arguments *)
  Class Allocable {I A} (P : I -> word.rep -> A -> Semantics.mem -> Prop) :=
    {
    size_in_bytes : Z;
    size_in_bytes_mod
    : size_in_bytes mod Memory.bytes_per_word Semantics.width = 0;
    P_to_bytes
    : forall px i x,
        Lift1Prop.impl1 (P i px x) (Memory.anybytes px size_in_bytes);
    P_from_bytes
    : forall px,
        Lift1Prop.impl1 (Memory.anybytes px size_in_bytes)
                        (Lift1Prop.ex1 (fun i => Lift1Prop.ex1 (P i px)))
    }.


  Definition pred_sep {A} R (pred : A -> predicate) (v : A) tr' mem' locals':=
    (R * (fun mem => pred v tr' mem locals'))%sep mem'.

  (* identity used as a marker to indicate when something should be allocated *)
  (*TODO: should this require finding the instance? probably not
   Definition alloc {p : Semantics.parameters} {A} {P : A -> @Semantics.mem p -> Prop} `{@Allocable p A P} (a : A) := a. *)
  Definition alloc {A} (a : A) := a. 

  Lemma compile_alloc
        {tr mem locals functions A} (v : A):
    let v := alloc v in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
           {I} {AP : I -> word.rep -> A -> map.rep -> Prop} `{Allocable I A AP}
           (R: _ -> Prop) out_var,

      R mem ->

      (let v := v in
       forall i out_ptr uninit m,
         sep (AP i out_ptr uninit) R m ->
         (<{ Trace := tr;
             Memory := m;
             Locals := map.put locals out_var out_ptr;
             Functions := functions }>
          k_impl
          <{ pred_sep (Memory.anybytes out_ptr size_in_bytes) pred (nlet_eq [out_var] v k) }>)) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>      
      cmd.stackalloc out_var size_in_bytes k_impl
      <{ pred (nlet_eq [out_var] v k) }>.
  Proof.
    repeat straightline.
    split; eauto using size_in_bytes_mod.
    intros out_ptr mStack mCombined Hplace%P_from_bytes.
    destruct Hplace as [i [out Hout]].
    repeat straightline.
    specialize (H1 i out_ptr out mCombined).     
    eapply WeakestPrecondition_weaken
      with (p1 := pred_sep (Memory.anybytes out_ptr size_in_bytes)
                           pred (let/n x as out_var eq:Heq := v in
                                 k x Heq)).
    2:{
      eapply H1.
      exists mStack;
        exists mem;
        intuition.
      apply map.split_comm; eauto.
    }
    {
      clear H1.
      unfold pred_sep;
        unfold Basics.flip;
        simpl.
      intros.
      destruct H1 as [mem1 [mem2 ?]].
      exists mem2; exists mem1;
        intuition.
      apply map.split_comm; eauto.
    }
  Qed.

  (* TODO: augment Rupicola tactics to handle this *)
  
End with_parameters.


Arguments alloc : simpl never.
Arguments size_in_bytes : simpl never.
Hint Extern 10 => simple eapply compile_alloc; shelve : compiler.
