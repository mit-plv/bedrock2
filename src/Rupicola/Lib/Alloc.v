Require Import Rupicola.Lib.SeparationLogicImpl.
Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.Notations.

Local Open Scope Z_scope.

Section with_parameters.  
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  (* To enable allocation of A terms via the predicate P, implement this class *)
  (* I is a type if indices to use if P can take additional arguments *)
  Class Allocable {I A} (P : I -> word.rep -> A -> mem -> Prop) :=
    {
    size_in_bytes : Z;
    size_in_bytes_mod
    : size_in_bytes mod Memory.bytes_per_word width = 0;
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
        {tr m l functions A} (v : A):
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
           {I} {AP : I -> word.rep -> A -> map.rep -> Prop} `{Allocable I A AP}
           (R: mem -> Prop) out_var,

      R m ->

      (forall i out_ptr uninit m',
         sep (AP i out_ptr uninit) R m' ->
         (<{ Trace := tr;
             Memory := m';
             Locals := map.put l out_var out_ptr;
             Functions := functions }>
          k_impl
          <{ pred_sep (Memory.anybytes out_ptr size_in_bytes) pred (nlet_eq [out_var] v k) }>)) ->
      <{ Trace := tr;
         Memory := m;
         Locals := l;
         Functions := functions }>      
      cmd.stackalloc out_var size_in_bytes k_impl
      <{ pred (nlet_eq [out_var] (alloc v) k) }>.
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
        exists m;
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
  
End with_parameters.


Arguments alloc : simpl never.
Arguments size_in_bytes : simpl never.


(*TODO: speed up by combining pred_seps first and using 1 proper/ecancel_assumption?*)
Ltac clear_pred_seps :=   
  unfold pred_sep;
  repeat change (fun x => ?h x) with h;
  repeat match goal with
         | [ H : _ ?m |- _ ?m] =>
           eapply Proper_sep_impl1;
           [ eapply P_to_bytes | clear H m; intros H m | ecancel_assumption]
         end.
