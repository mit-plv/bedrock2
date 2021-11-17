Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.Notations.

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
  Class Allocable {A} (P : word.rep -> A -> mem -> Prop) :=
    {
    size_in_bytes : Z;
    size_in_bytes_mod
    : size_in_bytes mod Memory.bytes_per_word width = 0;
    P_to_bytes
    : forall px x,
        Lift1Prop.impl1 (P px x) (Memory.anybytes px size_in_bytes);
    P_from_bytes
    : forall px,
        Lift1Prop.impl1 (Memory.anybytes px size_in_bytes)
                        (Lift1Prop.ex1 (P px))
    }.

  (* FIXME if we need to roundtrip:

     Class Allocable {A} (P : word.rep -> A -> mem -> Prop) :=
       { alloc_sz: Z;
         alloc_length_ok bs := Z.of_nat (List.length bs) = alloc_sz;
         alloc_sz_ok : alloc_sz mod Memory.bytes_per_word width = 0;

         alloc_to_bytes : A -> list byte;
         alloc_of_bytes : forall bs: list byte, alloc_length_ok bs -> A;

         alloc_to_bytes_length_ok a: alloc_length_ok (alloc_to_bytes a);

         alloc_to_bytes_ok ptr bs:
           Lift1Prop.impl1
             (P ptr bs)
             (array ptsto (word.of_Z 1) ptr (alloc_to_bytes bs));
         alloc_of_bytes_ok ptr bs (Hlen: alloc_length_ok bs) :
           Lift1Prop.impl1
             (array ptsto (word.of_Z 1) ptr bs)
             (P ptr (alloc_of_bytes bs Hlen)) }.

     Lemma alloc_of_bytes_to_bytes
           {A} (P : word.rep -> A -> mem -> Prop)
           `{Allocable _ P} a Hlen:
       alloc_of_bytes (alloc_to_bytes a) Hlen = a.
     Proof. … Qed. *)

  Program Instance Allocable_scalar : Allocable scalar :=
    {| size_in_bytes := Memory.bytes_per_word width;
       size_in_bytes_mod := Z_mod_same_full _;
       P_to_bytes := scalar_to_anybytes;
       P_from_bytes := anybytes_to_scalar |}.

  Definition pred_sep {A} R (pred : A -> predicate) (v : A) tr' mem' locals':=
    (R * (fun mem => pred v tr' mem locals'))%sep mem'.

  (* identity used as a marker to indicate when something should be allocated *)
  Definition stack {A} (a : A) := a. 

  Lemma compile_stack {tr m l functions A} (v : A):
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      {AP : word.rep -> A -> map.rep -> Prop} `{Allocable A AP}
      (R: mem -> Prop) out_var,

      R m ->

      (forall out_ptr uninit m',
          sep (AP out_ptr uninit) R m' ->
          <{ Trace := tr;
             Memory := m';
             Locals := map.put l out_var out_ptr;
             Functions := functions }>
          k_impl
          <{ pred_sep (Memory.anybytes out_ptr size_in_bytes)
                      pred (nlet_eq [out_var] v k) }>) ->
      <{ Trace := tr;
         Memory := m;
         Locals := l;
         Functions := functions }>
      cmd.stackalloc out_var size_in_bytes k_impl
      <{ pred (nlet_eq [out_var] (stack v) k) }>.
  Proof.
    repeat straightline; split; eauto using size_in_bytes_mod.
    intros out_ptr mStack mCombined [out Hout]%P_from_bytes; repeat straightline.
    eapply WeakestPrecondition_weaken
      with (p1 := pred_sep (Memory.anybytes out_ptr size_in_bytes)
                           pred (let/n x as out_var eq:Heq := v in k x Heq)).
    - unfold pred_sep, Basics.flip; simpl.
      intros * [mem1 [mem2 ?]].
      exists mem2, mem1; intuition. apply map.split_comm; eauto.
    - eapply H1.
      exists mStack, m; intuition eauto. apply map.split_comm; eauto.
  Qed.

End with_parameters.

Arguments stack : simpl never.
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

(* FIXME I don't think eassumption is needed, and there might actually be multiple ?R m *)
(* must be applied before compile_simple_alloc 
   TODO: understand why
 *)
#[export] Hint Extern 10 =>
  simple eapply compile_stack; [eassumption | shelve] : compiler.
#[export] Hint Extern 1 (pred_sep _ _ _ _ _ _) =>
  clear_pred_seps; shelve : compiler_cleanup_post.
