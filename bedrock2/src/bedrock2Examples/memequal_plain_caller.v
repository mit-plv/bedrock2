(* A plain (non-leakage) caller of [memequal], whose spec is a leakage spec.
   Exercises SemanticsRelations.plain_of_leakage_call through
   ProgramLogic.straightline_call (its [straightline_call_from_leakage] variant),
   and the link-time discharge of the stackalloc-freeness side condition. *)
Require Import bedrock2.NotationsCustomEntry coqutil.Macros.WithBaseName.

Import Syntax Syntax.Coercions BinInt String List List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition memequal_twice := func! (x,y,n) ~> r {
  unpack! r0 = memequal(x, y, n);
  unpack! r1 = memequal(y, x, n);
  r = r0 & r1
}.

Require Import bedrock2.WeakestPrecondition bedrock2.Semantics bedrock2.ProgramLogic.
Require Import bedrock2.LeakageSemantics bedrock2.SemanticsRelations.
Require Import bedrock2Examples.memequal.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface bedrock2.Map.SeparationLogic.
Require Import coqutil.Tactics.Tactics coqutil.Word.Properties.
Require coqutil.Map.SortedListString.
Import Coq.Init.Byte coqutil.Byte.
Local Notation string := String.string.

Local Notation "xs $@ a" := (Array.array ptsto (bits.of_Z _ 1) a xs) (at level 10, format "xs $@ a").

Section WithParameters.
  Context {width} {BW: Bitwidth width}.
  Local Notation word := (bits width).
  Context {mem: map.map word byte}.
  (* concrete locals so that [straightline] can read variables by computation *)
  Local Instance locals: map.map string word := SortedListString.map _.
  Local Instance locals_ok: map.ok locals := SortedListString.ok _.
  (* The callee's spec is stated over a leakage ext_spec; the plain caller uses
     the corresponding plain ext_spec, obtained by forgetting the leakage. *)
  Context {ext_spec: LeakageSemantics.ExtSpec} {pick_sp: PickSp}.
  Existing Instance deleakaged_ext_spec.
  Import ProgramLogic.Coercions.

  Global Instance spec_of_memequal_twice : spec_of "memequal_twice" :=
    fnspec! "memequal_twice" (x y n : word) / (xs ys : list byte) (Rx Ry : mem -> Prop) ~> r,
    { requires t m := m =* xs$@x * Rx /\ m =* ys$@y * Ry /\
                      length xs = n :>Z /\ length ys = n :>Z;
      ensures t' m' := m=m' /\ t=t' /\ (r = 0 :>Z \/ r = 1 :>Z) /\
                       (r  = 1 :>Z <-> xs  = ys) }.

  Context {mem_ok: map.ok mem} {ext_spec_ok : ext_spec.ok ext_spec}.
  Existing Instance deleakaged_ext_spec_ok.

  (* The generic proof needs the side condition that nothing reachable from
     the callee uses stackalloc, which is only known at link time, so it is
     taken as a hypothesis here (instead of [program_logic_goal_for_function!]). *)
  Lemma memequal_twice_ok : forall functions, stackalloc_free_env functions ->
    program_logic_goal_for memequal_twice
      (map.get functions "memequal_twice" = Some memequal_twice ->
       spec_of_memequal functions -> spec_of_memequal_twice functions).
  Proof.
    intros functions Hsf.
    repeat straightline.
    straightline_call.
    { ssplit; try ecancel_assumption; assumption. }
    repeat straightline.
    straightline_call.
    { ssplit; try ecancel_assumption; assumption. }
    repeat straightline.
    ssplit; trivial.
    all: subst r; rewrite bits.unsigned_and.
    all: destruct H8 as [H8|H8], H11 as [H11|H11]; rewrite H8, H11 in *; cbn.
    all: solve [ left; reflexivity | right; reflexivity | assumption
               | rewrite H12; split; intro; symmetry; assumption ].
  Qed.

  Lemma link_memequal_twice : spec_of_memequal_twice (map.of_list &[,memequal_twice; memequal]).
  Proof.
    eapply memequal_twice_ok; try exact eq_refl; try eapply memequal_ok; try exact eq_refl.
    eapply stackalloc_free_env_of_list. exact eq_refl.
  Qed.
End WithParameters.
