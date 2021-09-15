Require Import Coq.ZArith.ZArith.
Require Import compiler.FlatImp.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.simpl_rewrite.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Utility.Utility.
Require Import coqutil.Z.Lia.
Require Import coqutil.Macros.unique.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.Solver.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Map.TestLemmas.
Require Import bedrock2.Syntax.
Require Import coqutil.Datatypes.ListSet.
Require Import coqutil.Tactics.Simp.
Require Import compiler.Simulation.

Open Scope Z_scope.

Local Notation srcvar := String.string (only parsing).
Local Notation impvar := Z (only parsing).
Local Notation stmt  := (@FlatImp.stmt srcvar). (* input type *)
Local Notation stmt' := (@FlatImp.stmt impvar). (* output type *)
Local Notation bcond  := (@FlatImp.bcond srcvar).
Local Notation bcond' := (@FlatImp.bcond impvar).

Definition accessed_vars_bcond(c: bcond): list srcvar :=
  match c with
  | CondBinary _ x y => list_union String.eqb [x] [y]
  | CondNez x => [x]
  end.

Fixpoint live(s: stmt)(used_after: list srcvar): list srcvar :=
  match s with
  | SSet x y
  | SLoad _ x y _
  | SInlinetable _ x _ y =>
    list_union String.eqb [y] (list_diff String.eqb used_after [x])
  | SStore _ a x _ => list_union String.eqb [a; x] used_after
  | SStackalloc x _ body => list_diff String.eqb (live body used_after) [x]
  | SLit x _ => list_diff String.eqb used_after [x]
  | SOp x _ y z => list_diff String.eqb (list_union String.eqb [y; z] used_after) [x]
  | SIf c s1 s2 => list_union String.eqb
                              (list_union String.eqb (live s1 used_after) (live s2 used_after))
                              (accessed_vars_bcond c)
  | SSeq s1 s2 => live s1 (live s2 used_after)
  | SLoop s1 c s2 =>
    live s1 (list_union String.eqb (accessed_vars_bcond c) (list_union String.eqb used_after (live s2 [])))
  | SSkip => used_after
  | SCall binds _ args
  | SInteract binds _ args => list_union String.eqb args (list_diff String.eqb used_after binds)
  end.

(* old RegAlloc files:
https://github.com/mit-plv/bedrock2/tree/7cbae1a1caf7d19270d0fb37199f86eb8ea5ce4f/compiler/src/compiler
*)

Declare Scope option_monad_scope. Local Open Scope option_monad_scope.

Notation "c1 ;; c2" :=
  (match c1 with
   | Some _ => c2
   | None => None
   end)
  (at level 61, right associativity) : option_monad_scope.

Notation "x <- c1 ;; c2" :=
  (match c1 with
   | Some x => c2
   | None => None
   end)
  (at level 61, c1 at next level, right associativity) : option_monad_scope.

Notation "' pat <- c1 ;; c2" :=
  (match c1 with
   | Some pat => c2
   | None => None
   end)
  (at level 61, pat pattern, c1 at next level, right associativity) : option_monad_scope.

Scheme Equality for Syntax.access_size. (* to create access_size_beq *)
Scheme Equality for bopname. (* to create bopname_beq *)
Scheme Equality for bbinop. (* to create bbinop_beq *)

(* TODO List.list_eqb should not require an EqDecider instance *)
(* TODO move *)
Module Byte.
  Lemma eqb_spec: EqDecider Byte.eqb.
  Proof.
    intros. destruct (Byte.eqb x y) eqn: E; constructor.
    - apply Byte.byte_dec_bl. assumption.
    - apply Byte.eqb_false. assumption.
  Qed.
End Byte.

Module map.
  Class ops{K V: Type}(M: map.map K V) := {
    intersect: M -> M -> M; (* set intersection when interpreting maps as sets of tuples *)
  }.
End map.

#[export] Hint Resolve Byte.eqb_spec : typeclass_instances.

Definition assert(b: bool): option unit := if b then Some tt else None.

Section RegAlloc.

  Context {src2imp: map.map srcvar impvar}.
  Context {src2impOk: map.ok src2imp}.
  Context {imp2src: map.map impvar srcvar} {imp2srcOps: map.ops imp2src}.
  Context {imp2srcOk: map.ok imp2src}.

  (* "bindings" from impvar to srcvar that hold for sure after executing s:
     Q: how to implement loop case? Does it have to iterate until a fixpoint is reached?

     What if we just return those of s1?

     But if we chain it on top of a previous bindings, and s2 gets executed, that might invalidate some
     bindings --> need the concept of "update := add|remove" ??

     *)
  Definition assert_maps(m: imp2src)(y': impvar)(y: srcvar): option unit :=
    y0 <- map.get m y';; assert (String.eqb y0 y).

  Definition check_bcond(m: imp2src)(c: bcond)(c': bcond'): option unit :=
    match c, c' with
    | CondBinary op y z, CondBinary op' y' z' =>
      assert_maps m y' y;; assert_maps m z' z;; assert (bbinop_beq op op')
    | CondNez y, CondNez y' =>
      assert_maps m y' y
    | _, _ => None
  end.

  (* does 2 things at once: checks that the correct variables are read and computes the bindings
     that hold after executing the statement *)
  (* m: conservative underapproximation of which impvar stores which srcvar *)
  Fixpoint check(m: imp2src)(s: stmt)(s': stmt'){struct s}: option imp2src :=
    match s, s' with
    | SSet x y, SSet x' y' =>
      assert_maps m y' y;; Some (map.put m x' x)
    | SLoad sz x y ofs, SLoad sz' x' y' ofs' =>
      assert_maps m y' y;;
      assert (Z.eqb ofs ofs');;
      assert (access_size_beq sz sz');;
      Some (map.put m x' x)
    | SInlinetable sz x bs y, SInlinetable sz' x' bs' y' =>
      assert_maps m y' y;;
      assert (access_size_beq sz sz');;
      assert (List.list_eqb Byte.eqb bs bs');;
      Some (map.put m x' x)
    | SLit x z, SLit x' z' =>
      assert (Z.eqb z z');;
      Some (map.put m x' x)
    | SOp x op y z, SOp x' op' y' z' =>
      assert_maps m y' y;;
      assert_maps m z' z;;
      assert (bopname_beq op op');;
      Some (map.put m x' x)
    | SIf c s1 s2, SIf c' s1' s2' =>
      check_bcond m c c';;
      m1 <- check m s1 s1';;
      m2 <- check m s2 s2';;
      Some (map.intersect m1 m2)
    | SSeq s1 s2, SSeq s1' s2' =>
      m1 <- check m s1 s1';;
      check m1 s2 s2'
    | SLoop s1 c s2, SLoop s1' c' s2' =>
      m1 <- check m s1 s1';;
      check_bcond m1 c c';;
      m2 <- check m1 s2 s2';;
      (* need to check again because next loop iteration is done with m2 instead of m!! *)
      None
    | _, _ => None
    end.

End RegAlloc.
