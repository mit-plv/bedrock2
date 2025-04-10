From Coq Require Import BinInt String List InitialRing.
From bedrock2 Require Import BasicC64Semantics WeakestPrecondition ProgramLogic.
Import ListNotations ProgramLogic.Coercions SeparationLogic Array Scalars.
Local Open Scope string_scope. Local Open Scope Z_scope.

(** * Specification *)

Local Notation eval := (fold_right (fun (a : word) (s : Z) => a + 2^64*s) 0).
Local Notation array := (array scalar (word.of_Z 8)). (* 8 = array stride *)
Local Instance spec_of_long_sub_4 : spec_of "long_sub_4" :=
  fnspec! "long_sub_4" (p_r p_x p_y b : word) / (x y r : list word) R ~> b_out,
  { requires t m := (* memory [m] contains 3 arrays with arbitrary aliasing *)
      m =*> array p_x x /\ m =*> array p_y y /\     m =* array p_r r ⋆ R /\
      length x = 4%nat /\ length y = 4%nat /\ length r = 4%nat /\ b < 2;
    ensures T M := T = t /\ exists (r : list word), M =* array p_r r ⋆ R /\
      length r = 4%nat /\ eval r - 2^256*b_out = eval x - eval y - b }.

(** * Implementation *)

Require Import bedrock2.NotationsCustomEntry bedrock2Examples.full_sub.

Definition long_sub_4 := func! (p_r, p_x, p_y, b) ~> b {
    unpack! s0, b = full_sub(load(p_x),          load(p_y),          b);
    unpack! s1, b = full_sub(load(p_x+$8),       load(p_y+$8),       b);
    unpack! s2, b = full_sub(load(p_x+$8+$8),    load(p_y+$8+$8),    b);
    unpack! s3, b = full_sub(load(p_x+$8+$8+$8), load(p_y+$8+$8+$8), b);
    store(p_r,          s0);
    store(p_r+$8,       s1);
    store(p_r+$8+$8,    s2);
    store(p_r+$8+$8+$8, s3) (* [b] is returned per declaration above *)
}.

(** * Proof *)

Import coqutil.Tactics.Tactics bedrock2.ZnWords.

Local Ltac lists_into_elements := repeat match goal with
  | H : length ?l = ?n |- _ =>  constr_eq true ltac:(isnatcst n);
  let x := fresh l "0" in destruct l as [(*nil*)|x l]; inversion H; clear H end.

Local Existing Instance spec_of_full_sub. (* use this spec for [full_sub] *)
Lemma long_sub_4_correct : program_logic_goal_for_function! long_sub_4.
Proof.
  straightline. destruct_products. lists_into_elements. unfold array, array in *.
  repeat (straightline || straightline_call || ZnWords). (* postcondition: *)
  eexists [_;_;_;_]. intuition try ecancel_assumption. unfold eval. ZnWords.
Qed.



(** * Linking Proof *)

From coqutil Require Import WithBaseName.
Definition long_sub_4_funcs := &[, long_sub_4; full_sub].

Lemma link_full_sub : spec_of_long_sub_4 (Interface.map.of_list long_sub_4_funcs).
Proof. apply long_sub_4_correct; try apply full_sub_ok; trivial. Qed.

(** * Extraction *)

From bedrock2 Require Import ToCString.
Redirect "full_sub.br2.c" Compute c_module long_sub_4_funcs.
