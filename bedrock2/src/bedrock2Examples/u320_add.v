From Coq Require Import BinInt String List InitialRing.
From bedrock2 Require Import BasicC64Semantics WeakestPrecondition ProgramLogic.
Import ListNotations ProgramLogic.Coercions SeparationLogic Array Scalars.
Local Open Scope string_scope. Local Open Scope Z_scope.

(** * Specification *)

Local Notation eval := (fold_right (fun (a : word) (s : Z) => a + 2^64*s) 0).
Local Notation array := (array scalar (word.of_Z 8)).

Local Instance spec_of_u320_add : spec_of "u320_add" := 
    fnspec! "u320_add" (p_x p_y : word) / (x y r : list word) R ~> b,
    {
        requires t m :=
            m =* array p_x x ⋆ array p_y y ⋆ R 
            /\ length x = 5%nat /\ length y = 5%nat ;
        ensures T M := T = t /\ exists (r : list word), M =* array p_x r ⋆ array p_y y ⋆ R /\ 
        length r = 5%nat /\ 2^320*b + eval r = eval x + eval y  
    }.

(** * Implementation *)
Require Import bedrock2.NotationsCustomEntry bedrock2Examples.full_add.

Definition u320_add := func! (p_x, p_y) ~> b {
    b = $0;
    unpack! s0, b = br_full_add(load(p_x), load(p_y), b);
    unpack! s1, b = br_full_add(load(p_x + $8), load(p_y + $8), b);
    unpack! s2, b = br_full_add(load(p_x + $8 + $8), load(p_y + $8 + $8), b);
    unpack! s3, b = br_full_add(load(p_x + $8 + $8 + $8), load(p_y + $8 + $8 + $8), b);
    unpack! s4, b = br_full_add(load(p_x + $8 + $8 + $8 + $8), load(p_y + $8 + $8 + $8 + $8), b);

    store(p_x, s0);
    store(p_x + $8, s1);
    store(p_x + $8 + $8, s2);
    store(p_x + $8 + $8 + $8, s3);
    store(p_x + $8 + $8 + $8 + $8, s4)
}.

(** * Proof *)
Import coqutil.Tactics.Tactics bedrock2.ZnWords.

Local Existing Instance spec_of_full_add.

Local Ltac lists_into_elements := repeat match goal with
  | H : length ?l = ?n |- _ =>  constr_eq true ltac:(isnatcst n);
  let x := fresh l "0" in destruct l as [(*nil*)|x l]; inversion H; clear H end.

Local Existing Instance spec_of_full_add.
Lemma u320_add_correct : program_logic_goal_for_function! u320_add.
Proof.
    repeat straightline. lists_into_elements. unfold array in *.
    repeat (straightline || straightline_call || ZnWords).
    eexists [_ ; _ ; _ ; _ ; _]. intuition try ecancel_assumption.
    unfold eval. ZnWords. 
Qed.

(** * Linking Proof *)
From coqutil Require Import WithBaseName.
Definition u320_add_funcs := &[, u320_add; br_full_add].

Lemma link_full_add : spec_of_u320_add (Interface.map.of_list u320_add_funcs).
Proof. apply u320_add_correct; try apply full_add_ok; trivial. Qed.
