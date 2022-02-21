Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import bedrock2.ZnWords.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Interface.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Datatypes.Inhabited.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.SepAutoArray bedrock2.SepAuto.
Open Scope Z_scope.

Local Hint Mode Word.Interface.word - : typeclass_instances.

Infix "^+" := word.add  (at level 50, left associativity).
Infix "^-" := word.sub  (at level 50, left associativity).
Infix "^*" := word.mul  (at level 40, left associativity).
Infix "^<<" := word.slu  (at level 37, left associativity).
Infix "^>>" := word.sru  (at level 37, left associativity).
Notation "/[ x ]" := (word.of_Z x)       (* squeeze a Z into a word (beat it with a / to make it smaller) *)
  (format "/[ x ]").
Notation "\[ x ]" := (word.unsigned x)   (* \ is the open (removed) lid of the modulo box imposed by words, *)
  (format "\[ x ]").                     (* let a word fly into the large Z space *)
Notation len := List.length.
Coercion Z.of_nat : nat >-> Z.

Fixpoint ands(Ps: list Prop): Prop :=
  match Ps with
  | P :: rest => P /\ ands rest
  | nil => True
  end.

Section ZnWordTests.
  Context {word: word.word 32} {word_ok: word.ok word}
          {mem: map.map word Init.Byte.byte} {mem_ok: map.ok mem}.

  Goal forall (left0 right : word) (xs : list word),
    word.unsigned (word.sub right left0) = 8 * Z.of_nat (Datatypes.length xs) ->
    forall (x : list word) (x1 x2 : word),
    word.unsigned (word.sub x2 x1) = 8 * Z.of_nat (Datatypes.length x) ->
    word.unsigned (word.sub x2 x1) <> 0 ->
    word.unsigned
      (word.sub x2
         (word.add
            (word.add x1 (word.slu (word.sru (word.sub x2 x1) (word.of_Z 4)) (word.of_Z 3)))
            (word.of_Z 8))) =
    8 *
    Z.of_nat
      (Datatypes.length x -
       S (Z.to_nat (word.unsigned (word.sub (word.add x1 (word.slu (word.sru (word.sub x2 x1)
           (word.of_Z 4)) (word.of_Z 3))) x1) / word.unsigned (word.of_Z 8)))).
  Proof.
    intros. ZnWords.
  Qed.

  Let at_addr(addr: word)(clause: word -> mem -> Prop): mem -> Prop := clause addr.
  Local Notation "addr |-> clause" := (at_addr addr clause)
    (at level 25, format "addr  |->  '[' clause ']'").

  Goal forall a : word,
    let arguments := [a] in
    forall (vs : list word) (R : mem -> Prop),
    len vs = 3%nat ->
    let w0 := List.nth 0 vs default in
    let w1_0 := List.nth 1 vs default in
    let w2_0 := List.nth 2 vs default in
    let w1_1 := List.nth 0 vs default in
    forall cond0 : bool,
    let w2_1 := List.nth 0 vs default in
    let w2_2 := if cond0 then w2_1 else w2_0 in
    ands [~ \[w2_0] < \[w1_0]; ~ \[w0] < \[w1_0]] ->
    let w1 := w1_1 in
    let w2 := w2_0 in
    ~ \[w2] < \[w1] ->
    forall m : mem,
    seps [a |-> word_array ([w1_0] ++ [w1] ++ List.skipn 2 vs); R] m ->
    (forall (vs0 vs1 : list word) (v : word) (vs2 : list word),
     vs0 = vs1 ++ [v] ++ vs2 /\ len vs1 = Z.to_nat (\[a ^+ /[8] ^- a] / 4) ->
     Lift1Prop.iff1
       (sep (a |-> word_array vs1)
          (sep ((a ^+ /[8]) |-> scalar v)
             ((a ^+ /[4 * S (Z.to_nat (\[a ^+ /[8] ^- a] / 4))]) |-> word_array vs2)))
       (a |-> word_array vs0)) ->
    forall m' : mem,
    sep ((a ^+ /[8]) |-> scalar w2)
      (sep R
         (sep
            (a |-> word_array
                     (List.firstn (Z.to_nat (\[a ^+ /[8] ^- a] / 4))
                        ([w1_0] ++ [w1] ++ List.skipn 2 vs)))
            ((a ^+ /[4 * S (Z.to_nat (\[a ^+ /[8] ^- a] / 4))]) |->
             word_array
               (List.skipn (S (Z.to_nat (\[a ^+ /[8] ^- a] / 4)))
                  ([w1_0] ++ [w1] ++ List.skipn 2 vs))))) m' ->
    len (List.firstn (Z.to_nat (\[a ^+ /[8] ^- a] / 4)) ([w1_0] ++ [w1] ++ List.skipn 2 vs)) =
    Z.to_nat (\[a ^+ /[8] ^- a] / 4).
  Proof.
    intros. list_length_rewrites_without_sideconds_in_goal. ZnWords.
  Qed.

  Goal forall (a a' SZ: word) (T: Type) (f: T -> nat) (vs1: T),
      word.unsigned (word.sub a' a) mod word.unsigned SZ = 0 ->
      f vs1 = Z.to_nat (word.unsigned (word.sub a' a) / word.unsigned SZ) ->
      word.add a (word.of_Z (word.unsigned (word.of_Z (word := word) (word.unsigned SZ))
                             * Z.of_nat (f vs1))) = a'.
  Proof.
    intros.
(*    Fail ZnWords.*)
    (* This rewrite should not be needed, but it seems to be a limitation of lia:
       https://github.com/coq/coq/issues/15583
       TODO remove the rewrite if lia is fixed. *)
(*    rewrite H0.*)
    ZnWords.
  Qed.

End ZnWordTests.
