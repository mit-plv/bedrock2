Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import bedrock2.ZnWords.
Require Import coqutil.Word.Bitwidth.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Datatypes.Inhabited.
Require Import bedrock2.WordNotations. Local Open Scope word_scope.

Notation len := List.length.
Coercion Z.of_nat : nat >-> Z.

Fixpoint ands(Ps: list Prop): Prop :=
  match Ps with
  | P :: rest => P /\ ands rest
  | nil => True
  end.

Section ZnWordTests.
  Local Notation word := (bits 32).

  Goal forall (left0 right : word) (xs : list word),
    Zmod.unsigned (Zmod.sub right left0) = 8 * Z.of_nat (Datatypes.length xs) ->
    forall (x : list word) (x1 x2 : word),
    Zmod.unsigned (Zmod.sub x2 x1) = 8 * Z.of_nat (Datatypes.length x) ->
    Zmod.unsigned (Zmod.sub x2 x1) <> 0 ->
    Zmod.unsigned
      (Zmod.sub x2
         (Zmod.add
            (Zmod.add x1 (Zmod.slu (Zmod.sru (Zmod.sub x2 x1) 4) 3))
            (bits.of_Z 32 8))) =
    8 *
    Z.of_nat
      (Datatypes.length x -
       S (Z.to_nat (Zmod.unsigned (Zmod.sub (Zmod.add x1 (Zmod.slu (Zmod.sru (Zmod.sub x2 x1)
           4) 3)) x1) / Zmod.unsigned (bits.of_Z 32 8)))).
  Proof.
    intros. ZnWords.
  Qed.

  Goal forall a : word,
    let arguments := [a] in
    forall (vs : list word),
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
    len (List.firstn (Z.to_nat (\[a ^+ /[8] ^- a] / 4)) ([w1_0] ++ [w1] ++ List.skipn 2 vs))
    = Z.to_nat (\[a ^+ /[8] ^- a] / 4).
  Proof.
    intros. ZnWordsL.
  Qed.

  Goal forall (a a' SZ: word) (T: Type) (f: T -> nat) (vs1: T),
      Zmod.unsigned (Zmod.sub a' a) mod Zmod.unsigned SZ = 0 ->
      f vs1 = Z.to_nat (Zmod.unsigned (Zmod.sub a' a) / Zmod.unsigned SZ) ->
      Zmod.add a (bits.of_Z 32 (Zmod.unsigned (bits.of_Z 32 (Zmod.unsigned SZ))
                             * Z.of_nat (f vs1))) = a'.
  Proof.
    intros.
    try ZnWords.
    (* This rewrite should not be needed, but it seems to be a limitation of lia:
       https://github.com/coq/coq/issues/15583
       TODO remove the rewrite if lia is fixed. *)
    all: rewrite H0; ZnWords.
  Qed.

End ZnWordTests.

Section ZnWordTests64.
  Local Notation word := (bits 64).

  (* A word disequality must survive as a disequality on the unsigned values. *)
  Goal forall (w : word) (l : Z),
    w <> bits.of_Z 64 0 ->
    (0 < \[w] < 2 ^ 64 -> 0 <= l < 64) ->
    0 <= l <= 64.
  Proof. intros. ZnWords. Qed.

  (* The result of a bitwise operation is known to lie below 2 ^ 64. *)
  Goal forall a b c : word,
    \[a] + 2 ^ 64 * \[b] = \[Zmod.and c (bits.of_Z 64 4294967295)] -> \[b] < 1.
  Proof. intros. ZnWords. Qed.

  Goal forall a b c d : word,
    \[a] + 2 ^ 64 * \[b] = \[Zmod.or c d] -> \[b] < 1.
  Proof. intros. ZnWords. Qed.

  Goal forall a b c d : word,
    \[a] + 2 ^ 64 * \[b] = \[Zmod.xor c d] -> \[b] < 1.
  Proof. intros. ZnWords. Qed.

  Goal forall a b c : word,
    \[a] + 2 ^ 64 * \[b] = \[Zmod.not c] -> \[b] < 1.
  Proof. intros. ZnWords. Qed.

  Goal forall a b c d : word,
    \[a] + 2 ^ 64 * \[b] = \[Zmod.add c d] -> \[b] < 1.
  Proof. intros. ZnWords. Qed.
End ZnWordTests64.

(* List-length goals that used to need listZnWords / ZnWordsL: *)
Section ListLengthTests.
  Local Notation word := (bits 32).

  Goal forall (l: list word) (n: nat), (n <= len l)%nat -> len (List.firstn n l) = n.
  Proof. intros. ZnWords. Qed.

  Goal forall (l: list word) (n: nat), len (List.skipn n l) = (len l - n)%nat.
  Proof. intros. ZnWords. Qed.

  Goal forall (l: list word) (f: word -> word), Z.of_nat (len (List.map f l)) = len l.
  Proof. intros. ZnWords. Qed.

  Goal forall (x: word) (n: nat) (a: word), \[a] + len (List.repeat x n) = \[a] + n.
  Proof. intros. ZnWords. Qed.

  Goal forall (x: word) (n: nat), len (List.unfoldn (fun w => w ^+ /[1]) n x) = n.
  Proof. intros. ZnWords. Qed.

  Goal forall (l: list word) (i: nat) (v: word),
      (i < len l)%nat -> len (List.upd l i v) = len l.
  Proof. intros. ZnWords. Qed.

  Goal forall (a b c: word) (l: list word), len ([a; b] ++ l ++ [c]) = (3 + len l)%nat.
  Proof. intros. ZnWords. Qed.

  Goal forall (a b c: word), len [a; b; c] = 3%nat.
  Proof. intros. ZnWords. Qed.

  (* lengths inside hypotheses (former ZnWordsL) *)
  Goal forall (l: list word) (n: nat) (p q: word),
      \[q ^- p] = 4 * len (List.skipn n l) ->
      (n <= len l)%nat ->
      \[q ^- p] + 4 * n = 4 * len l.
  Proof. intros. ZnWords. Qed.

  Goal forall (l1 l2: list word) (x: word),
      \[x] = len (l1 ++ x :: l2) -> \[x] = len l1 + len l2 + 1.
  Proof. intros. ZnWords. Qed.

  (* boolean variables in ifs get case-split (former listZnWords behavior) *)
  Goal forall (b: bool) (x: Z) (l: list word),
      x = (if b then Z.of_nat (len l) else 2) -> 0 <= x.
  Proof. intros. ZnWords. Qed.

  Goal forall (b: bool) (l1 l2: list word) (n: Z),
      n = len (if b then l1 else l2) -> 0 <= n.
  Proof. intros. ZnWords. Qed.

  (* a plain word goal is unaffected *)
  Goal forall (a b: word), \[a] < \[b] -> \[a] <> \[b].
  Proof. intros. ZnWords. Qed.
End ListLengthTests.
