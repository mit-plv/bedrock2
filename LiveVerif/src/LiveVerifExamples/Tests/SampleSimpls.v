Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Datatypes.ZList.
Require bedrock2.WordNotations.
Require Import bedrock2.bottom_up_simpl.

Section Tests.

Local Notation width := 32.

Context {word: word.word 32} {word_ok: word.ok word}.

Local Hint Mode Word.Interface.word - : typeclass_instances.

Add Ring wring : (Properties.word.ring_theory (word := word))
    ((* too expensive: preprocess [autorewrite with rew_word_morphism], *)
     morphism (Properties.word.ring_morph (word := word)),
     constants [Properties.word_cst]).

Import ZList.List.ZIndexNotations. Local Open Scope zlist_scope.
Import bedrock2.WordNotations. Local Open Scope word_scope.

Ltac t := intros; bottom_up_simpl_in_goal; reflexivity.

Goal (forall a : Z, a = a + 0 -> a = a + 0 -> (a = a + 0) = (a = a)).
Proof. t. Qed.

Goal (forall (Q : list Z -> Prop) (n b : Z) (bs : list Z),
               (Q (List.repeatz b (n - n) ++ bs[2 / 4:] ++ List.repeatz b \[/[0]]) = Q bs) =
               (Q bs = Q bs)).
Proof. t. Qed.

Goal (forall (byte_of_Z : Z -> Byte.byte) (b : word) (bs : list Byte.byte),
               (List.repeatz (byte_of_Z \[b]) \[/[0]] ++ bs[\[/[0]]:] = bs) = (bs = bs)).
Proof. t. Qed.

Goal (forall w1 w2 w3 : word,
               w1 = /[1] -> w1 = w2 -> w2 = w3 -> w3 = w1 -> (w2 = /[1]) = (/[1] = /[1])).
Proof. t. Qed.

Goal (forall a b : word, (/[\[a ^+ b]] = a ^+ b) = (a ^+ b = a ^+ b)).
Proof. t. Qed.

Goal (forall (w : word) (z : Z), z = \[w] -> (/[z] = w) = (w = w)).
Proof. t. Qed.

Goal (forall (P : Z -> Prop) (a : word),
               P (\[a ^+ /[8] ^- a] / 4) -> P (\[a ^+ /[8] ^- a] / 4) = P 2).
Proof. t. Qed.

Goal (forall a b : Z,
               (a + a, a + 1) = (2 * a, 1 + b) ->
               ((a + a, a + 1) = (2 * a, 1 + b)) = ((2 * a, a + 1) = (2 * a, 1 + b))).
Proof. t. Qed.

Goal (forall a b c : Z,
               a + a + a = b -> a + a + a = c -> (a + a + a = b) = (3 * a = b)).
Proof. t. Qed.

Goal (forall a b c : Z,
               3 * a = b -> a + a + a = c -> (a + a + a = c) = (3 * a = c)).
Proof. t. Qed.

Goal (forall mtvec_base : Z,
               (/[4] ^* /[mtvec_base] ^+ /[144]
                ^+ /[4 *
                     Z.of_nat
                       (S
                          (Z.to_nat
                             (\[/[4] ^* /[Z.of_nat 29]
                                ^+ (/[4] ^* /[mtvec_base] ^+ /[28])
                                ^- (/[4] ^* /[mtvec_base] ^+ /[144])] / 4)))] =
                /[4] ^* /[mtvec_base] ^+ /[148]) =
               (/[4] ^* /[mtvec_base] ^+ /[148] = /[4] ^* /[mtvec_base] ^+ /[148])).
Proof. t. Qed.

Goal (forall (stack_hi : Z) (f : word -> Z),
               (f (/[stack_hi] ^+ /[-128]) = f (/[stack_hi] ^- /[128])) =
               (f (/[stack_hi] ^- /[128]) = f (/[stack_hi] ^- /[128]))).
Proof. t. Qed.

Goal (forall (T : Type) (l : list T) (a b c : T),
               ((a :: b :: c :: l)[:5] = a :: b :: c :: l[:2]) =
               (a :: b :: c :: l[:2] = a :: b :: c :: l[:2])).
Proof. t. Qed.

Goal (forall (A : Type) (l : list A) (x y z : A),
               (([|x; y|] ++ l)[:2] ++ ([|x; y; z|] ++ l)[2:] = x :: y :: z :: l) =
               (x :: y :: z :: l = x :: y :: z :: l)).
Proof. t. Qed.

Goal (forall a b : Z, 0 <= a + b < 2 ^ 32 -> (\[/[a + b]] - b = a) = (a = a)).
Proof. t. Qed.

Goal (forall (foo : Z -> word) (a : Z) (x y : word),
               \[x] + \[y] < 2 ^ 32 ->
               (\[foo (a + 0) ^+ x ^- foo a ^+ y] = \[x] + \[y]) =
               (\[x] + \[y] = \[x] + \[y])).
Proof. t. Qed.

Goal (forall z : Z, (/[\[/[z]]] = /[z]) = (/[z] = /[z])).
Proof. t. Qed.

Goal (forall i j k count d : Z,
               d <> 0 ->
               ((d * j - i * d + k * d * count) / d - count * k = j - i) =
               (j - i = j - i)).
Proof. t. Qed.

Goal (forall (A : Type) (xs ys : list A) (i j : Z),
               0 <= i <= 3 + j + i ->
               xs[i : 3 + i + j] = ys -> (xs[i : 3 + i + j] = ys) = (xs[i:][:j + 3] = ys)).
Proof. t. Qed.

Goal (forall (A : Type) (xs ys : list A) (i j : Z),
               0 <= i <= j ->
               xs[i:][:j - i] = ys -> (xs[i:][:j - i] = ys) = (xs[i : j] = ys)).
Proof. t. Qed.

Goal (forall (A : Type) (xs ys : list A),
               (len (xs ++ ys) = len xs + len ys) = (len xs + len ys = len xs + len ys)).
Proof. t. Qed.

Goal (forall (A : Type) (xs ys : list A) (i : Z),
               0 <= i < len ys ->
               (len (xs ++ ys ++ xs) = 2 * len xs + len ys) =
               (2 * len xs + len ys = 2 * len xs + len ys)).
Proof. t. Qed.

Goal (forall (A : Type) (ys : list A) (x : A) (i j : Z),
               0 <= i < len ys ->
               0 <= j < i -> (len ys[j := x][i := x] = len ys) = (len ys = len ys)).
Proof. t. Qed.

Goal (forall (A : Type) (xs ys : list A) (x : A) (i : Z),
               0 <= i < len ys ->
               (len (xs ++ ys[i := x] ++ xs) = 2 * len xs + len ys) =
               (2 * len xs + len ys = 2 * len xs + len ys)).
Proof. t. Qed.

Goal (forall (A : Type) (xs1 xs2 xs3 xs4 xs5 xs6 : list A),
               ((xs1 ++ xs2) ++ (xs3 ++ xs4 ++ xs5) ++ xs6 =
                xs1 ++ xs2 ++ xs3 ++ xs4 ++ xs5 ++ xs6) =
               (xs1 ++ xs2 ++ xs3 ++ xs4 ++ xs5 ++ xs6 =
                xs1 ++ xs2 ++ xs3 ++ xs4 ++ xs5 ++ xs6)).
Proof. t. Qed.

Goal (forall (A : Type) (l1 l2 : list A) (i : Z),
               len l1 = i -> ((l1 ++ l2)[:i] = l1) = (l1 = l1)).
Proof. t. Qed.

Goal (forall (A : Type) (l1 l2 : list A) (i : Z),
               len l1 = i -> ((l1 ++ l2)[0:][:i] = l1) = (l1 = l1)).
Proof. t. Qed.

Goal (forall (A : Type) (l1 l2 : list A) (i : Z),
               0 <= i <= len l1 -> ((l1 ++ l2)[:i] = l1[:i]) = (l1[:i] = l1[:i])).
Proof. t. Qed.

(* requires a different sidecond hook
Goal (forall (A : Type) (xs1 xs2 xs3 xs4 xs5 xs6 : list A) (i j k s : Z),
               0 <= j <= len xs3 ->
               s = len xs1 + len xs2 + len xs3 - j ->
               s <= i <= s + k ->
               k <= len xs4 ->
               (((xs1 ++ xs2) ++ (xs3[j:] ++ xs4[:k] ++ xs5) ++ xs6)[:i] =
                (xs1 ++ xs2 ++ xs3[j:] ++ xs4[:k])[:i]) =
               ((xs1 ++ xs2 ++ xs3[j:] ++ xs4[:k])[:i] =
                (xs1 ++ xs2 ++ xs3[j:] ++ xs4[:k])[:i])).
Proof. t. Qed. *)


Goal (forall (A : Type) (l1 l2 : list A) (x : A) (i : Z),
               len l1 = i ->
               ((l1 ++ [|x|] ++ l2)[:i + 1] = l1 ++ [|x|]) =
               ((l1 ++ x :: l2)[:i + 1] = l1 ++ [|x|])).
Proof. t. Qed.

End Tests.
