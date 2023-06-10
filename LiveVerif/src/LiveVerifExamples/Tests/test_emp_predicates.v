(* -*- eval: (load-file "../../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Load LiveVerif.

Goal forall (T: Type) (elem: T -> word -> mem -> Prop) (elemSize: PredicateSize elem)
            (xs: list T) (n1 n2 n3: Z)
            (a0 a1 a2 a3 a4: word) (F1 F2: word -> mem -> Prop) (R: mem -> Prop) (m: mem),
    n1 - n2 = 0 ->
    <{ * F1 a0
       * emp (1 + 1 = 2)
       * array elem (n1 - n2) xs a1
       * array elem n3 nil a2
       * F2 a3
       * array (uint 8) (n1 - n2) ? a4
       * R }> m ->
    <{ * F1 a0
       * F2 a3
       * R }> m.
Proof.
  intros. repeat heapletwise_step.
Qed.

End LiveVerif.

Comments .**/ //.
