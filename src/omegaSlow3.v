Require Import Omega.

Definition mygoal := forall 
(P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12: Prop)
(w : nat)
(firstFree : nat)
(v v0 : nat)
(H : S v <= v0)
(H0 : firstFree <= v)
(x : nat)
(H1 : S v <= x /\ S x <= S v0 \/ P1)
(H2 : S v <= v0 /\ S v0 <= S v0 \/ P2)
(H3 : S v <= v /\ S v <= S v0 \/ P3)
(H4 : S v <= firstFree /\ S firstFree <= S v0 \/ P8)
(H5 : firstFree <= x /\ S x <= S v \/ P4)
(H6 : firstFree <= v0 /\ S v0 <= S v \/ P5)
(H7 : firstFree <= v /\ S v <= S v \/ P6)
(H8 : firstFree <= firstFree /\ S firstFree <= S v \/ P7)
(H9 : firstFree <= x /\ S x <= S (S v0) -> P9)
(H10 : firstFree <= v0 /\ S v0 <= S (S v0) -> P10)
(H11 : firstFree <= v /\ S v <= S (S v0) -> P11)
(H12 : firstFree <= firstFree /\ S firstFree <= S (S v0) -> P12)
,
(S (S v0) <= firstFree /\ S firstFree <= firstFree)
.

Goal mygoal.
  unfold mygoal. intros. clear H10 H11 H12. Fail Time omega. (* 0.191 secs *) 
Abort.

Goal mygoal.
  unfold mygoal. intros. (*Timeout 60 omega. Timeout! *)
Abort.
