Require Import Coq.Classes.Morphisms.
Require Import bedrock2.Map bedrock2.Map.Decomp bedrock2.Lift1Prop bedrock2.Map.Separation. Import map.

Section SepProperties.
  Context {key value} {map : map key value} {ok : ok map}.
  Local Infix "*" := sep.

  Global Instance Proper_emp_iff : Proper (iff ==> iff1) emp. firstorder idtac. Qed.
  Global Instance Proper_emp_impl : Proper (Basics.impl ==> impl1) emp. firstorder idtac. Qed.
  Global Instance Proper_sep_iff1 : Proper (iff1 ==> iff1 ==> iff1) sep. firstorder idtac. Qed.
  Global Instance Proper_sep_impl1 : Proper (impl1 ==> impl1 ==> impl1) sep. firstorder idtac. Qed.

  Ltac t :=
    repeat match goal with
    | _ => progress subst
    | H:_ /\ _ |- _ => destruct H
    | H:exists _, _ |- _ => destruct H
    | H:disjoint (union _ _) _ |- _ => eapply disjoint_union_l in H; destruct H
    | H:disjoint _ (union _ _) |- _ => eapply disjoint_union_r in H; destruct H
    | _ => progress intuition idtac
    end.

  (* sep and sep *)
  Lemma sep_comm p q : iff1 (p*q) (q*p).
  Proof. cbv [iff1 sep split]; t; eauto 10 using union_comm, (fun m1 m2 => proj2 (disjoint_comm m1 m2)). Qed.
  Lemma sep_assoc p q r : iff1 ((p*q)*r) (p*(q*r)).
  Proof. cbv [iff1 sep split]; t; eauto 15 using eq_sym, union_assoc, ((fun m1 m2 m3 => proj2 (disjoint_union_l m1 m2 m3))), ((fun m1 m2 m3 => proj2 (disjoint_union_r m1 m2 m3))). Qed.
  Lemma sep_213 B A C : iff1 (A * (B * C)) (B * (A * C)).
  Proof. rewrite <-(sep_assoc _ B), (sep_comm _ B), sep_assoc. reflexivity. Qed.

  (* sep and ex1 *)
  Lemma sep_ex1_r {T} p (q:T->_) : iff1 (p * ex1 q) (ex1 (fun h => p * q h)).
  Proof. firstorder idtac. Qed.
  Lemma sep_ex1_l {T} p (q:T->_) : iff1 (ex1 q * p) (ex1 (fun h => q h * p)).
  Proof. rewrite sep_comm. rewrite sep_ex1_r. setoid_rewrite (sep_comm p). reflexivity. Qed.

  (* sep and emp *)
  Lemma sep_emp_emp p q : iff1 (sep (emp p) (emp q)) (emp (p /\ q)).
  Proof. cbv [iff1 sep emp split]; t; intuition eauto 20 using union_empty_l, disjoint_empty_l. Qed.
  Lemma sep_emp_r a b : iff1 (a * emp b) (emp b * a). eapply sep_comm. Qed.
  Lemma sep_emp_2 a b c : iff1 (a * (emp b * c)) (emp b * (a * c)).
  Proof. rewrite <-sep_assoc. rewrite (sep_comm a). rewrite sep_assoc. reflexivity. Qed.
  Lemma sep_emp_12 a b c : iff1 (emp a * (emp b * c)) (emp (a /\ b) * c).
  Proof. rewrite <-sep_assoc. rewrite sep_emp_emp. reflexivity. Qed.

  (* impl1 and emp *)
  Lemma impl1_l_sep_emp (a:Prop) b c : impl1 (emp a * b) c <-> (a -> impl1 b c).
  Proof. cbv [impl1 emp sep split]; t; rewrite ?union_empty_l; eauto 10 using union_empty_l, disjoint_empty_l. Qed.
  Lemma impl1_r_sep_emp a b c : (b /\ impl1 a c) -> impl1 a (emp b * c).
  Proof. cbv [impl1 emp sep split]; t; eauto 10 using union_empty_l, disjoint_empty_l. Qed.
End SepProperties.

Ltac set_evars := repeat match goal with |- context[?e] => is_evar e; set e end.
Ltac subst_evars := repeat match goal with x := ?e |- _ => is_evar e; subst x end.
Ltac normalize :=
  set_evars;
  (* COQBUG? Why is the repeat necessary? Why does it not work inside rewrite_strat? *)
  repeat (rewrite_strat (bottomup (terms @sep_emp_emp @sep_emp_r @sep_emp_12 @sep_emp_2 @sep_ex1_l @sep_ex1_r @sep_assoc)));
  subst_evars.
Ltac cancel_atom_goal1 P :=
  (* COQBUG: if I use fresh here, rewrite_strat fails *)
  pose proof (sep_213 P) as __PRIVATE_cancel_atom_goal1_ASDA;
  (rewrite_strat (try (bottomup (terms __PRIVATE_cancel_atom_goal1_ASDA))));
  clear __PRIVATE_cancel_atom_goal1_ASDA.
Ltac cancel_atom P :=
  eapply Proper_impl1_impl1; [ cbv [Basics.flip]; cancel_atom_goal1 P; eapply (Proper_sep_impl1 P _ (reflexivity _)) | reflexivity | reflexivity ].
Ltac cancel :=
  lazymatch goal with |- impl1 _ (sep _ _) => idtac end;
  set_evars;
  repeat match goal with |- impl1 _ (sep ?P _) => cancel_atom P end;
  subst_evars.