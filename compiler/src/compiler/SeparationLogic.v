Require Export Coq.Lists.List. Export ListNotations.
Require Export Coq.ZArith.BinInt. Open Scope Z_scope.
Require Export coqutil.Word.Interface coqutil.Word.Properties.
Require Export coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.rdelta coqutil.Tactics.destr.
Require Import coqutil.Tactics.rewr coqutil.Tactics.Tactics.
Require Export coqutil.Z.Lia.
Require Export coqutil.Datatypes.PropSet.
Require Export bedrock2.Lift1Prop.
Require Export bedrock2.Map.Separation.
Require Export bedrock2.Map.SeparationLogic.
Require Export bedrock2.Array.
Require Export bedrock2.Scalars.
Require Export bedrock2.ptsto_bytes.
Require Export compiler.SimplWordExpr.
Require Export riscv.Utility.Utility.
Require Import riscv.Utility.Encode.
Require Import riscv.Spec.Decode.

Infix "*" := sep : sep_scope.

Delimit Scope sep_scope with sep.
Arguments impl1 {T} (_)%sep (_)%sep.
Arguments iff1 {T} (_)%sep (_)%sep.

(* TODO does not get rid of %sep in printing as intended *)
Arguments sep {key} {value} {map} (_)%sep (_)%sep.


Lemma f_equal2: forall {A B: Type} {f1 f2: A -> B} {a1 a2: A},
    f1 = f2 -> a1 = a2 -> f1 a1 = f2 a2.
Proof. intros. congruence. Qed.

(* unifies two separation logic clauses syntactically, instantiating as many evars
   as it wants, but for subterms of type word, applies word solver instead of syntatic unify,
   and for subterms of type Z, applies lia instead of syntactic unify *)
Ltac wclause_unify OK :=
  lazymatch type of OK with
  | word.ok ?WORD =>
    lazymatch goal with
    | |- @eq ?T ?x ?y =>
      tryif first [is_evar x | is_evar y | constr_eq x y] then (
        reflexivity
      ) else (
        tryif (unify T (@word.rep _ WORD)) then (
          solve [solve_word_eq OK]
        ) else (
          tryif (unify T Z) then (
            solve [bomega]
          ) else (
            lazymatch x with
            | ?x1 ?x2 => lazymatch y with
                         | ?y1 ?y2 => refine (f_equal2 _ _); wclause_unify OK
                         | _ => fail "" x "is an application while" y "is not"
                         end
            | _ => lazymatch y with
                   | ?y1 ?y2 => fail "" x "is not an application while" y "is"
                   | _ => tryif constr_eq x y then reflexivity else fail "" x "does not match" y
                   end
            end
          )
        )
      )
    end
  | _ => fail 1000 "OK does not have the right type"
  end.


Section ptstos.
  Context {W: Words}.
  Context {mem : map.map word byte} {mem_ok: map.ok mem}.

  Definition bytes_per_word: Z := Z.of_nat (@Memory.bytes_per width Syntax.access_size.word).

  Definition ptsto_word(addr w: word): mem -> Prop :=
    ptsto_bytes (@Memory.bytes_per width Syntax.access_size.word) addr
                (LittleEndian.split _ (word.unsigned w)).

  Definition word_array: word -> list word -> mem -> Prop :=
    array ptsto_word (word.of_Z bytes_per_word).

  Definition iset := if Utility.width =? 32 then RV32IM else RV64IM.

  (* contains all the conditions needed to successfully execute instr, except
     that addr needs to be in the set of executable addresses, which is dealt with elsewhere *)
  Definition ptsto_instr(addr: word)(instr: Instruction): mem -> Prop :=
    (truncated_scalar Syntax.access_size.four addr (encode instr) *
     emp (verify instr iset) *
     emp ((word.unsigned addr) mod 4 = 0))%sep.

  Definition program(addr: word)(prog: list Instruction): mem -> Prop :=
    array ptsto_instr (word.of_Z 4) addr prog.

  Lemma invert_ptsto_instr: forall {addr instr R m},
    (ptsto_instr addr instr * R)%sep m ->
     verify instr iset /\
     (word.unsigned addr) mod 4 = 0.
  Proof.
    intros.
    unfold array, ptsto_instr in *.
    lazymatch goal with
    | H: (?T * ?P1 * ?P2 * R)%sep ?m |- _ =>
      assert ((T * R * P1 * P2)%sep m) as A by ecancel_assumption; clear H
    end.
    do 2 (apply sep_emp_r in A; destruct A as [A ?]).
    auto.
  Qed.

  Lemma invert_ptsto_program1: forall {addr instr R m},
    (program addr [instr] * R)%sep m ->
     verify instr iset /\
     (word.unsigned addr) mod 4 = 0.
  Proof.
    unfold program. intros. simpl in *. eapply invert_ptsto_instr.
    ecancel_assumption.
  Qed.

End ptstos.

(* This can be overridden by the user.
   The idea of a "tag" is that it's a subterm of a sepclause which is so unique that if
   the same tag appears both on the left and on the right of an iff1, we're sure that
   these two clauses should be matched & canceled with each other.
   "tag" should return any Gallina term. *)
Ltac tag P :=
  let __ := lazymatch type of P with
            | @map.rep _ _ _ -> Prop => idtac
            | _ => fail 10000 P "is not a sep clause"
            end in
  lazymatch P with
  | _ => fail "no recognizable tag"
  end.

(* This can be overridden by the user.
   The idea of "addr" is that if the addresses of two sepclauses are the same,
   we're sure that these two clauses should be matched & canceled with each other,
   even if they still contain many evars outside of their address.
   "addr" should return a Gallina term of type "word" *)
Ltac addr P :=
  let __ := lazymatch type of P with
            | @map.rep _ _ _ -> Prop => idtac
            | _ => fail 10000 P "is not a sep clause"
            end in
  lazymatch P with
  | ptsto ?A _ => A
  | ptsto_bytes _ ?A _ => A
  | ptsto_word ?A _ => A
  | ptsto_instr ?A _ => A
  | array _ _ ?A _ => A
  | word_array ?A _ => A
  | _ => fail "no recognizable address"
  end.

(* completely solves a sepclause equality or fails *)
Ltac sepclause_eq OK :=
  match goal with
  | |- ?G => assert_fails (has_evar G);
             wclause_unify OK
  | |- ?lhs = ?rhs => let tagL := tag lhs in
                      let tagR := tag rhs in
                      constr_eq tagL tagR;
                      wclause_unify OK
  | |- ?lhs = ?rhs => let addrL := addr lhs in
                      let addrR := addr rhs in
                      assert_fails (has_evar addrL);
                      assert_fails (has_evar addrR);
                      replace addrL with addrR by solve_word_eq OK;
                      (reflexivity || fail 10000 lhs "and" rhs "have the same address"
                      "according to addr, but can't be matched")
  end.

Ltac pick_nat n :=
  multimatch n with
  | S ?m => constr:(m)
  | S ?m => pick_nat m
  end.

Ltac wcancel_step OK := once (
  let RHS := lazymatch goal with |- Lift1Prop.iff1 _ (seps ?RHS) => RHS end in
  let jy := index_and_element_of RHS in (* <-- multi-success! *)
  let j := lazymatch jy with (?i, _) => i end in
  let y := lazymatch jy with (_, ?y) => y end in
  assert_fails (idtac; let y := rdelta_var y in is_evar y);
  let LHS := lazymatch goal with |- Lift1Prop.iff1 (seps ?LHS) _ => LHS end in
  let l := eval cbv [List.length] in (List.length LHS) in
  let i := pick_nat l in (* <-- multi-success! *)
  cancel_seps_at_indices i j; [sepclause_eq OK|]).

Ltac word_rep_to_word_ok R :=
  lazymatch constr:(@eq R (word.of_Z 0)) with
  | @eq _ (@word.of_Z _ ?Inst _) => constr:(_: word.ok Inst)
  end.

Ltac wcancel :=
  cancel;
  let OK := lazymatch goal with
            | |- @iff1 (@map.rep (@word.rep ?W ?WordInst) ?V ?M) _ _ =>
              constr:(_: word.ok WordInst)
            end in
  repeat wcancel_step OK;
  try solve [ecancel_done'].

(* mostly useful for debugging, once everything works, wcancel should do all the work *)
Ltac cancel_by_tag :=
  let RHS := lazymatch goal with |- Lift1Prop.iff1 _ (seps ?RHS) => RHS end in
  let jy := index_and_element_of RHS in
  let j := lazymatch jy with (?i, _) => i end in
  let y := lazymatch jy with (_, ?y) => y end in
  let tagR := tag y in
  assert_fails (idtac; let y := rdelta_var y in is_evar y);
  let LHS := lazymatch goal with |- Lift1Prop.iff1 (seps ?LHS) _ => LHS end in
  let l := eval cbv [List.length] in (List.length LHS) in
  let i := pick_nat l in
  let x := eval cbv [List.nth] in (List.nth i LHS (emp True)) in
  let tagL := tag x in
  constr_eq tagL tagR;
  cancel_seps_at_indices i j.

Ltac simpl_addrs :=
  simpl_Z_nat;
  unfold Register, MachineInt in *;
  (* note: it's the user's responsability to ensure that left-to-right rewriting with all
   nat and Z equations terminates, otherwise we'll loop infinitely here *)
  repeat match goal with
         | E: @eq ?T ?LHS _ |- _ =>
           lazymatch T with
           | Z => idtac
           | nat => idtac
           end;
           progress prewrite LHS E
         end.

Ltac wseplog_pre :=
  repeat (autounfold with unf_to_array);
  (* Note that "rewr" only works with equalities, not with iff1, so we use
     iff1ToEq to turn iff1 into eq (requires functional and propositionl extensionality).
     Alternatively, we could use standard rewrite (which might instantiate too many evars),
     or we could make a "seprewrite" which works on "seps [...] [...]" by replacing the
     i-th clause on any side with the rhs of the provided iff1, or we could make a
     seprewrite which first puts the clause to be replaced as the left-most, and then
     eapplies a "Proper_sep_iff1: Proper (iff1 ==> iff1 ==> iff1) sep", but that would
     change the order of the clauses. *)
  rewr (fun t => match t with
         | context [ array ?PT ?SZ ?start (?xs ++ ?ys) ] =>
           constr:(iff1ToEq (array_append' PT SZ xs ys start))
         | context [ array ?PT ?SZ ?start (?x :: ?xs) ] =>
           constr:(iff1ToEq (array_cons PT SZ x xs start))
         | context [ array ?PT ?SZ ?start nil ] =>
           constr:(iff1ToEq (array_nil PT SZ start))
         end) in |-*.

Ltac wwcancel :=
  wseplog_pre;
  simpl_addrs;
  wcancel.

Ltac wcancel_assumption := use_sep_assumption; wwcancel.

Hint Unfold program word_array: unf_to_array.

Section Footprint.
  Context {key value} {map : map.map key value} {ok : map.ok map}.

  (* if P allows different footprints, we return the intersection of all possible footprints *)
  Definition footprint_underapprox(P: map -> Prop): key -> Prop :=
    fun a => forall m, P m -> exists v, map.get m a = Some v.

  (* if P allows different footprints, we return the union of all possible footprints *)
  Definition footprint_overapprox(P: map -> Prop): key -> Prop :=
    fun a => exists m v, P m /\ map.get m a = Some v.

  Definition unique_footprint(P: map -> Prop): Prop :=
    forall m1 m2, P m1 -> P m2 -> map.same_domain m1 m2.

  Definition non_contrad(P: map -> Prop): Prop := exists m, P m.

  Lemma footprint_underapprox_subset_overapprox: forall (P: map -> Prop),
      non_contrad P ->
      subset (footprint_underapprox P) (footprint_overapprox P).
  Proof.
    unfold non_contrad, subset, footprint_underapprox, footprint_overapprox,
           elem_of.
    intros.
    destruct H as [m Pm].
    firstorder idtac.
  Qed.

  Lemma footprint_overapprox_subset_underapprox: forall (P: map -> Prop),
      unique_footprint P ->
      subset (footprint_overapprox P) (footprint_underapprox P).
  Proof.
    unfold unique_footprint, subset, footprint_underapprox, footprint_overapprox,
           elem_of, map.same_domain, map.sub_domain.
    intros.
    destruct H0 as [m' [v [Pm G]]].
    specialize (H _ _ H1 Pm).
    destruct H as [S1 S2].
    eapply S2. eassumption.
  Qed.

  Lemma footprint_over_equals_underapprox: forall (P: map -> Prop),
      unique_footprint P ->
      non_contrad P ->
      footprint_underapprox P = footprint_overapprox P.
  Proof.
    intros.
    apply iff1ToEq.
    split.
    - eapply footprint_underapprox_subset_overapprox. assumption.
    - eapply footprint_overapprox_subset_underapprox. assumption.
  Qed.

  (* Given that under normal circumstances, footprint_underapprox is the same as
     footprint_overapprox (see lemma above), we choose to use footprint_underapprox,
     because it requires no preconditions for footpr_sep_subset_l/r. *)

  Definition footpr := footprint_underapprox.

  Lemma in_footpr_sep_l: forall (x: key) (P Q: map -> Prop),
      elem_of x (footpr P) ->
      elem_of x (footpr (P * Q)%sep).
  Proof.
    unfold footpr, footprint_underapprox, sep, elem_of.
    intros.
    destruct H0 as [mp [mq [Sp [Pmp Qmq]]]].
    specialize (H mp Pmp).
    destruct H as [v G].
    unfold map.split, map.disjoint in Sp. destruct Sp as [? D]. subst.
    exists v.
    rewrite map.get_putmany_dec.
    destr (map.get mq x).
    - exfalso. eauto.
    - assumption.
  Qed.

  Lemma footpr_sep_subset_l: forall (P Q: map -> Prop) (A: key -> Prop),
      subset (footpr (sep P Q)) A -> subset (footpr P) A.
  Proof.
    unfold subset. eauto using in_footpr_sep_l.
  Qed.

  Lemma in_footpr_sep_r: forall (x: key) (P Q: map -> Prop),
      elem_of x (footpr Q) ->
      elem_of x (footpr (P * Q)%sep).
  Proof.
    unfold footpr, footprint_underapprox, sep, elem_of.
    intros.
    destruct H0 as [mp [mq [Sp [Pmp Qmq]]]].
    specialize (H mq Qmq).
    destruct H as [v G].
    unfold map.split, map.disjoint in Sp. destruct Sp as [? D]. subst.
    exists v.
    rewrite map.get_putmany_dec.
    destr (map.get mq x).
    - assumption.
    - discriminate.
  Qed.

  Lemma footpr_sep_subset_r: forall (P Q: map -> Prop) (A: key -> Prop),
      subset (footpr (sep P Q)) A -> subset (footpr Q) A.
  Proof.
    unfold subset. eauto using in_footpr_sep_r.
  Qed.

  Lemma rearrange_footpr_subset(P Q: map -> Prop) (A: key -> Prop)
      (H1: subset (footpr P) A)
      (H2: iff1 P Q):
      subset (footpr Q) A.
  Proof.
    intros. apply iff1ToEq in H2. subst P. assumption.
  Qed.

  Lemma shrink_footpr_subset(P Q R: map -> Prop) (A: key -> Prop)
      (H1: subset (footpr Q) A)
      (H2: iff1 Q (P * R)%sep):
      subset (footpr P) A.
  Proof.
    intros.
    apply iff1ToEq in H2. subst Q.
    eapply footpr_sep_subset_l. eassumption.
  Qed.

  Lemma same_domain_split: forall m1 m2 m1l m1r m2l m2r,
      map.same_domain m1l m2l ->
      map.same_domain m1r m2r ->
      map.split m1 m1l m1r ->
      map.split m2 m2l m2r ->
      map.same_domain m1 m2.
  Proof.
    unfold map.same_domain, map.sub_domain, map.split.
    intros. destruct H, H0, H1, H2. subst.
    split.
    - intros.
      rewrite map.get_putmany_dec in H1.
      destr (map.get m1r k).
      + inversion H1. subst v1.
        specialize (H0 _ _ E). destruct H0 as [v2 G].
        exists v2. apply map.get_putmany_right. assumption.
      + specialize (H _ _ H1). destruct H as [v2 G].
        exists v2. rewrite map.get_putmany_left. 1: assumption.
        destr (map.get m2r k); [exfalso | reflexivity].
        specialize (H4 _ _ E0). destruct H4 as [v2' G'].
        congruence.
    - intros.
      rewrite map.get_putmany_dec in H1.
      destr (map.get m2r k).
      + inversion H1. subst v1.
        specialize (H4 _ _ E). destruct H4 as [v2 G].
        exists v2. apply map.get_putmany_right. assumption.
      + specialize (H3 _ _ H1). destruct H3 as [v2 G].
        exists v2. rewrite map.get_putmany_left. 1: assumption.
        destr (map.get m1r k); [exfalso | reflexivity].
        specialize (H0 _ _ E0). destruct H0 as [v2' G'].
        congruence.
  Qed.

  Lemma unique_footprint_sep(P Q: map -> Prop):
    unique_footprint P ->
    unique_footprint Q ->
    unique_footprint (P * Q)%sep.
  Proof.
    unfold unique_footprint. intros.
    unfold sep in *.
    destruct H1 as [m1P [m1Q [? [? ?] ] ] ].
    destruct H2 as [m2P [m2Q [? [? ?] ] ] ].
    eapply same_domain_split; cycle 2; eauto.
  Qed.

End Footprint.
