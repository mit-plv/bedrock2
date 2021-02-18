Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.ECC.Field.
Local Open Scope Z_scope.

Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.NotationsInConstr.

Section S.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {field_parameters : FieldParameters}.
  Context {bignum_representaton : BignumRepresentation}.

  Context {relax_bounds :
             forall X : bignum,
               bounded_by tight_bounds X ->
               bounded_by loose_bounds X}.
  Hint Resolve relax_bounds : compiler_cleanup.

  Section Gallina.
    Local Notation "0" := (0 mod M).
    Local Notation "1" := (1 mod M).
    Local Infix "+" := (fun x y => (x + y) mod M).
    Local Infix "-" := (fun x y => (x - y) mod M).
    Local Infix "*" := (fun x y => (x * y) mod M).
    Local Infix "^" := (fun x y => (x ^ y) mod M).

    Definition exp_by_squaring_6 (x : Z) : Z :=
      let/d x2 := x ^ 2 in
      let/d x3 := x2 * x in
      let/d x6 := x3 ^ 2 in
      x6.

    Lemma mod_equal :
      forall a b m, a = b -> a mod m = b mod m.
    Proof.
      intros. rewrite H. lia.
    Qed.

    Lemma mod_exp :
      forall m, m <> 0 -> forall b a, ((a mod m) ^ Zpos b) mod m = (a ^ Zpos b) mod m.
    Proof.
      induction b; intros.
      - rewrite Pos2Z.pos_xI.
        rewrite Z.pow_add_r by lia.
        rewrite Z.pow_1_r.
        rewrite Z.pow_twice_r.
        rewrite <- Z.mul_mod_idemp_l by assumption.
        remember (((a mod m) ^ Z.pos b * (a mod m) ^ Z.pos b) mod m) as A.
        rewrite Z.mul_mod_idemp_r by assumption.
        rewrite Z.mul_mod in HeqA by assumption.
        rewrite IHb in HeqA.
        rewrite <- Z.mul_mod in HeqA by assumption.
        rewrite HeqA.
        rewrite Z.mul_mod_idemp_l by assumption.
        apply mod_equal.
        rewrite Z.pow_add_r by lia.
        rewrite Z.pow_twice_r.
        lia.
      - rewrite Pos2Z.pos_xO.
        rewrite Z.pow_twice_r.
        rewrite Z.mul_mod by assumption.
        rewrite IHb.
        rewrite <- Z.mul_mod by assumption.
        apply mod_equal.
        rewrite Z.pow_twice_r.
        reflexivity.
      - repeat rewrite Z.pow_1_r.
        rewrite Z.mod_mod by assumption.
        reflexivity.
    Qed.

    Fixpoint exp_by_squaring (x : Z) (n : positive) : Z :=
      match n with
      | xH => x mod M
      | xO xH => x^2 mod M
      | xI xH => let/n res := x^2 in x * res
      | xO n' => let/n res := exp_by_squaring x n' in res^2
      | xI n' => let/n res := exp_by_squaring x n' in
                 let/n res := res^2 in
                 x * res
      end.

    Print exp_by_squaring.

    Lemma letn_equal :
      forall A B (val : A) (body_l body_r : A -> B) (var : string),
        (let x := val in body_l x = body_r x)
        -> (let/n x as var := val in body_l x) = (let/n y as var := val in body_r y).
    Proof.
      intros. assumption.
    Qed.

    Lemma letn_nested :
      forall A B C (a : C) (val1 : A) (body1 : A -> B) (body2 : B -> C) (var var' : string),
        a = (let/n x as var' := val1 in let/n y as var := body1 x in body2 y)
        -> a = (let/n y as var := let/n x as var' := val1 in body1 x in body2 y).
    Proof.
      intros. assumption.
    Qed.

    Lemma letn_paren_equal :
      forall A B (a : A) (val : A) (body_r : A -> B) (var : string) left,
        left = (let/n y as var := val in (a, body_r y))
        -> left = (a, let/n y as var := val in body_r y).
    Proof.
      intros.
      rewrite H. reflexivity.
    Qed.

    Ltac tac :=
      lazymatch goal with
      | [ |- let _ := _ in _ = _ ] =>
        intros
      | [ |- _ = let/n _ as _ := (let/n _ as _ := _ in _) in _] =>
        eapply letn_nested
      | [ |- _ = let/n _ as _ := _ in _] =>
        eapply letn_equal with (body_l := fun _ => _)
      | [ |- _ = (_, let/n _ as _ := _ in _)] =>
        eapply letn_paren_equal
      end.

    Derive rewritten SuchThat
           (forall x, rewritten x = (x, let/n res := exp_by_squaring x 11 in res))
           As rewrite.
    Proof.
      cbv beta iota delta [exp_by_squaring].
      subst rewritten.
      intros.
      repeat tac.
      reflexivity.
    Qed.
    Print rewritten.

    (*
    Lemma exp_by_squaring_correct :
      M <> 0 -> forall n x, exp_by_squaring x n = x ^ (Zpos n).
    Proof.
      induction n; intros; cbn [exp_by_squaring]; unfold nlet.
      - rewrite IHn.
        rewrite mod_exp by assumption.
        rewrite Z.mul_mod_idemp_r by assumption.
        apply mod_equal.
        rewrite Pos2Z.pos_xI.
        rewrite Z.pow_add_r by lia.
        rewrite <- Z.pow_mul_r by lia.
        rewrite Z.mul_comm with (n := 2).
        lia.
      - rewrite IHn.
        rewrite mod_exp by assumption.
        apply mod_equal.
        symmetry. rewrite Pos2Z.pos_xO.
        rewrite <- Z.pow_mul_r by lia.
        rewrite Z.mul_comm with (n := 2).
        lia.
      - rewrite Z.pow_1_r.
        reflexivity.
    Qed.
    *)
  End Gallina.

  Section Bedrock.
    Definition exp_6 : bedrock_func :=
      ("exp_by_squaring_6",
       (["x"; "sq"], [],
        bedrock_func_body:
          (
            cmd.call [] bignum_copy [expr.var "x"; expr.var "sq"];;
            cmd.call [] square [expr.var "sq"; expr.var "sq"];;
            cmd.call [] mul [expr.var "x"; expr.var "sq"; expr.var "sq"];;
            cmd.call [] square [expr.var "sq"; expr.var "sq"]
          )
       )
      ).

    Instance spec_of_exp_6 : spec_of exp_6 :=
      fun functions =>
        forall x_ptr x x_val sq_ptr sq ret tr R mem,
          bounded_by tight_bounds sq ->
          bounded_by tight_bounds x ->
          bounded_by tight_bounds ret ->
          exp_by_squaring_6 x_val = eval ret ->
          ((Bignum x_ptr x * Bignum sq_ptr sq * R)%sep mem) ->
          x_val = eval x ->
          WeakestPrecondition.call
            functions exp_6 tr mem [x_ptr; sq_ptr]
            (fun tr' mem' rets =>
               tr = tr' /\ rets = nil
               /\ (Bignum x_ptr x * Bignum sq_ptr ret * R)%sep mem').

    Ltac tac :=
      repeat match goal with
             | [ |- WeakestPrecondition.dexprs _ _ _ _ ] => eexists
             | [ |- WeakestPrecondition.list_map _ _ _ ] => eexists
             | [ |- _ /\ _] => split
             | _ => reflexivity
             | [ |- context[map.get (map.put _ ?k _) ?k] ] => rewrite map.get_put_same
             | [ |- context[map.get (map.put _ ?k _) ?k2] ] => rewrite map.get_put_diff by discriminate
             | [ |- WeakestPrecondition.call _ _ _ _ _ _ ] => handle_call
             | [ |- bounded_by loose_bounds ?x ] => eapply relax_bounds
             | [ H : bounded_by tight_bounds ?x |- bounded_by tight_bounds ?x] => apply H
             | [ |- exists _, _ ] => eexists
             | [ H : context[emp (?k = [])] |- context[map.putmany_of_list_zip [] ?k] ] => destruct H
             | [ H : ?k = [] |- context[map.putmany_of_list_zip [] ?k] ] => rewrite H
             | [ |- WeakestPrecondition.cmd _ _ _ _ _ _ ] => straightline
             | [ |- WeakestPrecondition.call _ _ _ _ _ ] => handle_call
             | [ |- WeakestPrecondition.call _ _ _ _ _ ] => straightline_call
             | [ H : context[postcondition_func_norets] |- _ ] => destruct H
             end.


    Lemma exp_6_correct : program_logic_goal_for_function! exp_6.
    Proof.
      repeat straightline.
      intros; exists [x_ptr; sq_ptr]; split.
      - subst l. tac.
      - subst l. tac.
    Admitted.

    Definition exp_result x_ptr q_ptr xq_val : list word -> Semantics.mem -> Prop :=
      fun _ => Lift1Prop.ex1 (fun x => Lift1Prop.ex1 (fun q =>
                                                        (emp(eval x = fst xq_val) *
                                                         (emp(eval q mod M = snd xq_val) *
                                                          (Bignum x_ptr x * Bignum q_ptr q)))%sep)).

    Definition exp_by_squaring_6' (x : Z) : (Z * Z) :=
      let/n out := x ^ 2 mod M in
      let/n out := out * x mod M in
      let/n out := out ^ 2 mod M in
      (x, out).

    Lemma Lift1Prop_impl1_ex :
      forall {A B : Type} (q : A -> B -> Prop) (p : A -> Prop),
        (exists v, (Lift1Prop.impl1 p (fun m => q m v))) ->
        Lift1Prop.impl1 p (fun m => exists v, q m v).
      intros.
      unfold Lift1Prop.impl1.
      unfold Lift1Prop.impl1 in H.
      intros.
      destruct H.
      exists x0.
      apply H.
      apply H0.
    Qed.

    Lemma Lift1Prop_impl1_and :
      forall {A : Type} (q1 : Prop) (q2 p : A -> Prop),
        (q1 /\ (Lift1Prop.impl1 p (fun m => q2 m))) ->
        Lift1Prop.impl1 p (fun m => q1 /\ q2 m).
      intros.
      unfold Lift1Prop.impl1.
      unfold Lift1Prop.impl1 in H.
      intros.
      destruct H.
      split.
      - apply H.
      - apply H1.
        apply H0.
    Qed.

    Ltac field_cleanup :=
      Z.push_pull_mod; pull_mod;
      match goal with
      | [ H: _ mod _ = ?v |- _ ] => is_var v; rewrite <- H
      | _ => idtac
      end.

    Ltac compile_custom ::=
      progress (field_cleanup;
                try (try simple eapply compile_dlet_as_nlet_eq;
                     try simple eapply compile_nlet_as_nlet_eq;
                     first [ simple eapply compile_square
                           | simple eapply compile_mul]));
      (intros; unfold Placeholder in *).  (* FIXME get rid of placeholders? *)

    Hint Unfold exp_result : compiler_cleanup.

    Derive exp_body SuchThat
           (let exp6 := ("exp6", (["x"; "out"], [], exp_body)) in
            program_logic_goal_for exp6
                                   (forall functions,
                                       spec_of_UnOp un_square functions ->
                                       spec_of_BinOp bin_mul functions ->
                                       forall x_ptr x sq_ptr sq_init tr R mem,
                                         bounded_by tight_bounds x ->
                                         bounded_by tight_bounds sq_init ->
                                         ((Bignum x_ptr x * Bignum sq_ptr sq_init * R)%sep mem) ->
                                         WeakestPrecondition.call
                                           (exp6 :: functions)
                                           "exp6"
                                           tr mem [x_ptr; sq_ptr]
                                           (postcondition_func_norets
                                              (exp_result x_ptr sq_ptr (exp_by_squaring_6' (eval x)))
                                              R tr)))
           As exp_body_correct.
    Proof.
      compile.
      lift_eexists; sepsimpl; eauto || ecancel_assumption.
    Qed.

    Definition exp_by_squaring_9' (x : Z) : (Z * Z) :=
      let/n out := x ^ 2 mod M in
      let/n out := out ^ 2 mod M in
      let/n out := out ^ 2 mod M in
      let/n out := x * out mod M in
      (x, out).

    Derive exp9_body SuchThat
           (let exp9 := ("exp9", (["x"; "out"], [], exp9_body)) in
            program_logic_goal_for exp9
                                   (forall functions,
                                       spec_of_UnOp un_square functions ->
                                       spec_of_BinOp bin_mul functions ->
                                       forall x_ptr x sq_ptr sq_init tr R mem,
                                         bounded_by tight_bounds x ->
                                         bounded_by tight_bounds sq_init ->
                                         ((Bignum x_ptr x * Placeholder sq_ptr sq_init * R)%sep mem) ->
                                         WeakestPrecondition.call
                                           (exp9 :: functions)
                                           "exp9"
                                           tr mem [x_ptr; sq_ptr]
                                           (postcondition_func_norets
                                              (exp_result x_ptr sq_ptr (exp_by_squaring_9' (eval x)))
                                              R tr)))
           As exp9_body_correct.
    Proof.
      compile.
      lift_eexists; sepsimpl; eauto || ecancel_assumption.
    Qed.

    (* Lemma Zmult_mod_idemp_r_inplace : *)
    (*   forall a b n : Z, *)
    (*     (b * inplace (a mod n)) mod n = (b * inplace(a)) mod n. *)
    (*   unfold inplace. *)
    (*   apply Zmult_mod_idemp_r. *)
    (* Qed. *)

    Derive exp_11_body SuchThat
           (let exp11 := ("exp11", (["x"; "res"], [], exp_11_body)) in
            program_logic_goal_for exp11
                                   (forall functions,
                                       spec_of_UnOp un_square functions ->
                                       spec_of_BinOp bin_mul functions ->
                                       forall x_ptr x sq_ptr sq_init tr R mem,
                                         bounded_by tight_bounds x ->
                                         bounded_by tight_bounds sq_init ->
                                         ((Bignum x_ptr x * Placeholder sq_ptr sq_init * R)%sep mem) ->
                                         WeakestPrecondition.call
                                           (exp11 :: functions)
                                           "exp11"
                                           tr mem [x_ptr; sq_ptr]
                                           (postcondition_func_norets
                                              (exp_result x_ptr sq_ptr (rewritten (eval x)))

                                              R tr)))
           As exp_11_body_correct.
    Proof.
      compile.
      lift_eexists; sepsimpl; eauto || ecancel_assumption.
    Qed.

    Fixpoint run_length_encoding (n : positive) : list (bool * nat) :=
      match n with
      | xH => [(true, 0)]
      | xO n' =>
        match (run_length_encoding n') with
        | (false, k) :: t => (false, k + 1) :: t
        | t => (false, 0) :: t
        end
      | xI n' =>
        match (run_length_encoding n') with
        | (true, k) :: t => (true, k + 1) :: t
        | t => (true, 0) :: t
        end
      end%nat.

    Compute run_length_encoding 1.

    Fixpoint loop {A} (x : A) (k : nat) (f : A -> A) : A :=
      match k with
      | 0%nat => f x
      | S k' => f (loop x k' f)
      end.

    Definition exp_square_and_multiply (x : Z) (x' : Z) :=
      (Z.pow x' 2 mod M) * x mod M.

    Definition exp_square (x' : Z) :=
      (Z.pow x' 2 mod M).

    Fixpoint exp_from_encoding (x : Z) (n : list (bool * nat)) : Z :=
      match n with
      | [] =>
        1
      (* can add more cases for small k to be faster *)
      | (true, 0%nat) :: t =>
        let/n res := exp_from_encoding x t in
        let/n res := res^2 mod M in
        let/n res := x * res mod M in
        res
      | (true, k) :: t =>
        let/n res := exp_from_encoding x t in
        let/n res := loop res k (exp_square_and_multiply x) in
        res
      | (false, 0%nat) :: t =>
        let/n res := exp_from_encoding x t in
        let/n res := res^2 mod M in
        res
      | (false, k) :: t =>
        let/n res := exp_from_encoding x t in
        let/n res := loop res k (exp_square) in
        res
      end.

    Definition exp_by_squaring_encoded (x : Z) (n : positive) : Z :=
      exp_from_encoding x (run_length_encoding n).

    Compute run_length_encoding 4.

    (*
    Lemma exp_by_squaring_encoded_correct :
      M <> 0 -> forall n x, exp_by_squaring_encoded x n = x ^ (Zpos n) mod M.
    Proof.
      intros. rewrite <- exp_by_squaring_correct; eauto.
      unfold exp_by_squaring_encoded; induction n; simpl.
      - cbn -[loop].
        destruct (run_length_encoding n).
        + rewrite <- IHn. eauto.
        + destruct p. destruct b.
          { rewrite <- IHn.
          cbn. replace (n0 + 1)%nat with (S n0).
          { unfold nlet; destruct n0.
            { cbn.
              repeat eapply mod_equal.
              rewrite <- Z.mul_comm.
              f_equal.
              eapply mod_equal.
              set ((exp_from_encoding x l)) as exl.
              ring_simplify.
              rewrite <- Z.mul_comm. reflexivity.
            }
            eapply mod_equal.
            eapply Z.mul_comm.
          }
          { symmetry. eapply Nat.add_1_r. }
          }
        rewrite <- IHn. cbn. unfold nlet. eauto.
      - rewrite <- IHn.
        cbn.
        destruct (run_length_encoding n) as [|[[|] n0] t]; eauto.
        rewrite Nat.add_comm.
        destruct n0; eauto.
      - unfold nlet; cbn.
        rewrite Zmult_mod_idemp_r.
        eapply mod_equal.
        apply Z.mul_1_r.
    Qed.
    *)
  End Bedrock.

End S.
