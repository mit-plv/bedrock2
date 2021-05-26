Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Loops.
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
      let/d x2 := (x mod M) ^ 2 in
      let/d x3 := (x2 mod M) * (x mod M) in
      let/d x6 := (x3 mod M) ^ 2 in
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
      | xI xH => let/n res := x^2 mod M in x * res
      | xO n' => let/n res := exp_by_squaring x n' mod M in res^2
      | xI n' => let/n res := exp_by_squaring x n' mod M in
                 let/n res := res^2 mod M in
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

    Lemma exp_by_squaring_correct :
      M <> 0 -> forall n x, exp_by_squaring x n = x ^ (Zpos n).
    Proof.
      induction n; intros; cbn [exp_by_squaring]; unfold nlet.
      - rewrite IHn.
        rewrite mod_exp by assumption.
        rewrite Z.mul_mod_idemp_r by assumption.
        destruct n eqn : H'.
        + rewrite <- H'.
          rewrite Pos2Z.pos_xI.
          rewrite Z.pow_add_r; try easy.
          rewrite Z.pow_1_r.
          rewrite Z.pow_2_r.
          Z.push_pull_mod.
          rewrite Z.pow_twice_r.
          rewrite Z.mul_comm.
          reflexivity.
        + rewrite <- H'. change (Z.pos ?n~1) with (2 * Z.pos n + 1)%Z.
          rewrite Z.pow_add_r; try easy.
          rewrite Z.pow_1_r.
          rewrite Z.pow_2_r.
          Z.push_pull_mod.
          rewrite Z.pow_twice_r.
          rewrite Z.mul_comm.
          reflexivity.
        + Z.push_pull_mod.
          reflexivity.
      - rewrite IHn.
        rewrite mod_exp by assumption.
        destruct n eqn : H'; try reflexivity.
        + rewrite <- H'.
          rewrite Pos2Z.pos_xO.
          rewrite Z.pow_2_r.
          change (Z.pos ?n~0) with (2 * Z.pos n)%Z.
          rewrite Z.pow_twice_r.
          Z.push_pull_mod.
          reflexivity.
        + rewrite <- H'. change (Z.pos ?n~0) with (2 * Z.pos n)%Z.
          rewrite Z.pow_mul_r; try easy.
          rewrite Z.pow_twice_r.
          rewrite Z.pow_1_r.
          rewrite Z.pow_2_r.
          Z.push_pull_mod.
          reflexivity.
      - rewrite Z.pow_1_r.
        reflexivity.
    Qed.
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

(*
    Lemma exp_6_correct : program_logic_goal_for_function! exp_6.
    Proof.
      repeat straightline.
      intros; exists [x_ptr; sq_ptr]; split.
      - subst l. tac.
      - subst l. tac.
    Admitted.*)

    Definition exp_result x_ptr q_ptr xq_val : list word -> Semantics.mem -> Prop :=
      fun _ => Lift1Prop.ex1 (fun x => Lift1Prop.ex1 (fun q =>
                                                        (emp(eval x = fst xq_val) *
                                                         (emp(eval q mod M = snd xq_val) *
                                                          (Bignum x_ptr x * Bignum q_ptr q)))%sep)).

    Definition exp_by_squaring_6' (x : Z) : (Z * Z) :=
      let/n out := (x mod M) ^ 2 mod M in
      let/n out := out * (x mod M) mod M in
      let/n out := out  ^ 2 mod M in
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
      (* Z.push_pull_mod; pull_mod; *)
      match goal with
      | [ H: _ mod _ = ?v |- _ ] => is_var v; rewrite <- H
      | _ => idtac
      end.

    Ltac compile_custom ::=
      progress ( field_cleanup;
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
      compile_setup.
      repeat compile_step.
      lift_eexists; sepsimpl. eauto || ecancel_assumption.
      eapply Heq1.
      ecancel_assumption.
    Qed.

    Definition exp_by_squaring_9' (x : Z) : (Z * Z) :=
      let/n out := (x mod M) ^ 2 mod M in
      let/n out := out ^ 2 mod M in
      let/n out := out ^ 2 mod M in
      let/n out := x mod M * out mod M in
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

    Compute exp9_body.

(*
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
    Qed.*)

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
      | 0%nat => x
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
        let/n res := exp_from_encoding x t mod M in
        let/n res := res^2 mod M in
        let/n res := x * res mod M in
        res
      | (true, k) :: t =>
        let/n res := exp_from_encoding x t mod M in
        let/n res := loop res (S k) (exp_square_and_multiply x) in
        res
      | (false, 0%nat) :: t =>
        let/n res := exp_from_encoding x t mod M in
        let/n res := res^2 mod M in
        res
      | (false, k) :: t =>
        let/n res := exp_from_encoding x t mod M in
        let/n res := loop res (S k) (exp_square) in
        res
      end.

    Definition exp_by_squaring_encoded (x : Z) (n : positive) : Z :=
      exp_from_encoding x (run_length_encoding n).

    Compute run_length_encoding 4.

    Lemma run_length_encoding_nonempty:
      forall n, run_length_encoding n <> [].
    Proof.
      destruct n eqn : H'; simpl.
      + destruct (run_length_encoding p).
        { inversion 1. }
        destruct p0; destruct b; inversion 1.
      + destruct (run_length_encoding p).
        { inversion 1. }
        destruct p0; destruct b; inversion 1.
      + inversion 1.
    Qed.

    Lemma exp_by_squaring_encoded_correct : 
      M <> 0 -> forall n x, exp_by_squaring_encoded x n = x ^ (Zpos n) mod M.
    Proof.
      intros. rewrite <- exp_by_squaring_correct; eauto.
      unfold exp_by_squaring_encoded; induction n; simpl.
      - cbn -[loop].
        destruct (run_length_encoding n) eqn : Heq.
        + apply run_length_encoding_nonempty in Heq.
          inversion Heq.
        + destruct p. destruct b.
          { rewrite <- IHn.
          cbn. replace (n0 + 1)%nat with (S n0) by lia.
          unfold nlet; destruct n0.
            { cbn.
              destruct n eqn : H'.
              { repeat eapply mod_equal.
                unfold exp_square_and_multiply.
                rewrite <- Z.mul_comm.
                f_equal.
                rewrite ! Z.pow_2_r.
                Z.push_pull_mod.
                f_equal.
                ring.
              }
              { repeat eapply mod_equal.
                unfold exp_square_and_multiply.
                rewrite <- Z.mul_comm.
                f_equal.
                rewrite ! Z.pow_2_r.
                Z.push_pull_mod.
                f_equal.
                ring.
              }
              {
              unfold run_length_encoding in Heq.
              inversion Heq.
              repeat eapply mod_equal.
              unfold exp_square_and_multiply.
              unfold exp_from_encoding.
              rewrite <- Z.mul_comm.
              f_equal.
              rewrite ! Z.pow_2_r.
              Z.push_pull_mod.
              f_equal.
              ring.
              }
            }
            cbn.
            destruct n eqn : H'.
            { repeat eapply mod_equal.
              Z.push_pull_mod.
                unfold exp_square_and_multiply.
                rewrite <- Z.mul_comm.
                f_equal.
            }
            { repeat eapply mod_equal.
              Z.push_pull_mod.
                unfold exp_square_and_multiply.
                rewrite <- Z.mul_comm.
                f_equal.
            }
            
              {
              unfold run_length_encoding in Heq.
              inversion Heq.
              }
          }
          rewrite <- IHn.
          cbn.
          unfold nlet.
          destruct n0; destruct n eqn : H'; try reflexivity.
          { unfold run_length_encoding in Heq.
            Z.push_pull_mod.
            inversion Heq.
          }
          unfold run_length_encoding in Heq.
          inversion Heq.
      - rewrite <- IHn.
        cbn. 
        destruct n eqn : H'.
        { destruct (run_length_encoding p~1) as [|[[|] n0] t]; try reflexivity.
          simpl.
          replace (n0 + 1)%nat with (S n0) by lia.
          unfold nlet.
          cbn.
          unfold exp_square.
          destruct n0.
          { unfold loop.
            set (exp_from_encoding x t mod M) as ext.
            rewrite <- Z.pow_mod.
            Z.push_pull_mod.
            f_equal.
          }
          set (exp_from_encoding x t mod M) as ext.
          rewrite Z.mul_1_r.
          set (loop ext (S n0) (fun x' : Z => x' ^ 2 mod M) mod M) as lext.
          f_equal.
          Z.push_pull_mod.
          ring.
        }
        { destruct (run_length_encoding p~0) as [|[[|] n0] t]; try reflexivity.
          simpl.
          replace (n0 + 1)% nat with (S n0) by lia.
          unfold nlet.
          cbn.
          unfold exp_square.
          destruct n0.
          { unfold loop.
            set (exp_from_encoding x t mod M) as ext.
            rewrite Z.mul_1_r.
            rewrite <- Z.pow_mod.
            Z.push_pull_mod.
            f_equal.
            ring.
          }
          set (exp_from_encoding x t mod M) as ext.
          rewrite Z.mul_1_r.
          set (loop ext (S n0) (fun x' : Z => x' ^ 2 mod M)) as lext.
          Z.push_pull_mod.
          rewrite <- Z.pow_mod.
          f_equal.
          ring.
        }
        inversion IHn.
        unfold nlet in H1.
        unfold run_length_encoding.
        unfold exp_from_encoding.
        unfold nlet.
        rewrite Z.pow_2_r.
        rewrite <- Z.pow_mod.
        Z.push_pull_mod.
        f_equal.
        ring.
      - unfold nlet.
        cbn.
        Z.push_pull_mod.
        rewrite Z.mul_1_r.
        reflexivity.
    Qed.

    Definition exp_by_squaring_encoded_6' (x : Z) : (Z * Z) :=
      let/n out := x ^ 2 mod M in
      let/n out := loop out 7 (fun out => let/n out := exp_square out in out) in
      (x, out).

    Lemma loop_equals':
      forall {A} f (x : A) k,
        (ExitToken.new, loop x k f) =
      (ranged_for' 0 (Z.of_nat k)
       (fun (tok : ExitToken.t) (idx : Z) (acc : A) _ =>
          (tok, f acc)) x).
    Proof.
      induction k.
      - simpl.
        unfold ranged_for'.
        rewrite ranged_for_break_exit; try reflexivity.
        lia.
      - cbn -[Z.of_nat].
        replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia.
        erewrite ranged_for'_unfold_r_nstop; try lia; try easy.
        all: rewrite <- IHk; reflexivity.
    Qed.
    
        
    Lemma loop_equals :
      forall {A} f (x : A) k,
        Z.of_nat k < 2 ^ Semantics.width ->
        loop x k f =
        let/n from := 0 in
        let/n to := word.of_Z (Z.of_nat k) in
        ranged_for_u (word.of_Z from) to
                     (fun t _ acc _ =>
                        let/n out := f acc in (t, out)) x.
    Proof.
      intros.
      unfold nlet.
      unfold ranged_for_u in *.
      unfold ranged_for_w in *.
      unfold ranged_for in *.
      unfold w_body.
      pose proof Nat2Z.is_nonneg k.
      pose proof Nat2Z.is_nonneg (S k).
      repeat rewrite word.unsigned_of_Z_0.
      repeat rewrite word.unsigned_of_Z.
      repeat rewrite word.wrap_small by lia.
      rewrite <- loop_equals'.
      reflexivity.
    Qed.

    Lemma Znum_to_Bignum :
      forall R mem x_ptr x, (Znum x_ptr x * R)%sep mem ->
                            exists b : bignum, (x = eval b mod M) /\
                                               (Bignum x_ptr b * R)%sep mem.
      intros.
      unfold Znum in *.
      destruct H as (? & ? & ? & ? & ?).
      destruct H0 as (? & ? & ?).
      exists x2.
      split.
      - apply H0.
      - unfold sep. exists x0. exists x1. split.
        + apply H.
        + split.
          apply H2.
          apply H1.
      Qed.


  
   Definition exp_result' x_ptr q_ptr xq_val : list word -> Semantics.mem -> Prop :=
     fun _ => (Znum x_ptr (fst xq_val) * Znum q_ptr (snd xq_val))%sep.

   Hint Unfold exp_result' : compiler_cleanup.
   Hint Unfold exp_square : compiler_cleanup.

   Hint Extern 1 => simple eapply compile_Z_square; shelve : compiler.

       (*
   Ltac compile_copy :=
      match goal with
      | [ H: (Znum ?ptr ?v * ?R)%sep ?m |- ?l ] =>
        match l with
        | context [map.put _ ?x ptr] =>
          match l with
            | context [let/n _ as x eq:_ := v in _] =>
            apply compile_copy_pointer with (var := x) (x_ptr0 := ptr) (Data := Znum) (R0 := R)
          end
        end
      end.*)

   Ltac compile_try_copy_pointer :=
     lazymatch goal with
     | [ H : ?pred ?m |- WeakestPrecondition.cmd _ _ _ ?m ?l (_ ?term) ] =>
       match term with
       | nlet_eq [?var_] ?v _ =>
         match l with
         | context [map.put _ var_ ?ptr] =>
           match pred with
           | context [?Data_ ptr v] =>
             simple eapply compile_copy_pointer with (var := var_) (x_ptr0 := ptr) (Data := Data_)
           end
         end
       end
     end.

   Ltac compile_custom ::=
     progress ( field_cleanup;
                try rewrite loop_equals;
                try (try simple eapply compile_dlet_as_nlet_eq;
                     try simple eapply compile_nlet_as_nlet_eq;
                     first [ simple eapply compile_square
                           | simple eapply compile_mul
                           | compile_try_copy_pointer]));
     intros.

   Lemma clean_width :
     forall x, x < 2 ^ 32 -> x < 2 ^ Semantics.width.
   Proof.
     intros; destruct Semantics.width_cases as [ -> | -> ]; lia.
   Qed.

   Hint Extern 1 => simple eapply clean_width; reflexivity : compiler_cleanup.
     
    Derive exp_body' SuchThat
           (let exp6_encoded := ("exp6", (["x"; "out"], [], exp_body')) in
            program_logic_goal_for exp6_encoded
                                   (forall functions,
                                       spec_of_Z_UnOp un_square functions ->
                                       spec_of_Z_BinOp bin_mul functions ->
                                       forall x_ptr x sq_ptr sq_init tr R mem,
                                         (*bounded_by tight_bounds x ->*)
                                         (*bounded_by tight_bounds sq_init ->*)
                                         ((Znum x_ptr x * Znum sq_ptr sq_init * R)%sep mem) ->
                                         WeakestPrecondition.call
                                           (exp6_encoded :: functions)
                                           "exp6"
                                           tr mem [x_ptr; sq_ptr]
                                           (postcondition_func_norets
                                              (exp_result' x_ptr sq_ptr (exp_by_squaring_encoded_6' x))
                                              R tr)))
           As exp_body_correct'.
    compile.
    simple apply compile_nlet_as_nlet_eq.
    
    eapply compile_ranged_for_u with (loop_pred := (fun idx z tr' mem' locals' =>
         tr' = tr /\
         locals' = map.put
                 (map.put (map.put (map.put map.empty "x" x_ptr) "out" sq_ptr) "from"
                    idx) "to" v1 /\
         (Znum sq_ptr z ⋆ (Znum x_ptr x ⋆ R)) mem')); repeat compile_step.
            
    Qed.
        
  End Bedrock.

End S.
