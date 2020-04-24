Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Array.
Require Import bedrock2.BasicCSyntax.
Require Import bedrock2.BasicC64Semantics.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Scalars.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Map.SortedList.
Require Import coqutil.Tactics.destr.
Require Import Coq.Numbers.DecimalString.

Local Open Scope string_scope.
Import ListNotations.

Module GallinaIncr.
  Local Existing Instance bedrock2.BasicCSyntax.StringNames_params.
  Local Existing Instance BasicC64Semantics.parameters.
  Local Existing Instance BasicC64Semantics.parameters_ok.

  Notation word := Semantics.word.

  Record cell := { data : Semantics.word }.

  Notation address := word.

  Definition cell_value (addr: address) (c: cell) : Semantics.mem -> Prop :=
    scalar addr c.(data).

  Definition get c := c.(data).
  Definition put v (c: cell) := {| data := v |}.

  Import dlet.

  Notation "'let/d'  x  :=  val  'in'  body" :=
    (dlet val (fun x => body)) (at level 4).

  Definition incr_gallina_spec (c: cell) :=
    let/d v := get c in
    let/d v := word.add v (word.of_Z 1) in
    let/d c := put v c in
    c.

  Definition swap_gallina_spec (c1 c2: cell) :=
    let/d v1 := get c1 in
    let/d v2 := get c2 in
    let/d c1 := put v2 c1 in
    let/d c2 := put v1 c2 in
    (c1, c2).


  Local Infix "~>" := scalar (at level 40, only parsing).

  Require Import derive.Derive.

  Inductive Counter (n : nat) : Type :=
  | ofNat : Counter n
  .

  Definition mklit z := expr.literal z.
      Ltac compile_step b2_body mem locals spec := fail.

      Ltac gen_sym_inc :=
        lazymatch goal with
        | H : Counter ?n |- _ =>
          pose proof (ofNat (S n)); clear H
        | _ => pose proof (ofNat 0)
        end.

      Ltac gen_sym_fetch prefix :=
        lazymatch goal with
        | H : Counter ?n |- _ =>
          let x := constr:((prefix ++ DecimalString.NilEmpty.string_of_uint (Nat.to_uint n))%string) in
          let x := eval cbv in x in
          constr:(x)
        end.

      Ltac match_compile_goal :=
        lazymatch goal with
        | [  |- WeakestPrecondition.cmd _ ?b2_body _ ?mem
                                       {| value := ?locals |}
                                       (fun (t : Semantics.trace) (m _ : rep) =>
                                          _ /\
                                          _ /\
                                          sep (_ ?spec) _ m) ] =>
          compile_step b2_body mem locals spec
        end.

      Ltac lookup_object_in predicates predicate value :=
        lazymatch predicates with
        | predicate ?ptr value =>
          constr:(Some ptr)
        | sep ?l ?r =>
          lazymatch lookup_object_in l predicate value with
          | Some ?ptr => constr:(Some ptr)
          | None => lookup_object_in r predicate value
          end
        | _ => constr:(@None address)
        end.

      Ltac lookup_object predicate value mem :=
        lazymatch goal with
        | [ H: ?predicates mem |- _ ] =>
          let ptr := lookup_object_in predicates predicate value in
          lazymatch ptr with
          | Some ?ptr => ptr
          | None => fail "failed to look up object" value
          end
        | _ => fail "failed to find preconditions for " mem
        end.

      Ltac lookup_variable locals ptr :=
        lazymatch locals with
        | [] => fail
        | (?k, ptr) :: _ => k
        | (_, _) :: ?tl => lookup_variable tl ptr
        end.

      Ltac expr_of_constant g :=
        lazymatch g with
        | word.of_Z ?z =>
          constr:(expr.literal z)
        end.

      Ltac expr_of_gallina locals g :=
        match g with            (* FIXME test with is_var *)
        | _ => let v := lookup_variable locals g in
              constr:(expr.var v)
        | _ => expr_of_constant g
        | ?other => fail "failed to translate to expr " other
        end.

      Ltac compile_step b2_body mem locals spec ::=
        lazymatch spec with
        | (dlet ?value ?continuation) =>
          lazymatch value with
          | get ?c =>
            let ptr := lookup_object cell_value c mem in
            let var := expr_of_gallina locals ptr in
            let b2_continuation := fresh "body" in
            gen_sym_inc;
            let name := gen_sym_fetch "v" in
            evar (b2_continuation: cmd);
            unify b2_body
                  (cmd.seq (cmd.set name (expr.load access_size.word
                                                   var))
                           b2_continuation);
            subst b2_continuation
          | word.add ?l ?r =>
            let ll := expr_of_gallina locals l in
            let rr := expr_of_gallina locals r in
            gen_sym_inc;
            let name := gen_sym_fetch "v" in
            let b2_continuation := fresh "body" in
            evar (b2_continuation: cmd);
            unify b2_body (* FIXME coq renamed v into v0 *)
                  (cmd.seq (cmd.set name (expr.op
                                            bopname.add
                                            ll rr))
                           b2_continuation);
            subst b2_continuation
          | put ?x ?c =>
            let ptr := lookup_object cell_value c mem in
            let var := expr_of_gallina locals ptr in
            let x := expr_of_gallina locals x in
            let b2_continuation := fresh "body" in
            evar (b2_continuation: cmd);
            unify b2_body
                  (cmd.seq (cmd.store access_size.word var x)
                           b2_continuation);
            subst b2_continuation
          | ?other => fail "Not sure what to do with" other
          end
        | _ => unify b2_body (cmd.skip)
        end.


  Derive body SuchThat
         (let swap := ("swap", (["c"], [], body)) in
          program_logic_goal_for swap
          (forall functions,
           forall c_ptr c tr R mem,
             seps [cell_value c_ptr c; R] mem ->
             WeakestPrecondition.call
               (swap :: functions)
               "swap"
               tr mem [c_ptr]
               (fun tr' mem' rets =>
                  tr = tr' /\ rets = nil
                  /\ seps [cell_value c_ptr (incr_gallina_spec c); R] mem')))
    As body_correct.
  Proof.
    cbv zeta.
    red.
    intros.
    cbn -[incr_gallina_spec cell_value].
    eexists; split.
    { reflexivity. }
    { unfold incr_gallina_spec.

      (* FIXME capture name of binder with Ltac2 *)

      (* Ltac unify_body term := *)
      (*   lazymatch goal with *)
      (*   | [ body := ?evar : cmd |- _ ] => *)
      (*     unify evar term; subst body *)
      (*   end. *)

      (* unify_body (cmd.skip). *)

      unfold seps in H.

      let x := lookup_variable [("c", c_ptr)] c_ptr in
      pose x.

      let e := expr_of_gallina [("c", c_ptr)] c_ptr in
      pose e.

      let x := expr_of_constant (word.of_Z 1) in
      pose x.

      let e := expr_of_gallina [("c", c_ptr)] (word.of_Z 1) in
      pose e.

      subst body.
      match_compile_goal.

      repeat straightline.
      exists (get c).
      split.
      { cbn.
        red.
        exists c_ptr.
        simpl.
        split; try reflexivity.
        eexists.
        split.
        { eapply load_word_of_sep.
          unfold cell_value in *.
          eassumption. }
        { reflexivity. } }

      red.
      simpl map.put.
      set (get c) as v.
      unfold dlet at 1.

      match_compile_goal.
      repeat straightline.
      subst v0.
      subst l.
      set (v0:=word.add v (word.of_Z 1)).
      unfold dlet at 1.
      simpl map.put.

      match_compile_goal.
      unfold cell_value in *.
      repeat straightline.
      unfold dlet at 1.

      match_compile_goal.
      repeat straightline.
      cbn [data put].
      repeat split; try ecancel_assumption. }
    Qed.

  Definition TwoCells a_ptr b_ptr ab : Semantics.mem -> Prop :=
    sep (cell_value a_ptr (fst ab)) (cell_value b_ptr (snd ab)).

  Print swap_gallina_spec.
  Derive swap_body SuchThat
         (let swap := ("swap", (["a"; "b"], [], swap_body)) in
          program_logic_goal_for swap
          (forall functions,
           forall a_ptr a b_ptr b tr R mem,
             sep (TwoCells a_ptr b_ptr (a,b)) R mem ->
             WeakestPrecondition.call
               (swap :: functions)
               "swap"
               tr mem [a_ptr;b_ptr]
               (fun tr' mem' rets =>
                  tr = tr' /\ rets = nil
                  /\ sep (TwoCells a_ptr b_ptr (swap_gallina_spec a b))
                         R mem')))
    As swap_body_correct.
  Proof.
    cbv zeta.
    red.
    intros.
    cbn -[swap_gallina_spec TwoCells Semantics.word].
    eexists; split; [ reflexivity | ].
    unfold swap_gallina_spec.

    subst swap_body.
    unfold TwoCells in *|-.
    cbn [fst snd] in *.
    match_compile_goal.
    repeat straightline.
    exists (get a).
    split.
    { cbn.
      red.
      exists a_ptr.
      simpl.
      split; try reflexivity.
      eexists.
      split.
      { eapply load_word_of_sep.
        unfold cell_value in *.
        ecancel_assumption. }
      { reflexivity. } }
    red.
    simpl map.put.

    set (v1:=get a).
    unfold dlet at 1.

    match_compile_goal.
    repeat straightline.
    exists (get b).
    split.
    { cbn.
      red.
      exists b_ptr.
      simpl.
      split; try reflexivity.
      eexists.
      split.
      { eapply load_word_of_sep.
        unfold cell_value in *.
        ecancel_assumption. }
      { reflexivity. } }
    red.
    simpl map.put.

    set (v2:=get b).
    unfold dlet at 1.

    match_compile_goal.
    repeat straightline.
    eapply store_word_of_sep.
    { instantiate (2:=data _).
      change (scalar ?x (data ?y)) with (cell_value x y).
      ecancel_assumption. }
    intros.
    change (scalar a_ptr v2) with (cell_value a_ptr (put v2 a)) in H0.
    set (c1:=put v2 a) in *.
    unfold dlet at 1.


    match_compile_goal.
    repeat straightline.
    eapply store_word_of_sep.
    { instantiate (2:=data _).
      change (scalar ?x (data ?y)) with (cell_value x y).
      ecancel_assumption. }
    intros.
    change (scalar b_ptr v1) with (cell_value b_ptr (put v1 b)) in H2.
    set (c2:=put v1 b) in *.
    unfold dlet at 1.

    match_compile_goal.
    repeat straightline.
    cbv [TwoCells].
    simpl.
    repeat split; ecancel_assumption.
  Qed.


End Incr.
