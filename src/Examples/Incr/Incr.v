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

  Definition swap_gallina_spec (c1 c2: cell) :=
    let v1 := get c1 in
    let v2 := get c2 in
    let c1 := put v2 c1 in
    let c2 := put v1 c2 in
    (c1, c2).

  Import dlet.

  Notation "'let/d'  x  :=  val  'in'  body" :=
    (dlet val (fun x => body)) (at level 4).

  Definition incr_gallina_spec (c: cell) :=
    let/d v := get c in
    let/d v := word.add v (word.of_Z 1) in
    let/d c := put v c in
    c.

  Local Infix "~>" := scalar (at level 40, only parsing).

  Require Import derive.Derive.


  Definition mklit z := expr.literal z.

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
      Ltac compile_step b2_body mem locals pred this spec := fail.

      Ltac match_compile_goal :=
        lazymatch goal with
        | [  |- WeakestPrecondition.cmd _ ?b2_body _ ?mem
                                       {| value := ?locals |}
                                       (fun (t : Semantics.trace) (m _ : rep) =>
                                          _ /\
                                          _ /\
                                          sep (?pred ?this ?spec) _ m) ] =>
          compile_step b2_body mem locals pred this spec
        end.

      (* FIXME capture name of binder with Ltac2 *)

      (* Ltac unify_body term := *)
      (*   lazymatch goal with *)
      (*   | [ body := ?evar : cmd |- _ ] => *)
      (*     unify evar term; subst body *)
      (*   end. *)

      (* unify_body (cmd.skip). *)

      unfold seps in H.

      Ltac lookup_object_in predicates predicate value :=
        lazymatch predicates with
        | predicate ?ptr value =>
          ptr                   (* FIXME should recurse *)
        end.

      Ltac lookup_object predicate value mem :=
        lazymatch goal with
        | [ H: sep ?predicates _ mem |- _ ] =>
          let ptr := lookup_object_in predicates predicate value in
          ptr
        end.

      let ptr := lookup_object cell_value c mem in
      pose ptr.

      Ltac lookup_variable locals ptr :=
        match locals with
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
        end.

      let x := lookup_variable [("c", c_ptr)] c_ptr in
      pose x.

      let e := expr_of_gallina [("c", c_ptr)] c_ptr in
      pose e.

      let x := expr_of_constant (word.of_Z 1) in
      pose x.

      let e := expr_of_gallina [("c", c_ptr)] (word.of_Z 1) in
      pose e.

      subst body.

      Ltac compile_step b2_body mem locals pred this spec ::=
        lazymatch spec with
        | (dlet ?value ?continuation) =>
          lazymatch value with
          | get ?c =>
            let ptr := lookup_object cell_value c mem in
            let var := expr_of_gallina locals ptr in
            let b2_continuation := fresh "body" in
            evar (b2_continuation: cmd);
            unify b2_body
                  (cmd.seq (cmd.set "v" (expr.load access_size.word
                                                   var))
                           b2_continuation);
            subst b2_continuation
          | word.add ?l ?r =>
            let ll := expr_of_gallina locals l in
            let rr := expr_of_gallina locals r in
            let b2_continuation := fresh "body" in
            evar (b2_continuation: cmd);
            unify b2_body (* FIXME coq renamed v into v0 *)
                  (cmd.seq (cmd.set "v0" (expr.op
                                            bopname.add
                                            ll rr))
                           b2_continuation);
            subst b2_continuation
          | ?other => fail "Not sure what to do with" other
          end
        end.

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
End Incr.
