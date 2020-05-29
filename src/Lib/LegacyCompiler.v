Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.Compiler.

Ltac compile_step := fail.

Ltac match_compile_goal :=
  lazymatch goal with
  | [  |- WeakestPrecondition.cmd _ ?b2_body _ ?mem
                                 {| value := ?locals |}
                                 (fun (t : Semantics.trace) m _ =>
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

Axiom cell_value : Type.

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
