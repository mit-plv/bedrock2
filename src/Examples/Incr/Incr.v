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
    let/d one := word.of_Z 1 in
    let/d v := word.add v one in
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

  Notation "[[ locals ]]" := ({| value := locals; _value_ok := _ |}) (only printing).

  Definition postcondition_for spec R tr :=
    (fun (tr' : Semantics.trace) (mem' : Semantics.mem) (rets : list address) =>
       tr = tr' /\ rets = nil
       /\ sep spec R mem').

  Definition postcondition_norets spec R tr :=
    (fun (tr' : Semantics.trace) (mem' : Semantics.mem) (_ : Semantics.locals) =>
       postcondition_for spec R tr tr' mem' []).

  Notation "'find' body 'implementing' spec 'with-locals' locals 'and-memory' mem 'and-trace' tr 'and-rest' R 'and-functions' fns" :=
    (WeakestPrecondition.cmd
       (WeakestPrecondition.call fns)
       body tr mem locals
       (postcondition_norets spec R tr)) (at level 0).

  Lemma compile_get :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R R' functions T (pred: T -> _ -> Prop) c c_ptr c_var k k_impl,
    forall var,
      sep (cell_value c_ptr c) R' mem ->
      map.get locals c_var = Some c_ptr ->
      let v := (get c) in
      (let head := v in
       find k_impl
       implementing (pred (k head))
       with-locals (map.put locals var head)
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq (cmd.set var (expr.load access_size.word (expr.var c_var)))
                     k_impl)
       implementing (pred (dlet head k))
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    repeat straightline.
    exists (get c).
    split.
    { cbn.
      red.
      exists c_ptr.
      split.
      { eassumption. }
      { eexists; split; [ | reflexivity ].
        eapply load_word_of_sep.
        eassumption. } }
    red; intros.
    eassumption.
  Qed.

  Lemma compile_constant :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R functions T (pred: T -> _ -> Prop) z k k_impl,
    forall var,
      let v := word.of_Z z in
      (let head := v in
       find k_impl
       implementing (pred (k head))
       with-locals (map.put locals var head)
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq (cmd.set var (expr.literal z)) k_impl)
       implementing (pred (dlet head k))
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    repeat straightline.
    eassumption.
  Qed.

  (* FIXME add let pattern to other lemmas *)
  Lemma compile_add :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R (* R' *) functions T (pred: T -> _ -> Prop) x x_var y y_var k k_impl,
    forall var,
      (* WeakestPrecondition.dexpr mem locals (expr.var x_var) x -> *)
      (* WeakestPrecondition.dexpr mem locals (expr.var y_var) y -> *)
      map.get locals x_var = Some x ->
      map.get locals y_var = Some y ->
      let v := word.add x y in
      (let head := v in
       find k_impl
       implementing (pred (k head))
       with-locals (map.put locals var head)
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq (cmd.set var (expr.op bopname.add (expr.var x_var) (expr.var y_var)))
                     k_impl)
       implementing (pred (dlet head k))
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    repeat straightline.
    eexists; split.
    { repeat straightline.
      exists x; split; try eassumption.
      repeat straightline.
      exists y; split; try eassumption.
      reflexivity. }
    red.
    eassumption.
  Qed.

  Lemma compile_put :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R R' functions T (pred: T -> _ -> Prop) c c_ptr c_var x x_var k k_impl,
      sep (cell_value c_ptr c) R' mem ->
      map.get locals c_var = Some c_ptr ->
      map.get locals x_var = Some x ->
      let v := (put x c) in
      (let head := v in
       forall m,
         sep (cell_value c_ptr head) R' m ->
         (find k_impl
          implementing (pred (k head))
          with-locals locals
          and-memory m and-trace tr and-rest R
          and-functions functions)) ->
      (let head := v in
       find (cmd.seq (cmd.store access_size.word (expr.var c_var) (expr.var x_var))
                     k_impl)
       implementing (pred (dlet head k))
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    unfold cell_value in *.
    repeat straightline.
    exists c_ptr.
    split.
    { repeat straightline; eauto. }
    { eexists; split.
      { repeat straightline; eauto. }
      repeat straightline.
      subst v; simpl.
      match goal with
      | [ H: context[WeakestPrecondition.cmd] |- _ ] => apply H
      end.
      eassumption. }
  Qed.

  Lemma compile_skip :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R functions T (pred: T -> _ -> Prop) head,
      sep (pred head) R mem ->
      (find cmd.skip
       implementing (pred head)
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    repeat straightline.
    red; red; eauto.
  Qed.

  Set Nested Proofs Allowed.

  Ltac solve_map_get_goal :=
    lazymatch goal with
    | [  |- map.get {| value := ?locals; _value_ok := _ |} _ = Some ?val ] =>
      let var := lookup_variable locals val in
      instantiate (1 := var);
      reflexivity
    end.

  Create HintDb compiler.

  Ltac t :=
    lazymatch goal with
    | [  |- let _ := _ in _ ] => intros
    | [  |- context[map.put _ _ _] ] => simpl map.put
    | [  |- WeakestPrecondition.cmd _ _ _ _ _ _ ] =>
      gen_sym_inc;
      let name := gen_sym_fetch "v" in
      (* FIXME compile_skip applies in all cases, so guard it *)
      first [simple eapply compile_get with (var := name) |
             simple eapply compile_put |
             simple eapply compile_constant with (var := name) |
             simple eapply compile_add with (var := name) |
             simple eapply compile_skip]
    | [  |- sep _ _ _ ] =>
      autounfold with compiler in *;
      cbn [fst snd] in *;
      ecancel_assumption
    | [  |- map.get _ _ = Some _ ] => solve_map_get_goal
    end.

  Ltac t_setup :=
    match goal with
    | _ => progress (cbv zeta; unfold program_logic_goal_for)
    | [  |- forall _, _ ] => intros
    | [  |- exists _, _ ] => eexists
    | [  |- _ /\ _ ] => split
    | [  |- context[postcondition_for _ _ _] ] =>
      set (postcondition_for _ _ _)
    | _ => reflexivity
    | _ => cbn
    end.

  Ltac term_head x :=
    match x with
    | ?f _ => term_head f
    | _ => x
    end.

  Ltac setup :=
    repeat t_setup;
    repeat match goal with
           | [ H := _ |- _ ] => subst H
           end;
    match goal with
    | [  |- context[postcondition_for (?pred ?spec) ?R ?tr] ] =>
      change (fun x y _ => postcondition_for (pred spec) R tr x y [])
        with (postcondition_norets (pred spec) R tr);
      let hd := term_head spec in
      unfold hd
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
               (postcondition_for (cell_value c_ptr (incr_gallina_spec c)) R tr)))
    As body_correct.
  Proof.
    setup.
    repeat t.
  Qed.

  Ltac lookup_variable locals ptr ::=
    match locals with
    | [] => fail
    | (?k, ?ptr') :: ?tl =>   (* FIXME do we actually want to unify like this? *)
      let _ := constr:(eq_refl ptr : ptr = ptr') in
      constr:(k)
    | _ :: ?tl =>
      lookup_variable tl ptr
    end.

  Definition TwoCells a_ptr b_ptr ab : Semantics.mem -> Prop :=
    sep (cell_value a_ptr (fst ab)) (cell_value b_ptr (snd ab)).

  Hint Unfold TwoCells : compiler.

  (* FIXME instead of cbn [fst snd], use simpl never hints in the sep case *)
  Arguments Semantics.word : simpl never.

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
               (postcondition_for (TwoCells a_ptr b_ptr (swap_gallina_spec a b)) R tr)))
    As swap_body_correct.
  Proof.
    setup.
    repeat t.
  Qed.
End GallinaIncr.
