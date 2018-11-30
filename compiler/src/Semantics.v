Require Import Coq.ZArith.BinIntDef.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Program.Tactics.
Require Import bbv.DepEqNat.
Require Import lib.LibTacticsMin.
Require Import riscv.util.BitWidths.
Require Import riscv.Utility.
Require Export bedrock2.Syntax.
Require Export bedrock2.Semantics.
Require Import bedrock2.Macros.
Require Import compiler.util.Common.
Require Import compiler.util.Tactics.
Require Import compiler.Op.
Require Import compiler.Decidable.
Require Import compiler.Memory.
Require Import bedrock2.Notations.

Require Coq.Lists.List.

Module Import Semantics.
  Class parameters := {
    syntax :> Basic_bopnames.parameters;

    word : Set;
    word_zero : word;
    word_succ : word -> word;
    word_test : word -> bool;
    word_of_Z : BinNums.Z -> option word;
    interp_binop : bopname -> word -> word -> word;

    byte : Type;
    (* nat included for conceptual completeness, only middle-endian would use it *)
    combine : nat -> byte -> word -> word;
    split : nat -> word -> byte * word;

    mem_Inst : MapFunctions word byte;
    locals_Inst : MapFunctions varname word;

    funname_eqb : funname -> funname -> bool;

    (* TODO: only abstract over action name *)
    Event : Type;
    ext_spec:
      (* given an action label, a trace of what happened so far,
         and a list of function call arguments, *)
      actname -> list Event -> list word ->
      (* returns a set of (extended trace, function call results) *)
      (list Event -> list word -> Prop) ->
      Prop; (* or returns no set if the call fails.
      Will give it access to the memory (and possibly the full registers)
      once we have adequate separation logic reasoning in the compiler correctness proof.
      Passing in the trace of what happened so far allows ext_spec to impose restrictions
      such as "you can only call foo after calling init". *)
  }.
End Semantics.

Existing Instance mem_Inst.
Existing Instance locals_Inst.

Local Notation "' x <- a ; f" :=
  (match (a: option _) with
   | x => f
   | _ => None
   end)
  (right associativity, at level 70, x pattern).

Section semantics.
  Context {pp : unique! parameters}.

  Local Notation mem := (map word byte).

  Fixpoint load_rec (sz : nat) (m:mem) (a:word) : option word :=
    match sz with
    | O => Some word_zero
    | S sz =>
      'Some b <- get m a                     | None;
      'Some w <- load_rec sz m (word_succ a) | None;
       Some (combine sz b w)
    end.
  Definition load n := load_rec (Z.to_nat n).
  Fixpoint unchecked_store_rec (sz : nat) (m:mem) (a v:word) : mem :=
    match sz with
    | O => m
    | S sz =>
      let '(b, w) := split sz v in
      unchecked_store_rec sz (put m a b) (word_succ a) w
    end.
  Definition unchecked_store n := unchecked_store_rec (Z.to_nat n).
  Definition store sz m a v : option mem :=
    match load sz m a with
    | None => None
    | Some _ => Some (unchecked_store sz m a v)
    end.

  Definition trace := list Event.
  Definition locals := map Syntax.varname word.

  Implicit Types post : trace -> mem -> locals -> Prop. (* COQBUG(unification finds Type instead of Prop and fails to downgrade *)

  Fixpoint eval_expr(m: mem)(st: locals)(e: expr): option word :=
    match e with
    | expr.literal v => word_of_Z v
    | expr.var x => get st x
    | expr.load n_bytes a =>
        'Some a' <- eval_expr m st a;
        load n_bytes m a'
    | expr.op op e1 e2 =>
        'Some v1 <- eval_expr m st e1;
        'Some v2 <- eval_expr m st e2;
        Some (interp_binop op v1 v2)
    end.

  Section WithEnv.
    Context {funcMap: MapFunctions funcname (list varname * list varname * cmd)}.
    Notation env := (map funcname (list varname * list varname * cmd)).
    Context (e: env).

    Inductive exec_cmd:
      cmd ->
      trace -> mem -> locals ->
      (trace -> mem -> locals -> Prop) ->
      Prop :=
    | ExSkip: forall t m l post,
        post t m l ->
        exec_cmd cmd.skip t m l post
    | ExSet: forall t m l x y y' post,
        eval_expr m l y = Some y' ->
        post t m (put l x y') ->
        exec_cmd (cmd.set x y) t m l post
    | ExStore: forall t m m' l n_bytes a addr v val post,
        eval_expr m l a = Some addr ->
        eval_expr m l v = Some val ->
        store n_bytes m addr val = Some m' ->
        post t m' l ->
        exec_cmd (cmd.store n_bytes a v) t m l post
    | ExIfThen: forall t m l cond vcond bThen bElse post,
        eval_expr m l cond = Some vcond ->
        vcond <> word_zero ->
        exec_cmd bThen t m l post ->
        exec_cmd (cmd.cond cond bThen bElse) t m l post
    | ExIfElse: forall t m l cond bThen bElse post,
        eval_expr m l cond = Some word_zero ->
        exec_cmd bElse t m l post ->
        exec_cmd (cmd.cond cond bThen bElse) t m l post
     | ExSeq: forall t m l s1 s2 mid post,
        exec_cmd s1 t m l mid ->
        (forall t' m' l', mid t' m' l' -> exec_cmd s2 t' m' l' post) ->
        exec_cmd (cmd.seq s1 s2) t m l post
     | ExWhileDone: forall t m l cond body post,
        eval_expr m l cond = Some word_zero ->
        post t m l ->
        exec_cmd (cmd.while cond body) t m l post
     | ExWhileStep : forall t m l cond body v mid post,
        eval_expr m l cond  = Some v ->
        v <> word_zero ->
        exec_cmd body t m l mid ->
        (forall t' m' l',
            mid t' m' l' ->
            exec_cmd (cmd.while cond body) t' m' l' post) ->
        exec_cmd (cmd.while cond body) t m l post
     | ExCall: forall t m l binds fname args params rets fbody argvs st0 post outcome,
        get e fname = Some (params, rets, fbody) ->
        option_all (List.map (eval_expr m l) args) = Some argvs ->
        putmany params argvs empty_map = Some st0 ->
        exec_cmd fbody t m st0 outcome ->
        (forall t' m' st1,
            outcome t' m' st1 ->
            exists retvs l',
              option_all (List.map (get st1) rets) = Some retvs /\
              putmany binds retvs l = Some l' /\
              post t' m' l') ->
        exec_cmd (cmd.call binds fname args) t m l post
     | ExInteract: forall t m l action argexprs argvals resvars outcome post,
        option_all (List.map (eval_expr m l) argexprs) = Some argvals ->
        ext_spec action t argvals outcome ->
        (forall new_t resvals,
            outcome new_t resvals ->
            exists l', putmany resvars resvals l = Some l' /\ post (new_t) m l') ->
        exec_cmd (cmd.interact resvars action argexprs) t m l post
    .
  End WithEnv.
End semantics.