Require Import coqutil.sanity coqutil.Macros.subst coqutil.Macros.unique coqutil.Byte.
Require Import coqutil.Datatypes.PrimitivePair coqutil.Datatypes.HList.
Require Import coqutil.Decidable.
Require Import bedrock2.Notations bedrock2.Syntax coqutil.Map.Interface.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.LittleEndian.
Require Import bedrock2.MetricLogging.
Require Export bedrock2.Memory.
Require Import Coq.Lists.List.
Require Import bedrock2.Semantics.

Module step. Section WithEnv.
  Context {pp : unique! parameters} {e: env}.

  (* TODO: also do small-step expression evaluation with non-deterministic order? *)

  Definition state := (cmd * trace * mem * locals)%type.

  (* COQBUG(unification finds Type instead of Prop and fails to downgrade *)
  (* P is not really a post condition, but just a condition on the next
     state after 1 step *)
  Implicit Types P : state -> Prop.

  Inductive step: state -> (state -> Prop) -> Prop :=
  (* cmd.skip does not step because it's done *)
  | set: forall x e t m l mc P v mc',
      eval_expr m l e mc = Some (v, mc') ->
      P (cmd.skip, t, m, map.put l x v) ->
      step (cmd.set x e, t, m, l) P
  | unset: forall x t m l P,
      P (cmd.skip, t, m, map.remove l x) ->
      step (cmd.unset x, t, m, l) P
  | store: forall sz ea ev t m m' l mc P a v mc' mc'',
      eval_expr m l ea mc = Some (a, mc') ->
      eval_expr m l ev mc' = Some (v, mc'') ->
      store sz m a v = Some m' ->
      P (cmd.skip, t, m', l) ->
      step (cmd.store sz ea ev, t, m, l) P
  | if_true: forall t m l mc e c1 c2 v mc' P,
      eval_expr m l e mc = Some (v, mc') ->
      word.unsigned v <> 0 ->
      P (c1, t, m, l) ->
      step (cmd.cond e c1 c2, t, m, l) P
  | if_false: forall t m l mc e c1 c2 mc' P v,
      eval_expr m l e mc = Some (v, mc') ->
      word.unsigned v = 0 ->
      P (c2, t, m, l) ->
      step (cmd.cond e c1 c2, t, m, l) P
  | seq1: forall c1 c2 t m l P,
      step (c1, t, m, l) (fun '(c1', t', m', l') =>
         P (cmd.seq c1' c2, t', m', l')) ->
      step (cmd.seq c1 c2, t, m, l) P
  | seq2: forall c2 t m l P,
      P (c2, t, m, l) ->
      step (cmd.seq cmd.skip c2, t, m, l) P
  | while_true: forall e c t m l mc mc' v P,
      eval_expr m l e mc = Some (v, mc') ->
      word.unsigned v <> 0 ->
      P (cmd.seq c (cmd.while e c), t, m, l) ->
      step (cmd.while e c, t, m, l) P
  | while_false: forall t m l mc e c mc' P v,
      eval_expr m l e mc = Some (v, mc') ->
      word.unsigned v = 0 ->
      P (cmd.skip, t, m, l) ->
      step (cmd.while e c, t, m, l) P
  (*| call: forall binds fname arges t m l mc P params ret fbody
    TODO how to restore caller's env after call? *)
  (* external calls are considered as one step *)
  | interact: forall binds action arges t m l Q P mKeep mGive args mc mc',
      map.split m mKeep mGive ->
      evaluate_call_args_log m l arges mc = Some (args, mc') ->
      ext_spec t mGive action args Q ->
      (forall mReceive resvals, Q mReceive resvals ->
          exists l', map.putmany_of_list_zip binds resvals l = Some l' /\
          exists m', map.split m' mKeep mReceive /\
                     P (cmd.skip, cons ((mGive, action, args), (mReceive, resvals)) t, m', l')) ->
      step (cmd.interact binds action arges, t, m, l) P.

  End WithEnv.
  Arguments step {_} _.
End step. Notation step := step.step.
