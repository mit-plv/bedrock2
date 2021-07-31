Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.MetricLogging.
Require Import coqutil.Macros.unique.
Require Import bedrock2.Memory.
Require Import compiler.util.Common.
Require Import coqutil.Decidable.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Byte.
Require Import bedrock2.Syntax.
Require Import coqutil.Z.Lia.
Require Import compiler.SeparationLogic.
Require Import bedrock2.Semantics.
Require Import coqutil.Word.Interface.
Require Import compiler.FlatImp.
Require Import coqutil.Datatypes.ListSet.

Local Hint Mode Word.Interface.word - : typeclass_instances.

Module exec.
  Section FlatImpExec.
    Context {varname: Type} {varname_eqb: varname -> varname -> bool}.
    Context {width: Z} {BW: Bitwidth width} {word: word.word width}.
    Context {mem: map.map word byte} {locals: map.map varname word}
            {env: map.map String.string (list varname * list varname * stmt varname)}.
    Context {ext_spec: ExtSpec}.
    Context {varname_eq_spec: EqDecider varname_eqb}
            {word_ok: word.ok word}
            {mem_ok: map.ok mem}
            {locals_ok: map.ok locals}
            {env_ok: map.ok env}
            {ext_spec_ok: ext_spec.ok ext_spec}.
    Variable (e: env).

    Local Notation metrics := MetricLog.

    Definition one sz addr (value: word) : mem -> Prop :=
      littleendian (bytes_per (width:=width) sz) addr (word.unsigned value).

    (* COQBUG(unification finds Type instead of Prop and fails to downgrade *)
    Implicit Types post : trace -> mem -> locals -> metrics -> Prop.

    Inductive exec:
      stmt varname ->
      trace -> mem -> locals -> metrics ->
      (trace -> mem -> locals -> metrics -> Prop)
    -> Prop :=

    | interact: forall t m Keep Give l mc action argvars argvals resvars outcome post,
        (Keep * Give)%sep m ->
        map.getmany_of_list l argvars = Some argvals ->
        (forall mGive, Give mGive ->
            ext_spec t mGive action argvals outcome /\
            forall mReceive resvals,
            outcome mReceive resvals ->
            exists l', map.putmany_of_list_zip resvars resvals l = Some l' /\
            forall m', (Keep * eq mReceive)%sep m' ->
            post (((mGive, action, argvals), (mReceive, resvals)) :: t) m' l'
                 (addMetricInstructions 1
                 (addMetricStores 1
                 (addMetricLoads 2 mc)))) ->
        exec (SInteract resvars action argvars) t m l mc post

    | call: forall t m l mc binds fname args params rets fbody argvs st0 post outcome,
        map.get e fname = Some (params, rets, fbody) ->
        map.getmany_of_list l args = Some argvs ->
        map.putmany_of_list_zip params argvs map.empty = Some st0 ->
        exec fbody t m st0 mc outcome ->
        (forall t' m' mc' st1,
            outcome t' m' st1 mc' ->
            exists retvs l',
              map.getmany_of_list st1 rets = Some retvs /\
              map.putmany_of_list_zip binds retvs l = Some l' /\
              post t' m' l' mc') ->
        exec (SCall binds fname args) t m l mc post

    | load: forall t m l mc sz R x a o v addr post,
        map.get l a = Some addr ->
        (R * one sz (word.add addr (word.of_Z o)) v)%sep m ->
        post t m (map.put l x v)
             (addMetricLoads 2
             (addMetricInstructions 1 mc)) ->
        exec (SLoad sz x a o) t m l mc post

    | store: forall t m mc l sz a o addr v old_val val R post,
        map.get l a = Some addr ->
        map.get l v = Some val ->
        (R * one sz (word.add addr (word.of_Z o)) old_val)%sep m ->
        (* below could/should be seplog entailment: (R * one sz addr val) ==> post *)
        (forall m',
            (R * one sz (word.add addr (word.of_Z o)) val)%sep m' ->
            post t m' l
                 (addMetricLoads 1
                 (addMetricInstructions 1
                 (addMetricStores 1 mc)))) ->
        exec (SStore sz a v o) t m l mc post

    | stackalloc: forall t (M M': mem -> Prop) mSmall l mc x n body post,
        n mod (bytes_per_word width) = 0 ->
        M mSmall ->
        (forall a mCombined,
            (anybytes a n * M)%sep mCombined ->
            exec body t mCombined (map.put l x a) (addMetricLoads 1 (addMetricInstructions 1 mc))
             (fun t' mCombined' l' mc' =>
                (M' * anybytes a n)%sep mCombined' /\
                forall mSmall', M' mSmall' -> post t' mSmall' l' mc')) ->
        exec (SStackalloc x n body) t mSmall l mc post

    | lit: forall t m l mc x v post,
        post t m (map.put l x (word.of_Z v))
             (addMetricLoads 8
             (addMetricInstructions 8 mc)) ->
        exec (SLit x v) t m l mc post
    | op: forall t m l mc x op y y' z z' post,
        map.get l y = Some y' ->
        map.get l z = Some z' ->
        post t m (map.put l x (interp_binop op y' z'))
             (addMetricLoads 2
             (addMetricInstructions 2 mc)) ->
        exec (SOp x op y z) t m l mc post
    | set: forall t m l mc x y y' post,
        map.get l y = Some y' ->
        post t m (map.put l x y')
             (addMetricLoads 1
             (addMetricInstructions 1 mc)) ->
        exec (SSet x y) t m l mc post
    | if_true: forall t m l mc cond  bThen bElse post,
        eval_bcond l cond = Some true ->
        exec bThen t m l
             (addMetricLoads 2
             (addMetricInstructions 2
             (addMetricJumps 1 mc))) post ->
        exec (SIf cond bThen bElse) t m l mc post
    | if_false: forall t m l mc cond bThen bElse post,
        eval_bcond l cond = Some false ->
        exec bElse t m l
             (addMetricLoads 2
             (addMetricInstructions 2
             (addMetricJumps 1 mc))) post ->
        exec (SIf cond bThen bElse) t m l mc post
    | loop: forall t m l mc cond body1 body2 mid1 mid2 post,
        (* This case is carefully crafted in such a way that recursive uses of exec
         only appear under forall and ->, but not under exists, /\, \/, to make sure the
         auto-generated induction principle contains an IH for all recursive uses. *)
        exec body1 t m l mc mid1 ->
        (forall t' m' l' mc',
            mid1 t' m' l' mc' ->
            eval_bcond l' cond <> None) ->
        (forall t' m' l' mc',
            mid1 t' m' l' mc' ->
            eval_bcond l' cond = Some false ->
            post t' m' l'
                 (addMetricLoads 1
                 (addMetricInstructions 1
                 (addMetricJumps 1 mc')))) ->
        (forall t' m' l' mc',
            mid1 t' m' l' mc' ->
            eval_bcond l' cond = Some true ->
            exec body2 t' m' l' mc' mid2) ->
        (forall t'' m'' l'' mc'',
            mid2 t'' m'' l'' mc'' ->
            exec (SLoop body1 cond body2) t'' m'' l''
                 (addMetricLoads 2
                 (addMetricInstructions 2
                 (addMetricJumps 1 mc''))) post) ->
        exec (SLoop body1 cond body2) t m l mc post

(* Error: Non strictly positive occurrence of "exec"
    | seq_cps: forall t m l mc s1 s2 post,
        exec s1 t m l mc (fun t' m' l' mc' => exec s2 t' m' l' mc' post) ->
        exec (SSeq s1 s2) t m l mc post
*)

    | seq: forall t m l mc s1 s2 mid post,
        exec s1 t m l mc mid ->
        (forall t' m' l' mc', mid t' m' l' mc' -> exec s2 t' m' l' mc' post) ->
        exec (SSeq s1 s2) t m l mc post
    | skip: forall t m l mc post,
        post t m l mc ->
        exec SSkip t m l mc post.

  End FlatImpExec.
End exec.
Notation exec := exec.exec.
