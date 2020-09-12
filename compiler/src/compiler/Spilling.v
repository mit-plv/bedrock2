Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Map.SeparationLogic.
Require Import compiler.FlatImp.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.simpl_rewrite.
Require Import coqutil.Datatypes.PropSet.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Utility.Utility.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import compiler.Simp.
Require Import compiler.Simulation.
Require Import compiler.SeparationLogic.
Require Import compiler.SpillingMapGoals.
Require Import bedrock2.MetricLogging.

Open Scope Z_scope.

Module map.
  Section MAP.
    Context {key value} {map : map.map key value}.

    Definition dom(l: map): key -> Prop := fun x => exists v, map.get l x = Some v.

    Inductive mut_disj: list map -> Prop :=
    | mut_disj_nil:
        mut_disj []
    | mut_disj_cons: forall m l,
        (forall m', In m' l -> map.disjoint m m') ->
        mut_disj l ->
        mut_disj (m :: l).

    Definition map_keys{key': Type}{map': map.map key' value}(f: key -> key'): map -> map' :=
      map.fold (fun m' k v => map.put m' (f k) v) map.empty.

    Definition join: list map -> map := List.fold_right map.putmany map.empty.

    Definition splits(L R: list map): Prop := join L = join R /\ mut_disj L /\ mut_disj R.

    Definition geto(a: option map)(k: key): option value :=
      match a with
      | Some m => map.get m k
      | None => None
      end.

    Definition domo(a: option map): key -> Prop :=
      match a with
      | Some m => fun k => exists v, map.get m k = Some v
      | None => fun k => True (* TODO depending on where it's used, this should be False *)
      end.

    Definition putmanyo(a b: option map): option map :=
      match a, b with
      | Some a, Some b => Some (map.putmany a b)
      | _, _ => None
      end.

    (* domains need not be disjoint, but if they overlap, the two maps have to agree on the value *)
    Definition agreeing_putmany{value_eqb: value -> value -> bool}{value_eq_spec: EqDecider value_eqb}
               (a b: option map): option map :=
      match a, b with
      | Some a, Some b => map.fold (fun o k v => match o with
                                                 | Some m => match map.get m k with
                                                             | Some v' => if value_eqb v v'
                                                                          then Some m else None
                                                             | None => Some (map.put m k v)
                                                             end
                                                 | None => None
                                                 end)
                                   (Some a)
                                   b
      | _, _ => None
      end.

    Definition disj_putmany(a b: option map): option map :=
      match a, b with
      | Some a, Some b => map.fold (fun o k v => match o with
                                                 | Some m => match map.get m k with
                                                             | Some _ => None
                                                             | None => Some (map.put m k v)
                                                             end
                                                 | None => None
                                                 end)
                                   (Some a)
                                   b
      | _, _ => None
      end.

    Lemma disj_putmany_empty_l: forall m: option map,
        disj_putmany (Some map.empty) m = m.
    Admitted.

    Lemma disj_putmany_empty_r: forall m: option map,
        disj_putmany m (Some map.empty) = m.
    Admitted.

    Context {ok : map.ok map} {key_eqb: key -> key -> bool} {key_eq_dec : EqDecider key_eqb}.

    Lemma mut_disj_disjoint: forall m1 m2,
        mut_disj [m1; m2] ->
        map.disjoint m1 m2.
    Proof.
      intros. inversion H. subst. eapply H2. simpl. auto.
    Qed.

    Lemma disjoint_mut_disj: forall m1 m2,
        map.disjoint m1 m2 ->
        mut_disj [m1; m2].
    Proof.
      intros. repeat constructor; simpl; intros; subst; try contradiction.
      destruct H0; subst; try assumption. contradiction.
    Qed.

    Lemma split_splits: forall m m1 m2,
        map.split m m1 m2 ->
        splits [m] [m1; m2].
    Proof.
      unfold map.split, splits, join. simpl. intros. destruct H. subst. split.
      - rewrite ?map.putmany_empty_r. reflexivity.
      - repeat constructor; simpl; intros; try contradiction.
        destruct H; subst; firstorder idtac.
    Qed.

    Lemma splits_split: forall m m1 m2,
        splits [m] [m1; m2] ->
        map.split m m1 m2.
    Proof.
      unfold map.split, splits, join. simpl. intros. destruct H as (?&?&?).
      apply mut_disj_disjoint in H1.
      rewrite ?map.putmany_empty_r in H.
      auto.
    Qed.

    Axiom split_spec: forall (M A B: map),
        map.split M A B <-> forall k,
          (exists v, map.get M k = Some v /\
                     ((map.get A k = Some v /\ map.get B k = None) \/
                      (map.get B k = Some v /\ map.get A k = None))) \/
          (map.get M k = None /\ map.get A k = None /\ map.get B k = None).

    Axiom putmany_spec: forall (m1 m2: map) k,
        (exists v, map.get (map.putmany m1 m2) k = Some v /\
                   (map.get m2 k = Some v \/ (map.get m2 k = None /\ map.get m1 k = Some v))) \/
        (map.get (map.putmany m1 m2) k = None /\ map.get m2 k = None /\ map.get m1 k = None).

    Axiom getmany_of_list_shrink: forall (l l1 l2: map) keys,
        map.split l l1 l2 ->
        Forall (fun k => map.get l2 k = None) keys ->
        map.getmany_of_list l keys = map.getmany_of_list l1 keys.

    Axiom putmany_of_list_zip_split: forall (l l' l1 l2: map) keys values,
        map.putmany_of_list_zip keys values l = Some l' ->
        map.split l l1 l2 ->
        Forall (fun k => map.get l2 k = None) keys ->
        exists l1', map.split l' l1' l2 /\ map.putmany_of_list_zip keys values l1 = Some l1'.

    Axiom putmany_of_list_zip_grow: forall (l l1 l1' l2: map) keys values,
        map.putmany_of_list_zip keys values l1 = Some l1' ->
        map.split l l1 l2 ->
        Forall (fun k => map.get l2 k = None) keys ->
        exists l', map.split l' l1' l2 /\ map.putmany_of_list_zip keys values l = Some l'.

    Lemma getmany_of_list_preserved: forall (l1 l2: map) ks,
        (forall k, In k ks -> map.get l1 k = map.get l2 k) ->
        map.getmany_of_list l1 ks = map.getmany_of_list l2 ks.
    Proof.
      induction ks; intros. 1: reflexivity.
      unfold map.getmany_of_list in *. simpl.
      rewrite IHks. 2: {
        intros. eapply H. simpl. auto.
      }
      specialize (H a). simpl in H. rewrite H. 2: auto.
      reflexivity.
    Qed.

    (* disjoint-unions *)
    Definition dus'(l: list (option map)): option map :=
      List.fold_left (fun res e => disj_putmany res e) l (Some map.empty).

    Fixpoint dus (xs : list (option map)) : option map :=
      match xs with
      | [x] => x
      | x :: xs => disj_putmany (dus xs) x
      | nil => Some map.empty
      end.

  End MAP.
End map.


Section Spilling.

  Notation stmt := (stmt Z).

  Definition zero := 0.
  Definition ra := 1.
  Definition sp := 2.
  Definition tmp1 := 3.
  Definition tmp2 := 4.
  Definition fp := 5. (* returned by stackalloc, always a constant away from sp: a wasted register *)
  Definition regvar0 := 6.

  (* TODO: storing value returned by stackalloc into a register is always a wasted register,
     because it's constant away from the stackpointer

     integrate spilling into FlatToRiscv?

     Or make StackImp language with same syntax as FlatImp but with a stack in the memory and
     which shares the register file among function calls? *)

  (* Definition needs_spilling: Z -> bool := Z.leb 32. *)

  Context {W: Utility.Words} {mem: map.map word byte} {mem_ok: map.ok mem}.

  Definition stack_loc(r: Z): option Z :=
    if Z.leb 32 r then Some ((r - 32) * bytes_per_word) else None.

  Definition arg_reg1(r: Z): Z := if Z.leb 32 r then tmp1 else r.
  Definition arg_reg2(r: Z): Z := if Z.leb 32 r then tmp2 else r.
  Definition res_reg(r: Z): Z := if Z.leb 32 r then tmp1 else r.

  Definition load_arg_reg1(r: Z): stmt :=
    match stack_loc r with
    | Some o => SLoad Syntax.access_size.word tmp1 fp o
    | None => SSkip
    end.

  Definition load_arg_reg2(r: Z): stmt :=
    match stack_loc r with
    | Some o => SLoad Syntax.access_size.word tmp2 fp o
    | None => SSkip
    end.

  Definition save_res_reg(r: Z): stmt :=
    match stack_loc r with
    | Some o => SStore Syntax.access_size.word fp tmp1 o
    | None => SSkip
    end.

  Notation "s1 ;; s2" := (SSeq s1 s2) (right associativity, at level 100).

  Definition prepare_bcond(c: bcond Z): stmt :=
    match c with
    | CondBinary _ x y => load_arg_reg1 x;; load_arg_reg2 y
    | CondNez x => load_arg_reg1 x
    end.

  Definition spill_bcond(c: bcond Z): bcond Z :=
    match c with
    | CondBinary op x y => CondBinary op (arg_reg1 x) (arg_reg2 y)
    | CondNez x => CondNez (arg_reg1 x)
    end.

  Fixpoint spill_stmt(s: stmt): stmt :=
    match s with
    | SLoad sz x y o =>
      load_arg_reg1 y;;
      SLoad sz (res_reg x) (arg_reg1 y) o;;
      save_res_reg x
    | SStore sz x y o =>
      load_arg_reg1 x;; load_arg_reg2 y;;
      SStore sz (arg_reg1 x) (arg_reg2 y) o
    | SStackalloc x n body =>
      SStackalloc (res_reg x) n (save_res_reg x;; spill_stmt body)
    | SLit x n =>
      SLit (res_reg x) n;;
      save_res_reg x
    | SOp x op y z =>
      load_arg_reg1 y;; load_arg_reg2 z;;
      SOp (res_reg x) op (arg_reg1 y) (arg_reg2 z);;
      save_res_reg x
    | SSet x y => (* TODO could be optimized if exactly one is on the stack *)
      load_arg_reg1 y;;
      SSet (res_reg x) (arg_reg1 y);;
      save_res_reg x
    | SIf c thn els =>
      prepare_bcond c;;
      SIf (spill_bcond c) (spill_stmt thn) (spill_stmt els)
    | SLoop s1 c s2 =>
      SLoop (spill_stmt s1;; prepare_bcond c) (spill_bcond c) (spill_stmt s2)
    | SSeq s1 s2 => SSeq (spill_stmt s1) (spill_stmt s2)
    | SSkip => SSkip
    (* Note: these two are only correct if argvars and resvars all are registers! *)
    | SCall argvars f resvars => SCall argvars f resvars
    | SInteract argvars f resvars => SInteract argvars f resvars
    end.

  Definition valid_vars_bcond(c: bcond Z): Prop :=
    match c with
    | CondBinary _ x y => fp < x /\ fp < y
    | CondNez x => fp < x
    end.

  (*
  Fixpoint calls_use_registers(s: stmt): bool :=
    match s with
    | SLoad _ _ _ _ | SStore _ _ _ _ | SLit _ _ | SOp _ _ _ _ | SSet _ _ | SSkip => true
    | SStackalloc x n body => calls_use_registers body
    | SIf _ s1 s2 | SLoop s1 _ s2 | SSeq s1 s2 => calls_use_registers s1 && calls_use_registers s2
    | SCall argvars _ resvars | SInteract argvars _ resvars =>
      List.forallb (Z.gtb 32) argvars && List.forallb (Z.gtb 32) resvars
    end.
   *)

  Definition max_var_bcond(c: bcond Z): Z :=
    match c with
    | CondBinary _ x y => Z.max x y
    | CondNez x => x
    end.

  Fixpoint max_var(s: stmt): Z :=
    match s with
    | SLoad _ x y _ | SStore _ x y _ | SSet x y => Z.max x y
    | SStackalloc x n body => Z.max x (max_var body)
    | SLit x _ => x
    | SOp x _ y z => Z.max x (Z.max y z)
    | SIf c s1 s2 | SLoop s1 c s2 => Z.max (max_var_bcond c) (Z.max (max_var s1) (max_var s2))
    | SSeq s1 s2 => Z.max (max_var s1) (max_var s2)
    | SSkip => 0
    (* Variables involved in function calls are not spilled, so we can ignore them *)
    | SCall argvars f resvars | SInteract argvars f resvars => 0
    end.

  Definition spill_fbody(s: stmt): stmt :=
    SStackalloc fp (bytes_per_word * (max_var s - 32)) (spill_stmt s).

  Context {locals: map.map Z word}.
  Context {localsOk: map.ok locals}.
  Context {env: map.map String.string (list Z * list Z * stmt)}.
  Context (ext_spec:  list (mem * String.string * list word * (mem * list word)) ->
                      mem -> String.string -> list word -> (mem -> list word -> Prop) -> Prop).

  Instance semanticsParams: FlatImp.parameters Z. refine ({|
    FlatImp.varname_eqb := Z.eqb;
    FlatImp.locals := locals;
    FlatImp.ext_spec := ext_spec;
  |}).
  Defined.

  Definition valid_vars_src(maxvar: Z): stmt -> Prop :=
    Forall_vars_stmt (fun x => fp < x <= maxvar) (fun x => fp < x < 32).

  Definition valid_vars_tgt: stmt -> Prop :=
    Forall_vars_stmt (fun x => sp < x <= 32) (fun x => sp < x < 32).

  Lemma spill_stmt_valid_vars: forall s m,
      max_var s <= m ->
      valid_vars_src m s ->
      valid_vars_tgt (spill_stmt s).
  Proof.
    (* Wihtout the clear, firstorder becomes very slow COQBUG https://github.com/coq/coq/issues/11352.
       Not using firstorder though because there's something higher order here: *)
    clear mem mem_ok locals localsOk env ext_spec.
    assert (forall vars, Forall (fun x : Z => 5 < x < 32) vars -> Forall (fun x : Z => 2 < x < 32) vars). {
      intros. eapply Forall_impl. 2: eassumption. simpl. blia.
    }
    unfold valid_vars_src, valid_vars_tgt.
    induction s; simpl; intros;
      repeat match goal with
             | c: bcond Z |- _ => destr c
             | |- context[Z.leb ?x ?y] => destr (Z.leb x y)
             | |- _ => progress simpl
             | |- _ => progress unfold tmp1, tmp2, sp, fp, res_reg, arg_reg1, arg_reg2, res_reg,
                         spill_bcond, max_var_bcond, ForallVars_bcond, prepare_bcond,
                         load_arg_reg1, load_arg_reg2, save_res_reg, stack_loc in *
             end;
      try blia;
      simp;
      repeat match goal with
      | IH: _, H: Forall_vars_stmt _ _ _ |- _ =>
        specialize IH with (2 := H);
        match type of IH with
        | ?P -> _ => let A := fresh in assert P as A by blia; specialize (IH A); clear A
        end
      end;
      eauto;
      intuition try blia.
  Qed.

  Definition oeq{T: Type}(oL oR: option T): Prop := exists L R, oL = Some L /\ oR = Some R /\ oL = oR.

  Notation "a \+/ b" := (map.disj_putmany a b) (at level 34, left associativity).
  Notation "a \</ b" := (map.putmanyo a b) (at level 34, left associativity).
  Notation "a \?/ b" := (map.agreeing_putmany a b) (at level 34, left associativity).
  Notation "k ~> v" := (Some (map.put map.empty k v)) (at level 30).

  Infix "==" := oeq (at level 38).

  Definition one(sz: Syntax.access_size.access_size)(addr value: word): option mem :=
    Some (map.putmany_of_tuple (Memory.footprint addr (@Memory.bytes_per width sz))
                               (LittleEndian.split (@Memory.bytes_per width sz) (word.unsigned value))
                               map.empty).

  Definition array{T: Type}(elem: word -> T -> option mem)(size: word): word -> list T -> option mem :=
    fix rec addr ls :=
      match ls with
      | [] => Some map.empty
      | e :: es => elem addr e \+/ rec (word.add addr size) es
      end.

  Definition word_array: word -> list word -> option mem :=
    array (one Syntax.access_size.word) (word.of_Z bytes_per_word).

  Definition related(maxvar: Z)(frame: option mem)(done: bool)
             (t1: trace)(m1: option mem)(l1: option locals)(mc1: MetricLog)
             (t2: trace)(m2: option mem)(l2: option locals)(mc2: MetricLog): Prop :=
      exists fpval tmp1val tmp2val lStack lRegs stackwords,
        t1 = t2 /\
        m2 == m1 \+/ word_array fpval stackwords \+/ frame /\
        subset (map.domo lRegs) (fun x => fp < x < 32) /\
        subset (map.domo lStack) (fun x => 32 <= x <= maxvar) /\
        l1 = lRegs \+/ lStack /\
        l2 = lRegs \+/ tmp1 ~> tmp1val \+/ tmp2 ~> tmp2val \+/ fp ~> fpval /\
        forall r, 32 <= r <= maxvar -> forall v, map.geto lStack r = Some v ->
           nth_error stackwords (Z.to_nat (r - 32)) = Some v.

  (*
  Notation "m [ k := v ]" := (map.put m k v) (at level 10, left associativity, format "m [ k  :=  v ]").
  Notation "m [ k ]" := (map.get m k) (at level 10, left associativity, format "m [ k ]").
  (* this notation overrides the notation for applying a function m to the singleton list containing k,
     but that's so rare that it's fine *)

  Definition related(maxvar: Z)(frame: mem)(done: bool):
    FlatImp.SimState Z -> FlatImp.SimState Z -> Prop :=
    fun '(t1, m1, l1, mc1) '(t2, m2, l2, mc2) =>
      exists fpval tmp1val tmp2val mStack lStack lRegs,
        t1 = t2 /\
        m2 = map.putmany m1 (map.putmany mStack frame) /\
        disjoint (map.dom m1) (map.dom mStack) /\
        disjoint (map.dom m1) (map.dom frame) /\
        disjoint (map.dom mStack) (map.dom frame) /\
        subset (map.dom lRegs) (fun x => fp < x < 32) /\
        subset (map.dom lStack) (fun x => 32 <= x <= maxvar) /\
        l1 = map.putmany lRegs lStack /\
        l2 = lRegs[tmp1 := tmp1val][tmp2 := tmp2val][fp := fpval] /\
        spilled_vars fpval maxvar lStack mStack.

  Definition related(maxvar: Z)(frame: option mem)(done: bool)
             (t1: trace)(m1: option mem)(l1: option locals)(mc1: MetricLog)
             (t2: trace)(m2: option mem)(l2: option locals)(mc2: MetricLog): Prop :=
      exists fpval tmp1val tmp2val mStack lStack lRegs,
        t1 = t2 /\
        m2 = m1 \+/ mStack \+/ frame /\
        subset (map.domo lRegs) (fun x => fp < x < 32) /\
        subset (map.domo lStack) (fun x => 32 <= x <= maxvar) /\
        l1 = lRegs \+/ lStack /\
        l2 = lRegs \+/ tmp1 ~> tmp1val \+/ tmp2 ~> tmp2val \+/ fp ~> fpval /\
        spilled_vars fpval maxvar lStack mStack.

  Definition related(maxvar: Z)(frame: mem)(done: bool):
    FlatImp.SimState Z -> FlatImp.SimState Z -> Prop :=
    fun '(t1, m1, l1, mc1) '(t2, m2, l2, mc2) =>
      exists fpval tmp1val tmp2val mStack lStack lRegs,
        t1 = t2 /\
        Some m2 = Some m1 \+/ Some mStack \+/ Some frame /\
        subset (map.dom lRegs) (fun x => fp < x < 32) /\
        subset (map.dom lStack) (fun x => 32 <= x <= maxvar) /\
        Some l1 = Some lRegs \+/ Some lStack /\
        Some l2 = Some lRegs \+/ tmp1 ~> tmp1val \+/ tmp2 ~> tmp2val \+/ fp ~> fpval /\
        spilled_vars fpval maxvar lStack mStack.

  Notation "k ~> v" := (map.put map.empty k v) (at level 30).

  Definition related(maxvar: Z)(frame: mem)(done: bool):
    FlatImp.SimState Z -> FlatImp.SimState Z -> Prop :=
    fun '(t1, m1, l1, mc1) '(t2, m2, l2, mc2) =>
      exists fpval tmp1val tmp2val mStack lStack lRegs,
        t1 = t2 /\
        map.splits [m2] [m1; mStack; frame] /\
        subset (map.dom lRegs) (fun x => fp < x < 32) /\
        subset (map.dom lStack) (fun x => 32 <= x <= maxvar) /\
        map.splits [l1] [lRegs; lStack] /\
        map.splits [l2] [lRegs; tmp1 ~> tmp1val; tmp2 ~> tmp2val; fp ~> fpval] /\
        spilled_vars fpval maxvar lStack mStack.
*)

  Definition envs_related(e1 e2: env): Prop :=
    forall f argvars resvars body1,
      map.get e1 f = Some (argvars, resvars, body1) ->
      map.get e2 f = Some (argvars, resvars, spill_fbody body1).

  Lemma seq_cps: forall e s1 s2 t m l mc post,
      exec e s1 t m l mc (fun t' m' l' mc' => exec e s2 t' m' l' mc' post) ->
      exec e (SSeq s1 s2) t m l mc post.
  Proof.
    intros. eapply exec.seq. 1: eassumption. simpl. clear. auto.
  Qed.

  Lemma load_putmany_l: forall m1 m2 sz a v,
      Memory.load sz m1 a = Some v ->
      disjoint (map.dom m1) (map.dom m2) ->
      Memory.load sz (map.putmany m1 m2) a = Some v.
  Proof.
  Admitted.

  (* cps style
  Lemma load_arg_reg1_correct: forall e a t m l mc post,
      post ... ->
      exec e (load_arg_reg1 a) t m l mc post. *)

  (* seq style
  Lemma load_arg_reg1_correct: forall e s a t m l mc post,
      exec e s t
      exec e (SSeq (load_arg_reg1 a) s) t m l mc post. *)

  Arguments map.disj_putmany : simpl never.

  Implicit Types post : trace -> option mem -> option locals -> MetricLog -> Prop.

  Section WithE.
    Variable (e: env).

(*
    Definition ext_spec' t mGive action argvals (outcome: mem -> list word -> Prop) :=
      match mGive with
      | Some mGive => ext_spec t mGive action argvals outcome
      | None => False
      end.

    Definition ext_spec' t mGive action argvals (outcome: option mem -> list word -> Prop) :=
      match mGive with
      | Some mGive => ext_spec t mGive action argvals
                               (fun mReceive resvals => outcome (Some mReceive) resvals)
      | None => False
      end.
*)

    Inductive exec:
      stmt ->
      trace -> option mem -> option locals -> MetricLog ->
      (trace -> option mem -> option locals -> MetricLog -> Prop)
    -> Prop :=
    | interact: forall t m mKeep mGive l l_not_read l_not_written oldresvals mc action argvars
                       argvals resvars outcome post,
        m == mKeep \+/ Some mGive ->
        l == l_not_read \+/ map.of_list_zip argvars argvals ->
        l == l_not_written \+/ map.of_list_zip resvars oldresvals ->
        ext_spec t mGive action argvals outcome ->
        (forall mReceive resvals,
            outcome mReceive resvals ->
            exists l', l' == l_not_written \+/ map.of_list_zip resvars resvals /\
            forall m', m' == mKeep \+/ Some mReceive ->
            post (((mGive, action, argvals), (mReceive, resvals)) :: t) m' l'
                 (addMetricInstructions 1
                 (addMetricStores 1
                 (addMetricLoads 2 mc)))) ->
        exec (SInteract resvars action argvars) t m l mc post

    | call: forall t m l mc binds fname args params rets fbody (*argvs st0*) post (* outcome *),
        map.get e fname = Some (params, rets, fbody) ->
        (* TODO
        map.getmany_of_list l args = Some argvs ->
        map.putmany_of_list_zip params argvs map.empty = Some st0 ->
        exec fbody t m st0 mc outcome ->
        (forall t' m' mc' st1,
            outcome t' m' st1 mc' ->
            exists retvs l',
              map.getmany_of_list st1 rets = Some retvs /\
              map.putmany_of_list_zip binds retvs l = Some l' /\
              post t' m' l' mc') ->
              *)
        exec (SCall binds fname args) t m l mc post
    | load: forall t m mFrame l l' lFrame mc sz x a o v addr post,
        l == lFrame \+/ a ~> addr ->
        m == mFrame \+/ one sz (word.add addr (word.of_Z o)) v ->
        l' == l \</ x ~> v ->
        post t m l'
             (addMetricLoads 2
             (addMetricInstructions 1 mc)) ->
        exec (SLoad sz x a o) t m l mc post
    | store: forall t (m mFrame m': option mem) mc l lFrame sz a o addr v (val oldval: word) post,
        l == lFrame \+/ (a ~> addr \?/ v ~> val) ->
        m == mFrame \+/ one sz (word.add addr (word.of_Z o)) oldval ->
        m' == mFrame \+/ one sz (word.add addr (word.of_Z o)) val ->
        post t m' l
             (addMetricLoads 1
             (addMetricInstructions 1
             (addMetricStores 1 mc))) ->
        exec (SStore sz a v o) t m l mc post
    | stackalloc: forall t mSmall l mc x n body post,
        n mod bytes_per_word = 0 ->
        (forall l0 a stacktrash mCombined,
            mCombined == mSmall \+/ map.of_disjoint_list_zip (Memory.ftprint a n) stacktrash ->
            l0 == l \</ x ~> a ->
            exec body t mCombined l0 (addMetricLoads 1 (addMetricInstructions 1 mc))
             (fun t' mCombined' l' mc' =>
              exists mSmall' stacktrash',
                mCombined' == mSmall' \+/ map.of_disjoint_list_zip (Memory.ftprint a n) stacktrash' /\
                post t' mSmall' l' mc')) ->
        exec (SStackalloc x n body) t mSmall l mc post

(*
    | lit: forall t m l mc x v post,
        post t m (map.put l x (word.of_Z v))
             (addMetricLoads 8
             (addMetricInstructions 8 mc)) ->
        exec (SLit x v) t m l mc post
*)

    | op: forall t m l l' lFrame mc x op y y' z z' post,
        l == lFrame \+/ (y ~> y' \?/ z ~> z') ->
        l' == l \</ x ~> Semantics.interp_binop op y' z' ->
        post t m l'
             (addMetricLoads 2
             (addMetricInstructions 2 mc)) ->
        exec (SOp x op y z) t m l mc post

(*
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
    | seq: forall t m l mc s1 s2 mid post,
        exec s1 t m l mc mid ->
        (forall t' m' l' mc', mid t' m' l' mc' -> exec s2 t' m' l' mc' post) ->
        exec (SSeq s1 s2) t m l mc post
    | skip: forall t m l mc post,
        post t m l mc ->
        exec SSkip t m l mc post
*)
.

  End WithE.

  Lemma mem_eq_trans: forall m1 m2 m3: option mem,
      m1 == m2 -> m2 == m3 -> m1 == m3.
  Admitted.

  Lemma mem_eq_rewrite: forall F A L R: option mem,
      L == R ->
      A == L \+/ F ->
      A == R \+/ F.
  Admitted.

  (* Note: does not hold if m is None! *)
  Lemma mem_eq_refl: forall m A B: option mem,
      A == B \+/ m -> (* <-- to assert that m is not None *)
      m == m.
  Proof.
    unfold oeq, map.disj_putmany. intros. simp. clear. eauto.
  Qed.

  Section cancel_lemmas.
    Let nth n xs := hd (@None mem) (skipn n xs).
    Let remove_nth n (xs : list (option mem)) :=
      (firstn n xs ++ tl (skipn n xs)).

    Lemma mem_eq_cancel_at: forall (i j: nat) (xs ys: list (option mem)),
        nth i xs = nth j ys ->
        map.dus (remove_nth i xs) == map.dus (remove_nth j ys) ->
        map.dus xs == map.dus ys.
    Proof.
    Admitted.
  End cancel_lemmas.

  Ltac cancel_at_indices i j :=
    lazymatch goal with
    | |- map.dus ?LHS == map.dus ?RHS =>
      simple refine (mem_eq_cancel_at i j LHS RHS _ _);
      cbn [firstn skipn List.app hd tl]
    end.

  Lemma spilling_correct (e e1 e2 : env) (Ev : envs_related e1 e2)
        (s1 : stmt)
  (t1 : trace)
  (m1 : option mem)
  (l1 : option locals)
  (mc1 : MetricLog)
  (post : trace -> option mem -> option locals -> MetricLog -> Prop):
  exec e1 s1 t1 m1 l1 mc1 post ->
  forall (frame : option mem) (maxvar : Z),
  valid_vars_src maxvar s1 ->
  forall (t2 : trace) (m2 : option mem) (l2 : option locals) (mc2 : MetricLog),
  related maxvar frame false t1 m1 l1 mc1 t2 m2 l2 mc2 ->
  exec e2 (spill_stmt s1) t2 m2 l2 mc2
    (fun (t2' : trace) (m2' : option mem) (l2' : option locals) (mc2' : MetricLog) =>
       exists t1' m1' l1' mc1',
         related maxvar frame false t1' m1' l1' mc1' t2' m2' l2' mc2' /\
         post t1' m1' l1' mc1').
  Proof.
    unfold related. induction 1; intros; simp; subst.
    - (* exec.interact *)
      eapply interact.
      + eapply mem_eq_trans. 1: eassumption.
        eapply mem_eq_trans.
        * eapply mem_eq_rewrite. 1: exact H.
          match goal with
          | |- ?L1 \+/ ?L2 \+/ ?L3 == ?R1 \+/ ?R2 =>
            change (map.dus [L3; L2; L1] == map.dus [R2; R1])
          end.
          cancel_at_indices 2%nat 1%nat. 1: reflexivity.
          cbv [map.dus].
          eapply mem_eq_refl.
          eapply mem_eq_trans. 1: exact H5rl.
          match goal with
          | |- ?L1 \+/ ?L2 \+/ ?L3 == ?R1 \+/ ?R2 =>
            change (map.dus [L3; L2; L1] == map.dus [R2; R1])
          end.


(*
  Lemma spilling_sim(e1 e2: env):
      envs_related e1 e2 ->
      forall frame s1 maxvar,
        valid_vars_src maxvar s1 ->
        simulation (SimExec Z e1 s1) (SimExec Z e2 (spill_stmt s1))
                   (related maxvar frame).
  Proof.
    unfold simulation, SimExec.
    intros Ev frame s1 maxvar V (((t1 & m1) & l1) & mc1) (((t2 & m2) & l2) & mc2) post1 R Exec.
    revert frame maxvar V t2 m2 l2 mc2 R.
    unfold compile_inv, related.
    match type of Exec with
    | FlatImp.exec _ _ _ _ _ _ ?P => remember P as post
    end.
    revert post1 Heqpost.
    induction Exec; simpl; intros; simp; subst.
    - (* exec.interact *)


    - (* exec.interact *)
      eapply map.split_splits in H.
      eapply @exec.interact with (mGive := mGive) (mKeep := map.putmany mKeep (map.putmany mStack frame)).
      + eapply map.splits_split.

(*

disjoint union on "option map" ?
m \+/ mStack \+/ frame

lRegs \+/ tmp1 ~> tmp1val \+/ tmp2 ~> tmp2val

but what to pass to exec.interact? -> also "option map"

disjoint_putmany

just congruence:
a = c ->
b = d ->
a \+/ b = c \+/ d

*)
      + unfold map.split in *; simp. split.
        * remember (map.putmany mStack frame) as A.
          rewrite <- map.putmany_assoc.
          { erewrite <- (@map.putmany_assoc _ _ _ _ _ word.eqb_spec).
            { f_equal.
              apply map.putmany_comm.
              subst A.

          1: exact mem_ok.

          { assert (map.ok FlatImp.mem = map.ok mem). {
              clear.
              reflexivity.

rewrite <- (@map.putmany_assoc _ _ _ mem_ok word.eqb).


subst. eapply split_interact; try eassumption.
      + erewrite map__getmany_of_list_shrink. 2: eassumption. 2: {
          eapply Forall_impl. 2: eassumption.
          clear -localsOk. unfold fp, tmp1, tmp2. intros.
          rewrite ?map.get_put_dec.
          rewrite ?(proj2 (Z.eqb_neq _ _ )) by blia.
          apply map.get_empty.
        }
        erewrite <- map__getmany_of_list_shrink; [eassumption..|].
        eapply Forall_impl. 2: eassumption.
        simpl.
        intros. unfold map__dom_in in *.
        destr (map.get lStack a). 2: reflexivity.
        match goal with
        | H: forall _, _ |- _ => specialize H with (1 := E)
        end.
        blia.
      + eassumption.
      + intros.
        match goal with
        | H: context[outcome], A: context[outcome] |- _ =>
          specialize H with (1 := A); move H at bottom
        end.
        simp.
        pose proof H2l as P.
        eapply map__putmany_of_list_zip_split in P. 2: eassumption. 2: {
          eapply Forall_impl. 2: eassumption.
          simpl.
          intros. unfold map__dom_in in *.
          destr (map.get lStack a). 2: reflexivity.
          match goal with
          | H: forall _, _ |- _ => specialize H with (1 := E)
          end.
          blia.
        }
        simp.
        eapply map__putmany_of_list_zip_grow with (l := l2) in Pr. 2: eassumption. 2: {
          eapply Forall_impl. 2: eassumption.
          clear -localsOk. unfold fp, tmp1, tmp2. intros.
          rewrite ?map.get_put_dec.
          rewrite ?(proj2 (Z.eqb_neq _ _ )) by blia.
          apply map.get_empty.
        }
        destruct Pr as (l2' & ? & ?).
        eexists. split. 1: eassumption.
        intros.
        repeat match goal with
               | |- exists (_: FlatImp.SimState _), _ => refine (ex_intro _ (_, _, _, _) _)
               | |- exists _, _ => eexists
               | |- _ /\ _ => split
               end.
        9: eapply H2r.
        1: reflexivity.
        8: eapply split_interact_shrink; eassumption.
        1: eapply split_interact_assoc; eassumption.
        1: eassumption.
        5: eassumption.
        4: eassumption.
        3: eassumption.
        2: eassumption.
        assert (map__dom_in (map.put (map.put (map.put map.empty fp fpval) tmp2 tmp2val) tmp1 tmp1val)
                            (fun x => x = fp \/ x = tmp2 \/ x = tmp1)) as A. {
          unfold map__dom_in. clear -localsOk. intros. rewrite ?map.get_put_dec in H.
          repeat destruct_one_match_hyp; subst; auto.
          rewrite map.get_empty in H. discriminate.
        }
        pose proof map__split_dom_in _ _ _ _ _ Rrrrrrrl Rrrrl A as B. simpl in B.
        pose proof map__putmany_of_list_zip_dom_in as C.
        specialize C with (1 := H4) (2 := B). simpl in C.
        apply map__split_dom_spec in H2. simp.
        assert (subset (of_list resvars) (fun x : Z => fp < x < 32)) as Vl' by admit.
        assert (subset (of_list argvars) (fun x : Z => fp < x < 32)) as Vr' by admit.
        change (map__dom_in l2' (union (fun x : Z => (fp < x < 32 \/ x = fp \/ x = tmp2 \/ x = tmp1)) (of_list resvars))) in C.
        assert (subset (map__dom l2') (union (fun x : Z => (fp < x < 32 \/ x = fp \/ x = tmp2 \/ x = tmp1)) (of_list resvars))) as C' by admit.
        clear - H2l0 H2r0 Vl' C'.
        unfold fp, tmp1, tmp2 in *.
        replace (map__dom (map.put (map.put (map.put map.empty 5 fpval) 4 tmp2val) 3 tmp1val)) with
            (fun x => x = 5 \/ x = 4 \/ x = 3) in * by admit.
        assert (subset (map__dom l1') (fun x : Z => fp < x < 32)). {
          set_solver_generic Z; try blia.
        }
        admit. (* ok, but TODO use map__dom instead of map__dom_in *)

    - (* exec.call *)
      admit.
    - (* exec.load *)
      eapply seq_cps.
      unfold load_arg_reg1, arg_reg1, save_res_reg, res_reg, stack_loc.
      destr (Z.leb 32 a).
      + match goal with
        | H: spilled_vars _ _ _ _ |- _ => pose proof H as A
        end.
        unfold spilled_vars in A.
        assert (32 <= a <= maxvar) as B by blia. specialize A with (1 := B); clear B. simp.
        eapply exec.load with (addr0 := fpval) (v1 := v0).
        * admit. (* ok *)
        * eapply grow_load. 1: eassumption.

jj
admit. (* growing from mStack to m2 preserves Memory.load *)
        * eapply seq_cps. eapply exec.load. {
            rewrite map.get_put_same. reflexivity.
          } {
            match goal with
            | |- _ = ?opt => unify opt (Some v)
            end.
            assert (map.get lStack a = Some addr) as B by admit.
            specialize Ar with (1 := B). subst v0.
            (* growing from m to m2 preserves Memory.load *)
            admit.
          } {
            destr (Z.leb 32 x).
            - eapply exec.store.
              + rewrite ?map.get_put_diff by (cbv; discriminate).
                match goal with
                | |- _ = ?opt => unify opt (Some fpval)
                end.
                admit. (* ok *)
              + rewrite map.get_put_same. reflexivity.
              + admit. (* memory stuff... *)
              + repeat match goal with
                       | |- exists (_: FlatImp.SimState _), _ => refine (ex_intro _ (_, _, _, _) _)
                       | |- exists _, _ => eexists
                       | |- _ /\ _ => split
                       end.
                1: reflexivity.
                8: eassumption.
                * admit.
                * admit.
                * admit.
                * admit.
                * admit.
                * rewrite map.put_put_same. admit.
                * admit.
            - admit.
          }
      + admit.
    - (* exec.store *)
      admit.
    - (* exec.stackalloc *)
      rename H1 into IH.
      unfold save_res_reg, res_reg, stack_loc.
      destr (Z.leb 32 x).
      + eapply exec.stackalloc. 1: assumption.
        intros. eapply seq_cps. eapply exec.store.
        * rewrite map.get_put_diff by discriminate.
          match goal with
          | |- _ = ?opt => unify opt (Some fpval)
          end.
          admit. (* ok *)
        * rewrite map.get_put_same. reflexivity.
        * unfold Memory.store, Memory.store_Z, Memory.store_bytes.
          destruct_one_match. 2: admit. (* shouldn't happen *)
          reflexivity.
        * eapply exec.weaken. {
            pose (fun m => (Memory.unchecked_store_bytes (Memory.bytes_per Syntax.access_size.word) m
                      (word.add fpval (word.of_Z ((x - 32) * bytes_per_word)))
            (LittleEndian.split (@Memory.bytes_per width Syntax.access_size.word) (word.unsigned a)))) as upd.
            match goal with
            | |- exec _ _ _ ?M _ _ _ => change M with (upd mCombined)
            end.
            rename mStack0 into mStackHL.
            (* mStack is our stack memory used for spilling, while mStackHL is allocated by this
               SStackalloc and exposed as memory to the source program *)
            eapply IH with (mCombined := map.putmany mSmall mStackHL) (frame := frame)
                           (post2 := fun '(t', m', l', mc') =>
                                       exists mSmall' mStack',
                                         Memory.anybytes a n mStack' /\ map.split m' mSmall' mStack' /\
                                         post1 (t', mSmall', l', mc')).
            1: eassumption.
            1: eapply split_stackalloc_1; eassumption.
            1: reflexivity.
            1: eassumption.
            (* existentials to pick to satisfy relation before invoking IH *)
            eexists fpval, a, tmp2val, (upd mL), (upd mStack), (map.put lStack x a), lRegs.
            ssplit.
            1: reflexivity.
            1: {
              eapply split_stackalloc_2 with (m3 := upd m2). 1,2: admit. (* ok *)
            }
            1: admit. (* ok *)
            1: eassumption.
            1: eapply map__dom_in_put; [assumption|blia].
            1: admit. (* ok *)
            1: admit. (* ok *)
            1: admit. (* ok *)
          }
          simpl. intros. simp.
          exists (map.putmany mSmall' mL0), mStack'.
          repeat match goal with
                 | |- exists (_: FlatImp.SimState _), _ => refine (ex_intro _ (_, _, _, _) _)
                 | |- exists _, _ => eexists
                 | |- _ /\ _ => split
                 end.
          11: eassumption.
          1: eassumption.
          1: eapply split_stackalloc_2; eassumption.
          1: reflexivity.
          1: {
            match goal with
            | |- map.split _ _ ?M => unify M mL0
            end.
            eapply split_stackalloc_1; eassumption.
          }
          1: eassumption.
          5: eassumption.
          all: try eassumption.
      + admit. (* same but without spilling *)
    - (* exec.lit *)
      admit.
    - (* exec.op *)
      admit.
    - (* exec.set *)
      admit.
    - (* exec.if_true *)
      unfold prepare_bcond. destruct cond.
      + simpl. eapply seq_cps. eapply seq_cps. simpl in *. simp.
        unfold load_arg_reg1, arg_reg1, load_arg_reg2, arg_reg2, save_res_reg, res_reg, stack_loc.
        destr (Z.leb 32 x).
        * match goal with
          | H: spilled_vars _ _ _ _ |- _ => pose proof H as A
          end.
          unfold spilled_vars in A.
          assert (32 <= x <= maxvar) as B by blia.
          specialize A with (1 := B); clear B. simp.
          eapply exec.load with (addr := fpval).
          { admit. }
          {


            Search Memory.load map.split.

exact Al. eassumption. }

            match goal with
          | H: spilled_vars _ _ _ _ |- _ => pose proof H as A
          end.
          unfold spilled_vars in A.
          assert (32 <= a <= maxvar) as B by blia. specialize A with (1 := B); clear B. simp.
          eapply exec.load with (addr0 := fpval) (v1 := v0).
        * admit. (* ok *)


    - (* exec.if_false *)
    - (* exec.loop *)
    - (* exec.seq *)
    - (* exec.skip *)
*)


  Abort.

End Spilling.
