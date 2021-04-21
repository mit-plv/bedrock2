Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Map.SeparationLogic.
Require Import compiler.FlatImp.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.ParamRecords.
Require Import coqutil.Tactics.simpl_rewrite.
Require Import coqutil.Datatypes.PropSet.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Utility.Utility.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.Simp.
Require Import compiler.Simulation.
Require Import compiler.SeparationLogic.
Require Import compiler.SpillingMapGoals.
Require Import bedrock2.MetricLogging.

Open Scope Z_scope.

Ltac specialize_rec H :=
  lazymatch type of H with
  | ?P -> ?Q => let F := fresh in assert P as F; [clear H|specialize (H F); clear F; specialize_rec H]
  | forall (x: ?T), _ => let n := fresh x in evar (n: T); specialize (H n); subst n; specialize_rec H
  | _ => idtac
  end.

Tactic Notation "spec" constr(t) "as" ident(H) := pose proof t as H; specialize_rec H.

Lemma sumbool_of_BoolSpec: forall {P Q: Prop} {b: bool},
    BoolSpec P Q b -> {P} + {Q}.
Proof.
  intros. destruct b.
  - left. inversion H. assumption.
  - right. inversion H. assumption.
Defined.

Lemma sumbool_of_EqDecider{T: Type}{d: T -> T -> bool}:
  EqDecider d ->
  forall x y: T, {x = y} + {x <> y}.
Proof. intros. eapply sumbool_of_BoolSpec. apply H. Qed.

Module map.
  Section MAP.
    Context {key value} {map : map.map key value}.
    Context {ok : map.ok map} {key_eqb: key -> key -> bool} {key_eq_dec : EqDecider key_eqb}.
    Implicit Types (k : key) (v : value) (x y z m : map).

    (* Note: there's already one in coqutil that requires disjointness *)
    Lemma putmany_assoc x y z : map.putmany x (map.putmany y z) = map.putmany (map.putmany x y) z.
    Proof.
      intros; eapply map.map_ext; intros.
      rewrite ?map.get_putmany_dec.
      destruct (map.get x k); destruct (map.get y k); destruct (map.get z k); reflexivity.
    Qed.

    Lemma put_idemp: forall (m: map) k v,
        map.get m k = Some v ->
        map.put m k v = m.
    Proof.
      intros. apply map.map_ext. intros. rewrite map.get_put_dec. destr (key_eqb k k0); congruence.
    Qed.

    (* to get stronger guarantees such as indexing into vs, we'd need NoDup *)
    Lemma putmany_of_list_zip_get: forall (ks: list key) (vs: list value) m0 m k,
        map.putmany_of_list_zip ks vs m0 = Some m ->
        In k ks ->
        map.get m k <> None.
    Proof.
      induction ks as [|k ks]; intros.
      - simpl in H0. destruct H0.
      - simpl in H0. destruct H0.
        + subst k0. cbn in H. simp. intro C.
          eapply map.putmany_of_list_zip_to_putmany in H.
          destruct H as (M & A & B). subst m.
          rewrite map.get_putmany_dec in C. rewrite map.get_put_same in C.
          destruct_one_match_hyp; discriminate.
        + cbn in H. simp. eapply IHks; eauto.
    Qed.

    Lemma split_remove_put: forall m m1 m2 k v,
        map.split m m1 m2 ->
        map.get m k = Some v ->
        map.split m (map.remove m1 k) (map.put m2 k v).
    Proof.
      intros.
      destruct (map.get_split k _ _ _ H) as [(A & B) | (A & B)].
      - eapply map.split_put_l2r.
        + apply map.get_remove_same.
        + replace (map.put (map.remove m1 k) k v) with m1. 1: assumption.
          apply map.map_ext.
          intro x.
          rewrite map.get_put_dec.
          destruct_one_match.
          * subst x. congruence.
          * rewrite map.get_remove_diff by congruence. reflexivity.
      - replace (map.remove m1 k) with m1. 2: {
          eapply map.map_ext. intro x. rewrite map.get_remove_dec.
          destruct_one_match.
          - subst x. assumption.
          - reflexivity.
        }
        replace (map.put m2 k v) with m2. 2: {
          apply map.map_ext. intro x. rewrite map.get_put_dec.
          destruct_one_match.
          - subst x. congruence.
          - reflexivity.
        }
        assumption.
    Qed.

    Lemma getmany_of_list_to_split: forall m (ks: list key) (vs: list value),
        map.getmany_of_list m ks = Some vs ->
        exists mrest mks, map.of_list_zip ks vs = Some mks /\ map.split m mrest mks.
    Proof.
      induction ks as [|k ks]; intros; destruct vs as [|v vs].
      - do 2 eexists. split. 1: reflexivity. unfold map.split. rewrite map.putmany_empty_r.
        split. 1: reflexivity. apply map.disjoint_empty_r.
      - discriminate.
      - cbn in H. simp. destruct_one_match_hyp; discriminate.
      - cbn in H. simp. specialize (IHks _ E0). simp. cbn.
        unfold map.of_list_zip in *.
        exists (map.remove mrest k), (map.put mks k v). split.
        + destr (map.putmany_of_list_zip ks vs (map.put map.empty k v)). 2: {
            pose proof map.putmany_of_list_zip_sameLength _ _ _ _ IHksp0 as C.
            eapply map.sameLength_putmany_of_list in C. destruct C as [a C].
            rewrite E1 in C. discriminate.
          }
          f_equal.
          eapply map.map_ext.
          intro x.
          eapply map.putmany_of_list_zip_to_putmany in E1.
          destruct E1 as (mks' & F & G).
          subst r.
          rewrite IHksp0 in F. apply Option.eq_of_eq_Some in F. subst mks'.
          rewrite map.get_putmany_dec.
          rewrite !map.get_put_dec.
          rewrite map.get_empty.
          destr (key_eqb k x). 2: destruct_one_match; reflexivity.
          subst x.
          destruct_one_match. 2: reflexivity.
          unfold map.split in IHksp1. simp.
          rewrite map.get_putmany_dec in E.
          rewrite E1 in E.
          assumption.
        + eapply split_remove_put; assumption.
    Qed.

    Lemma two_way_split: forall (m mA mB m1 m2: map),
        map.split m mA mB ->
        map.split m m1 m2 ->
        exists mA1 mA2 mB1 mB2,
          map.split mA mA1 mA2 /\
          map.split mB mB1 mB2 /\
          map.split m1 mA1 mB1 /\
          map.split m2 mA2 mB2.
    Abort.

    Lemma getmany_of_list_zip_shrink: forall (m m1 m2: map) (ks: list key) (vs: list value),
        map.split m m1 m2 ->
        map.getmany_of_list m ks = Some vs ->
        (forall k, In k ks -> map.get m2 k = None) ->
        map.getmany_of_list m1 ks = Some vs.
    Admitted.

    Lemma getmany_of_list_zip_grow: forall (m m1 m2: map) (ks: list key) (vs: list value),
        map.split m m1 m2 ->
        map.getmany_of_list m1 ks = Some vs ->
        map.getmany_of_list m ks = Some vs.
    Admitted.

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

    Lemma get_split_l: forall m m1 m2 k v,
        map.split m m1 m2 ->
        map.get m2 k = None ->
        map.get m k = Some v ->
        map.get m1 k = Some v.
    Proof.
      intros. unfold map.split, map.disjoint in *. simp.
      rewrite map.get_putmany_dec in H1.
      destruct_one_match_hyp; congruence.
    Qed.

    Lemma get_split_r: forall m m1 m2 k v,
        map.split m m1 m2 ->
        map.get m1 k = None ->
        map.get m k = Some v ->
        map.get m2 k = Some v.
    Proof.
      intros. unfold map.split, map.disjoint in *. simp.
      rewrite map.get_putmany_dec in H1.
      destruct_one_match_hyp; congruence.
    Qed.

    Lemma get_split_grow_l: forall m m1 m2 k v,
        map.split m m1 m2 ->
        map.get m2 k = Some v ->
        map.get m k = Some v.
    Proof.
      intros. unfold map.split, map.disjoint in *. simp.
      rewrite map.get_putmany_dec.
      destruct_one_match; firstorder congruence.
    Qed.

    Lemma get_split_grow_r: forall m m1 m2 k v,
        map.split m m1 m2 ->
        map.get m1 k = Some v ->
        map.get m k = Some v.
    Proof.
      intros. unfold map.split, map.disjoint in *. simp.
      rewrite map.get_putmany_dec.
      destruct_one_match; firstorder congruence.
    Qed.

    Lemma shrink_disjoint_l: forall m1 m2 m1' mRest,
        map.disjoint m1 m2 ->
        map.split m1 m1' mRest ->
        map.disjoint m1' m2.
    Proof.
      unfold map.split, map.disjoint. intros. destruct H0. subst.
      specialize H with (2 := H2). specialize H3 with (1 := H1).
      rewrite map.get_putmany_dec in H.
      destruct (map.get mRest k); eauto.
    Qed.

    Lemma shrink_disjoint_r: forall m1 m2 m2' mRest,
        map.disjoint m1 m2 ->
        map.split m2 m2' mRest ->
        map.disjoint m1 m2'.
    Proof.
      unfold map.split, map.disjoint. intros. destruct H0. subst.
      specialize H with (1 := H1). specialize H3 with (1 := H2).
      rewrite map.get_putmany_dec in H.
      destruct (map.get mRest k); eauto.
    Qed.

  End MAP.
End map.

Section MoreSepLog.
  Context {key value} {map : map.map key value}.
  Context {ok : map.ok map} {key_eqb: key -> key -> bool} {key_eq_dec : EqDecider key_eqb}.

  Lemma subst_split: forall (m m1 m2 M: map) (R: map -> Prop),
      map.split m m1 m2 ->
      (eq m * R)%sep M ->
      (eq m1 * eq m2 * R)%sep M.
  Proof.
    (* FIRSTORDER? *)
    intros.
    unfold map.split in H. simp.
    use_sep_assumption.
    cancel.
    cbn [seps].
    intro m. unfold sep, map.split. split; intros.
    - subst. eauto 10.
    - simp. reflexivity.
  Qed.

  Lemma eq_sep_to_split: forall (m m1: map) P,
      (eq m1 * P)%sep m ->
      exists m2, map.split m m1 m2 /\ P m2.
  Proof. unfold sep. intros. simp. eauto. Qed.

  Lemma sep_put_iff: forall (m: map) P R k v_old v_new,
      (ptsto k v_old * R)%sep m ->
      iff1 P (ptsto k v_new * R)%sep ->
      P (map.put m k v_new).
  Proof.
    intros.
    eapply sep_put in H.
    seprewrite H0.
    ecancel_assumption.
  Qed.

  Lemma sep_eq_put: forall (m1 m: map) P x v,
      (eq m1 * P)%sep m ->
      (forall m' w, P m' -> map.get m' x = Some w -> False) ->
      (eq (map.put m1 x v) * P)%sep (map.put m x v).
  Proof.
    intros. unfold sep, map.split in *. simp.
    exists (map.put mp x v), mq.
    specialize H0 with (1 := Hp2).
    repeat split; trivial.
    - apply map.map_ext.
      intro y.
      rewrite map.get_put_dec.
      rewrite ?map.get_putmany_dec.
      destr (map.get mq y).
      + destruct_one_match.
        * subst. exfalso. eauto.
        * reflexivity.
      + destruct_one_match.
        * subst. rewrite map.get_put_same. reflexivity.
        * rewrite map.get_put_diff by congruence. reflexivity.
    - unfold map.disjoint in *. intros.
      rewrite map.get_put_dec in H. destruct_one_match_hyp.
      + subst. eauto.
      + eauto.
  Qed.

  Lemma grow_eq_sep: forall (M M' m mAdd: map) (R: map -> Prop),
      (eq m * R)%sep M ->
      map.split M' M mAdd ->
      (eq (map.putmany m mAdd) * R)%sep M'.
  Proof.
    intros. apply sep_comm. apply sep_comm in H.
    unfold sep, map.split in *. simp.
    do 2 eexists. ssplit. 4: reflexivity. 3: eassumption.
    - symmetry. apply map.putmany_assoc.
    - unfold map.disjoint in *. intros. rewrite map.get_putmany_dec in H0.
      destruct_one_match_hyp.
      + simp. eapply H0p1. 2: eassumption. rewrite map.get_putmany_dec.
        rewrite H. instantiate (1 := ltac:(destruct(map.get mq k))).
        destruct (map.get mq k); reflexivity.
      + eauto.
  Qed.

  Lemma join_sep: forall (m m1 m2: map) (P P1 P2: map -> Prop),
      map.split m m1 m2 ->
      P1 m1->
      P2 m2 ->
      iff1 (P1 * P2)%sep P ->
      P m.
  Proof.
    unfold sep, map.split. intros. simp. eapply H2. eauto 10.
  Qed.

End MoreSepLog.

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

  Definition arg_reg(i r: Z): Z := if Z.leb 32 r then 2 + i else r.
  Definition res_reg(r: Z): Z := if Z.leb 32 r then tmp1 else r.

  (* i needs to be 1 or 2, r any register > fp *)
  Definition load_arg_reg(i r: Z): stmt :=
    match stack_loc r with
    | Some o => SLoad Syntax.access_size.word (2 + i) fp o
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
    | CondBinary _ x y => load_arg_reg 1 x;; load_arg_reg 2 y
    | CondNez x => load_arg_reg 1 x
    end.

  Definition spill_bcond(c: bcond Z): bcond Z :=
    match c with
    | CondBinary op x y => CondBinary op (arg_reg 1 x) (arg_reg 2 y)
    | CondNez x => CondNez (arg_reg 1 x)
    end.

  Fixpoint spill_stmt(s: stmt): stmt :=
    match s with
    | SLoad sz x y o =>
      load_arg_reg 1 y;;
      SLoad sz (res_reg x) (arg_reg 1 y) o;;
      save_res_reg x
    | SStore sz x y o =>
      load_arg_reg 1 x;; load_arg_reg 2 y;;
      SStore sz (arg_reg 1 x) (arg_reg 2 y) o
    | SInlinetable sz x t i =>
      load_arg_reg 2 i;;
      SInlinetable sz (res_reg x) t (arg_reg 2 i);;
      save_res_reg x
    | SStackalloc x n body =>
      SStackalloc (res_reg x) n (save_res_reg x;; spill_stmt body)
    | SLit x n =>
      SLit (res_reg x) n;;
      save_res_reg x
    | SOp x op y z =>
      load_arg_reg 1 y;; load_arg_reg 2 z;;
      SOp (res_reg x) op (arg_reg 1 y) (arg_reg 2 z);;
      save_res_reg x
    | SSet x y => (* TODO could be optimized if exactly one is on the stack *)
      load_arg_reg 1 y;;
      SSet (res_reg x) (arg_reg 1 y);;
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
    | SLoad _ x y _ | SStore _ x y _ | SInlinetable _ x _ y | SSet x y => Z.max x y
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
    SStackalloc fp (bytes_per_word * (max_var s - 31)) (spill_stmt s).

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
    (* Without the clear, firstorder becomes very slow COQBUG https://github.com/coq/coq/issues/11352.
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
             | |- _ => progress unfold tmp1, tmp2, sp, fp, res_reg, arg_reg, arg_reg, res_reg,
                         spill_bcond, max_var_bcond, ForallVars_bcond, prepare_bcond,
                         load_arg_reg, load_arg_reg, save_res_reg, stack_loc in *
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

  Definition tmps(l: locals): Prop :=
    forall k v, map.get l k = Some v -> k = tmp1 \/ k = tmp2.

  Definition related(maxvar: Z)(frame: mem -> Prop)(done: bool)
             (t1: trace)(m1: mem)(l1: locals)(mc1: MetricLog)
             (t2: trace)(m2: mem)(l2: locals)(mc2: MetricLog): Prop :=
      exists fpval lStack lRegs stackwords,
        t1 = t2 /\
        (eq m1 * word_array fpval stackwords * frame)%sep m2 /\
        (forall x v, map.get lRegs x = Some v -> fp < x < 32) /\
        (forall x v, map.get lStack x = Some v -> 32 <= x <= maxvar) /\
        (eq lRegs * eq lStack)%sep l1 /\
        (eq lRegs * tmps * ptsto fp fpval)%sep l2 /\
        (forall r, 32 <= r <= maxvar -> forall v, map.get lStack r = Some v ->
           nth_error stackwords (Z.to_nat (r - 32)) = Some v) /\
        length stackwords = Z.to_nat (maxvar - 31).

  Lemma load_from_word_array: forall p words frame m i v,
      (word_array p words * frame)%sep m ->
      nth_error words (Z.to_nat i) = Some v ->
      Memory.load Syntax.access_size.word m (word.add p (word.of_Z (i * bytes_per_word))) = Some v.
  Admitted.

  Lemma store_to_word_array: forall p oldwords frame m i v,
      (word_array p oldwords * frame)%sep m ->
      0 <= i < Z.of_nat (List.length oldwords) ->
      exists m' newwords,
        Memory.store Syntax.access_size.word m (word.add p (word.of_Z (i * bytes_per_word))) v = Some m' /\
        (word_array p newwords * frame)%sep m' /\
        nth_error newwords (Z.to_nat i) = Some v /\
        (forall j w, j <> Z.to_nat i -> nth_error oldwords j = Some w -> nth_error newwords j = Some w) /\
        length newwords = length oldwords.
  Admitted.

  Lemma store_bytes_sep_hi2lo: forall (mH mL : mem) R a n v_old v,
      Memory.load_bytes n mH a = Some v_old ->
      (eq mH * R)%sep mL ->
      (eq (Memory.unchecked_store_bytes n mH a v) * R)%sep (Memory.unchecked_store_bytes n mL a v).
  Proof.
    intros. simpl_param_projections. apply sep_comm. apply sep_comm in H0.
    unfold Memory.load_bytes, Memory.unchecked_store_bytes, sep, map.split in *.
    simp. do 2 eexists. ssplit. 3: eassumption. 3: reflexivity.
    - rewrite map.putmany_of_tuple_to_putmany.
      rewrite (map.putmany_of_tuple_to_putmany _ mq).
      symmetry. apply map.putmany_assoc.
    - unfold map.disjoint in *.
      intros.
      pose proof (map.putmany_of_tuple_preserves_domain (ok := mem_ok) _ _ v_old v _ H) as A.
      unfold map.same_domain, map.sub_domain in A. apply proj2 in A.
      edestruct A as [v3 B]. 1: eassumption.
      eauto.
  Qed.

  Definition envs_related(e1 e2: env): Prop :=
    forall f argvars resvars body1,
      map.get e1 f = Some (argvars, resvars, body1) ->
      map.get e2 f = Some (argvars, resvars, spill_fbody body1) /\
      Forall (fun x => fp < x < 32) argvars /\
      Forall (fun x => fp < x < 32) resvars /\
      (* upper bound always holds, but we still need to check lower bound: *)
      valid_vars_src (max_var body1) body1.

  Lemma seq_cps: forall e s1 s2 t m l mc post,
      exec e s1 t m l mc (fun t' m' l' mc' => exec e s2 t' m' l' mc' post) ->
      exec e (SSeq s1 s2) t m l mc post.
  Proof.
    intros. eapply exec.seq. 1: eassumption. simpl. clear. auto.
  Qed.

  Lemma sep_def: forall {m: mem} {P Q: mem -> Prop},
      (P * Q)%sep m ->
      exists m1 m2, map.split m m1 m2 /\ P m1 /\ Q m2.
  Proof. unfold sep. intros *. apply id. Qed.

  Implicit Types post : trace -> mem -> locals -> MetricLog -> Prop.

  Lemma put_tmp: forall l i v fpval lRegs,
      (eq lRegs * tmps * ptsto fp fpval)%sep l ->
      i = 1 \/ i = 2 ->
      (forall x v, map.get lRegs x = Some v -> fp < x < 32) ->
      (eq lRegs * tmps * ptsto fp fpval)%sep (map.put l (2 + i) v).
  Proof.
    intros.
    assert (((eq lRegs * ptsto fp fpval) * tmps)%sep l) as A by ecancel_assumption. clear H.
    enough (((eq lRegs * ptsto fp fpval) * tmps)%sep (map.put l (2 + i) v)). 1: ecancel_assumption.
    unfold sep at 1. unfold sep at 1 in A. simp.
    unfold tmps in *.
    unfold map.split.
    unfold map.split in Ap0. simp.
    exists mp, (map.put mq (2 + i) v). ssplit.
    - apply map.put_putmany_commute.
    - unfold sep, map.split in Ap1. simp. unfold map.disjoint in *.
      intros. rewrite map.get_put_dec in H2. rewrite map.get_putmany_dec in H.
      unfold ptsto in *. subst.
      setoid_rewrite map.get_put_dec in Ap1p0p1. setoid_rewrite map.get_empty in Ap1p0p1.
      setoid_rewrite <- map.put_putmany_commute in Ap0p1.
      setoid_rewrite map.putmany_empty_r in Ap0p1.
      setoid_rewrite map.get_put_dec in Ap0p1.
      rewrite map.get_put_dec in H. rewrite map.get_empty in H. unfold fp in *.
      destruct_one_match_hyp; simp; subst; destruct_one_match_hyp; simp; subst.
      + apply Z.eqb_eq in E0. blia.
      + specialize H1 with (1 := H). blia.
      + eapply Ap0p1. 2: exact H2. rewrite E1. reflexivity.
      + specialize Ap0p1 with (2 := H2). rewrite E1 in Ap0p1. eauto.
    - assumption.
    - intros. rewrite map.get_put_dec in H. unfold tmp1, tmp2.
      destruct_one_match_hyp.
      + blia.
      + eauto.
  Qed.

  Lemma load_arg_reg_correct(i: Z): forall r e2 t1 t2 m1 m2 l1 l2 mc1 mc2 post frame maxvar v,
      i = 1 \/ i = 2 ->
      related maxvar frame false t1 m1 l1 mc1 t2 m2 l2 mc2 ->
      fp < r <= maxvar ->
      map.get l1 r = Some v ->
      (forall mc2,
          related maxvar frame false t1 m1 l1 mc1 t2 m2 (map.put l2 (arg_reg i r) v) mc2 ->
          post t2 m2 (map.put l2 (arg_reg i r) v) mc2) ->
      exec e2 (load_arg_reg i r) t2 m2 l2 mc2 post.
  Proof.
    intros.
    unfold load_arg_reg, stack_loc, arg_reg, related in *. simp.
    destr (32 <=? r).
    - eapply exec.load.
      + eapply get_sep. simpl_param_projections. ecancel_assumption.
      + eapply load_from_word_array. 1: ecancel_assumption.
        eapply H0p5. 1: blia.
        unfold sep in H0p3. simp.
        eapply map.get_split_r. 1,3: eassumption.
        destr (map.get mp r); [exfalso|reflexivity].
        specialize H0p1 with (1 := E0). blia.
      + eapply H3.
        repeat match goal with
               | |- exists _, _ => eexists
               | |- _ /\ _ => split
               | |- _ => eassumption || reflexivity
               end.
        eapply put_tmp; eassumption.
    - eapply exec.skip.
      replace l2 with (map.put l2 r v) in H0p4|-*. 2: {
        apply map.put_idemp.
        edestruct (eq_sep_to_split l2) as (l2Rest & S22 & SP22). 1: ecancel_assumption.
        eapply map.get_split_grow_r. 1: eassumption.
        unfold sep in H0p3. destruct H0p3 as (lRegs' & lStack' & S2 & ? & ?). subst lRegs' lStack'.
        eapply map.get_split_l. 1: exact S2. 2: assumption.
        destr (map.get lStack r); [exfalso|reflexivity].
        specialize H0p2 with (1 := E0). blia.
      }
      eapply H3.
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             | |- _ => eassumption || reflexivity
             end.
  Qed.

  Lemma load_arg_reg_correct'(i: Z): forall r e2 t1 t2 m1 m2 l1 l2 mc1 mc2 post frame maxvar v,
      i = 1 \/ i = 2 ->
      related maxvar frame false t1 m1 l1 mc1 t2 m2 l2 mc2 ->
      fp < r <= maxvar ->
      map.get l1 r = Some v ->
      post t1 m1 l1 mc1 ->
      exec e2 (load_arg_reg i r) t2 m2 l2 mc2
           (fun t2' m2' l2' mc2' => exists t1' m1' l1' mc1',
                related maxvar frame false t1' m1' l1' mc1' t2' m2' l2' mc2' /\ post t1' m1' l1' mc1').
  Proof.
    intros.
    unfold load_arg_reg, stack_loc, arg_reg, related in *. simp.
    destr (32 <=? r).
    - eapply exec.load.
      + eapply get_sep. simpl_param_projections. ecancel_assumption.
      + eapply load_from_word_array. 1: ecancel_assumption.
        eapply H0p5. 1: blia.
        unfold sep in H0p3. simp.
        eapply map.get_split_r. 1,3: eassumption.
        destr (map.get mp r); [exfalso|reflexivity].
        specialize H0p1 with (1 := E0). blia.
      + repeat match goal with
               | |- exists _, _ => eexists
               | |- _ /\ _ => split
               | |- _ => eassumption || reflexivity
               end.
        eapply put_tmp; eassumption.
    - eapply exec.skip.
      replace l2 with (map.put l2 r v) in H0p4|-*. 2: {
        apply map.put_idemp.
        edestruct (eq_sep_to_split l2) as (l2Rest & S22 & SP22). 1: ecancel_assumption.
        eapply map.get_split_grow_r. 1: eassumption.
        unfold sep in H0p3. destruct H0p3 as (lRegs' & lStack' & S2 & ? & ?). subst lRegs' lStack'.
        eapply map.get_split_l. 1: exact S2. 2: assumption.
        destr (map.get lStack r); [exfalso|reflexivity].
        specialize H0p2 with (1 := E0). blia.
      }
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             | |- _ => eassumption || reflexivity
             end.
  Qed.

  (* Note: if we wanted to use this lemma in subgoals created by exec.loop,
     new postcondition must not mention the original t2, m2, l2, mc2, (even though
     it would be handy to just say t2'=t2, m2=m2', l2' = map.put l2 (arg_reg i r) v), because
     when the new postcondition is used as a "mid1" in exec.loop, and body1 is a seq
     in which this lemma was used, t2, m2, l2, mc2 are introduced after the evar "?mid1"
     is created (i.e. after exec.loop is applied), so they are not in the scope of "?mid1". *)
  Lemma load_arg_reg_correct''(i: Z): forall r e2 t1 t2 m1 m2 l1 l2 mc1 mc2 frame maxvar v,
      i = 1 \/ i = 2 ->
      related maxvar frame false t1 m1 l1 mc1 t2 m2 l2 mc2 ->
      fp < r <= maxvar ->
      map.get l1 r = Some v ->
      exec e2 (load_arg_reg i r) t2 m2 l2 mc2 (fun t2' m2' l2' mc2' =>
        t2' = t2 /\ m2' = m2 /\ l2' = map.put l2 (arg_reg i r) v /\
        related maxvar frame false t1 m1 l1 mc1 t2' m2' l2' mc2').
  Proof.
    intros.
    unfold load_arg_reg, stack_loc, arg_reg, related in *. simp.
    destr (32 <=? r).
    - eapply exec.load.
      + eapply get_sep. simpl_param_projections. ecancel_assumption.
      + eapply load_from_word_array. 1: ecancel_assumption.
        eapply H0p5. 1: blia.
        unfold sep in H0p3. simp.
        eapply map.get_split_r. 1,3: eassumption.
        destr (map.get mp r); [exfalso|reflexivity].
        specialize H0p1 with (1 := E0). blia.
      + repeat match goal with
               | |- exists _, _ => eexists
               | |- _ /\ _ => split
               | |- _ => eassumption || reflexivity
               end.
        eapply put_tmp; eassumption.
    - eapply exec.skip.
      assert (l2 = map.put l2 r v) as F. {
        symmetry. apply map.put_idemp.
        edestruct (eq_sep_to_split l2) as (l2Rest & S22 & SP22). 1: ecancel_assumption.
        eapply map.get_split_grow_r. 1: eassumption.
        unfold sep in H0p3. destruct H0p3 as (lRegs' & lStack' & S2 & ? & ?). subst lRegs' lStack'.
        eapply map.get_split_l. 1: exact S2. 2: assumption.
        destr (map.get lStack r); [exfalso|reflexivity].
        specialize H0p2 with (1 := E0). blia.
      }
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             | |- _ => eassumption || reflexivity
             end.
  Qed.

  Lemma loop_cps: forall e body1 cond body2 t m l mc post,
    exec e body1 t m l mc (fun t m l mc => exists b,
      eval_bcond l cond = Some b /\
      (b = false -> post t m l (addMetricLoads 1 (addMetricInstructions 1 (addMetricJumps 1 mc)))) /\
      (b = true -> exec e body2 t m l mc (fun t m l mc =>
         exec e (SLoop body1 cond body2) t m l
              (addMetricLoads 2 (addMetricInstructions 2 (addMetricJumps 1 mc))) post))) ->
    exec e (SLoop body1 cond body2) t m l mc post.
  Proof.
    intros. eapply exec.loop. 1: eapply H. all: cbv beta; intros; simp.
    - congruence.
    - replace b with false in * by congruence. clear b. eauto.
    - replace b with true in * by congruence. clear b. eauto.
    - assumption.
  Qed.

  (* SOp does not create an up-to-date `related` before we invoke this one, because after SOp,
     `related` does not hold: the result is already in l1 and lStack, but not yet in stackwords.
     So we request the `related` that held *before* SOp, i.e. the one where the result is not
     yet in l1 and l2. *)
  Lemma save_res_reg_correct: forall e t1 t2 m1 m2 l1 l2 mc1 mc1b mc2 mc2b x v maxvar frame post,
      post t1 m1 (map.put l1 x v) mc1 ->
      related maxvar frame false t1 m1 l1 mc1b t2 m2 l2 mc2b ->
      fp < x <= maxvar ->
      exec e (save_res_reg x) t2 m2 (map.put l2 (res_reg x) v) mc2
           (fun t2' m2' l2' mc2' => exists t1' m1' l1' mc1',
                related maxvar frame false t1' m1' l1' mc1' t2' m2' l2' mc2' /\ post t1' m1' l1' mc1').
  Proof.
    intros.
    unfold save_res_reg, stack_loc, res_reg, related in *. simp.
    destr (32 <=? x).
    - edestruct store_to_word_array as (m' & stackwords' & St & S' & Ni & Nj & L).
      1: ecancel_assumption.
      2: {
        eapply exec.store.
        - rewrite map.get_put_diff by (cbv; congruence).
          eapply get_sep. simpl_param_projections. ecancel_assumption.
        - rewrite map.get_put_same. reflexivity.
        - exact St.
        - repeat match goal with
                 | |- exists _, _ => eexists
                 | |- _ /\ _ => split
                 end.
          1: reflexivity.
          8: eassumption.
          1: ecancel_assumption.
          3: {
            unfold sep, map.split in H0p3|-*.
            destruct H0p3 as (lRegs' & lStack' & (? & D) & ? & ?). subst lRegs' lStack' l1.
            exists lRegs, (map.put lStack x v).
            repeat split.
            - apply map.put_putmany_commute.
            - unfold map.disjoint. intros.
              specialize H0p1 with (1 := H0).
              rewrite map.get_put_dec in H1. destr (x =? k).
              + subst x. blia.
              + specialize H0p2 with (1 := H1). blia.
          }
          1: eassumption.
          1: {
            intros. rewrite map.get_put_dec in H0. destr (x =? x0).
            - subst x0. blia.
            - eauto.
          }
          2: {
            intros.
            intros. rewrite map.get_put_dec in H1. destr (x =? r).
            - apply Option.eq_of_eq_Some in H1. subst. assumption.
            - eapply Nj. 1: blia. eauto.
          }
          1: { change tmp1 with (2 + 1). eapply put_tmp; eauto. }
          blia.
      }
      blia.
    - eapply exec.skip.
      (* even though we did nothing, we have to reconstruct the `related` from the `related` that
         held *before* the SOp *)
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             end.
      1: reflexivity.
      8: eassumption.
      1: ecancel_assumption.
      3: {
        apply sep_comm. apply sep_comm in H0p3.
        unfold sep, map.split in H0p3|-*.
        destruct H0p3 as (lRegs' & lStack' & (? & D) & ? & ?). subst lRegs' lStack' l1.
        exists lStack, (map.put lRegs x v).
        repeat split.
        - apply map.put_putmany_commute.
        - unfold map.disjoint. intros.
          specialize H0p2 with (1 := H0).
          rewrite map.get_put_dec in H1. destr (x =? k).
          + subst x. blia.
          + specialize H0p1 with (1 := H1). blia.
      }
      1: {
        intros. rewrite map.get_put_dec in H0. destr (x =? x0).
        - subst x0. blia.
        - eauto.
      }
      2: {
        spec (sep_eq_put lRegs l2) as A. 1,3: ecancel_assumption.
        clear -localsOk H1p0.
        unfold tmps, sep, map.split, tmp1, tmp2, fp in *.
        intros. simp.
        unfold ptsto, map.disjoint in *. subst.
        rewrite ?map.get_putmany_dec, ?map.get_put_dec, ?map.get_empty in H0.
        repeat destruct_one_match_hyp; subst; simp; try congruence; try blia.
        specialize Hp1 with (1 := H0). blia.
      }
      all: try eassumption.
  Qed.

  (* SOp does not create an up-to-date `related` before we invoke this one, because after SOp,
     `related` does not hold: the result is already in l1 and lStack, but not yet in stackwords.
     So we request the `related` that held *before* SOp, i.e. the one where the result is not
     yet in l1 and l2. *)
  Lemma save_res_reg_correct'': forall e t1 t2 m1 m2 l1 l2 mc1 mc1b mc2 mc2b x v maxvar frame post,
      related maxvar frame false t1 m1 l1 mc1b t2 m2 l2 mc2b ->
      fp < x <= maxvar ->
      (forall t2' m2' l2' mc2',
          related maxvar frame false t1 m1 (map.put l1 x v) mc1 t2' m2' l2' mc2' ->
          post t2' m2' l2' mc2') ->
      exec e (save_res_reg x) t2 m2 (map.put l2 (res_reg x) v) mc2 post.
  Proof.
    intros.
    unfold save_res_reg, stack_loc, res_reg, related in *. simp.
    destr (32 <=? x).
    - edestruct store_to_word_array as (m' & stackwords' & St & S' & Ni & Nj & L).
      1: ecancel_assumption.
      2: {
        eapply exec.store.
        - rewrite map.get_put_diff by (cbv; congruence).
          eapply get_sep. simpl_param_projections. ecancel_assumption.
        - rewrite map.get_put_same. reflexivity.
        - exact St.
        - eapply H1.
          repeat match goal with
                 | |- exists _, _ => eexists
                 | |- _ /\ _ => split
                 end.
          1: reflexivity.
          1: ecancel_assumption.
          3: {
            unfold sep, map.split in Hp3|-*.
            destruct Hp3 as (lRegs' & lStack' & (? & D) & ? & ?). subst lRegs' lStack' l1.
            exists lRegs, (map.put lStack x v).
            repeat split.
            - apply map.put_putmany_commute.
            - unfold map.disjoint. intros.
              specialize Hp1 with (1 := H).
              rewrite map.get_put_dec in H0. destr (x =? k).
              + subst x. blia.
              + specialize Hp2 with (1 := H0). blia.
          }
          1: eassumption.
          1: {
            intros. rewrite map.get_put_dec in H. destr (x =? x0).
            - subst x0. blia.
            - eauto.
          }
          2: {
            intros.
            intros. rewrite map.get_put_dec in H0. destr (x =? r).
            - apply Option.eq_of_eq_Some in H0. subst. assumption.
            - eapply Nj. 1: blia. eauto.
          }
          1: { change tmp1 with (2 + 1). eapply put_tmp; eauto. }
          blia.
      }
      blia.
    - eapply exec.skip.
      eapply H1.
      (* even though we did nothing, we have to reconstruct the `related` from the `related` that
         held *before* the SOp *)
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             end.
      1: reflexivity.
      1: ecancel_assumption.
      3: {
        apply sep_comm. apply sep_comm in Hp3.
        unfold sep, map.split in Hp3|-*.
        destruct Hp3 as (lRegs' & lStack' & (? & D) & ? & ?). subst lRegs' lStack' l1.
        exists lStack, (map.put lRegs x v).
        repeat split.
        - apply map.put_putmany_commute.
        - unfold map.disjoint. intros.
          specialize Hp2 with (1 := H).
          rewrite map.get_put_dec in H0. destr (x =? k).
          + subst x. blia.
          + specialize Hp1 with (1 := H0). blia.
      }
      1: {
        intros. rewrite map.get_put_dec in H. destr (x =? x0).
        - subst x0. blia.
        - eauto.
      }
      2: {
        spec (sep_eq_put lRegs l2) as A. 1,3: ecancel_assumption.
        clear -localsOk H0p0.
        unfold tmps, sep, map.split, tmp1, tmp2, fp in *.
        intros. simp.
        unfold ptsto, map.disjoint in *. subst.
        rewrite ?map.get_putmany_dec, ?map.get_put_dec, ?map.get_empty in H0.
        repeat destruct_one_match_hyp; subst; simp; try congruence; try blia.
        specialize Hp1 with (1 := H0). blia.
      }
      all: try eassumption.
  Qed.

  Lemma exec_seq_assoc: forall e s1 s2 s3 t m l mc post,
      exec e (s1;; s2;; s3) t m l mc post ->
      exec e ((s1;; s2);; s3) t m l mc post.
  Proof.
    intros. simp.
    eapply seq_cps.
    eapply seq_cps.
    eapply exec.weaken. 1: eassumption. intros.
    specialize H8 with (1 := H). simp.
    eapply exec.weaken. 1: eassumption. intros.
    eauto.
  Qed.

  Lemma exec_seq_assoc_bw: forall e s1 s2 s3 t m l mc post,
      exec e ((s1;; s2);; s3) t m l mc post ->
      exec e (s1;; (s2;; s3)) t m l mc post.
  Proof. intros. simp. eauto 10 using exec.seq. Qed.

  Lemma get_arg_reg_1: forall l l2 y y' (z : Z) (z' : word),
      fp < y ->
      fp < z ->
      map.get l y = Some y' ->
      map.get l z = Some z' ->
      map.get (map.put (map.put l2 (arg_reg 1 y) y') (arg_reg 2 z) z') (arg_reg 1 y) = Some y'.
  Proof.
    intros.
    destr (y =? z).
    - subst z. replace z' with y' in * by congruence.
      unfold arg_reg. destruct_one_match.
      + rewrite map.get_put_diff by blia. rewrite map.get_put_same. reflexivity.
      + rewrite map.get_put_same. reflexivity.
    - rewrite map.get_put_diff.
      + rewrite map.get_put_same. reflexivity.
      + unfold arg_reg. unfold fp in *. repeat destruct_one_match; blia.
  Qed.

(*
  Lemma spill_bcond_correct: forall maxvar frame t1 m1 l1 mc1 t2 m2 l2 mc2 c,
      related maxvar frame false t1 m1 l1 mc1 t2 m2 l2 mc2 ->
      eval_bcond l1 c = eval_bcond l2 (spill_bcond c).
  Proof.
    unfold related. intros. destruct c; cbn; simp.
    - destr (map.get l1 x).

 destr (map.get l1 y).
*)

  Lemma grow_related_mem: forall maxvar frame t1 mSmall1 l1 mc1 t2 mSmall2 l2 mc2 mStack mCombined2,
      related maxvar frame false t1 mSmall1 l1 mc1 t2 mSmall2 l2 mc2 ->
      map.split mCombined2 mSmall2 mStack ->
      exists mCombined1, map.split mCombined1 mSmall1 mStack /\
                         related maxvar frame false t1 mCombined1 l1 mc1 t2 mCombined2 l2 mc2.
  Proof.
  Admitted.

  Lemma shrink_related_mem: forall maxvar frame t1 m1 l1 mc1 t2 m2 l2 mc2 mRemove m1Small,
      related maxvar frame false t1 m1 l1 mc1 t2 m2 l2 mc2 ->
      map.split m1 m1Small mRemove ->
      exists m2Small, map.split m2 m2Small mRemove /\
                      related maxvar frame false t1 m1Small l1 mc1 t2 m2Small l2 mc2.
  Proof.
  Admitted.

  (* TODO share with FlatToRiscvDef.compile4bytes? *)
  Fixpoint tuple__firstn{A: Type}(n: nat)(l: list A)(default: A){struct n}: HList.tuple A n :=
    match n with
    | O => tt
    | S m => PrimitivePair.pair.mk (hd default l) (tuple__firstn m (tl l) default)
    end.

  Fixpoint List__firstn_default{A: Type}(n: nat)(l: list A)(default: A): list A :=
    match n with
    | O => nil
    | S m => hd default l :: List__firstn_default m (tl l) default
    end.

  Lemma tuple__firstn_to_list{A: Type}: forall n (l: list A) default,
      HList.tuple.to_list (tuple__firstn n l default) = List__firstn_default n l default.
  Proof.
    induction n; intros.
    - reflexivity.
    - cbn. f_equal. eapply IHn.
  Qed.

  Definition head_to_Z(sz: nat)(l: list byte): Z := LittleEndian.combine sz (tuple__firstn sz l Byte.x00).

  Fixpoint byte_list_to_Z_list(sz nWords: nat)(bs: list byte): list Z :=
    match nWords with
    | S m => head_to_Z sz bs :: byte_list_to_Z_list sz m (skipn sz bs)
    | O => nil
    end.

  Definition byte_list_to_word_list(bs: list byte): list word :=
    let sz := Z.to_nat (@Memory.bytes_per_word width) in
    List.map word.of_Z (byte_list_to_Z_list sz (length bs / sz)%nat bs).

  Lemma littleendian_head_to_Z: forall n l (addr : word),
      iff1 (littleendian n addr (head_to_Z n l))
           (array ptsto (word.of_Z 1) addr (List__firstn_default n l Byte.x00)).
  Proof.
    intros. unfold littleendian, ptsto_bytes, head_to_Z.
    rewrite LittleEndian.split_combine. rewrite tuple__firstn_to_list.
    reflexivity.
  Qed.

  Lemma scalar_head_to_Z: forall l (addr : word),
      iff1 (scalar addr (word.of_Z (head_to_Z (Z.to_nat bytes_per_word) l)))
           (array ptsto (word.of_Z 1) addr (List__firstn_default (Z.to_nat bytes_per_word) l Byte.x00)).
  Proof.
    unfold scalar, truncated_word, truncated_scalar. intros. rewrite word.unsigned_of_Z. unfold word.wrap.
  Abort.

  (* byte_list_to_word_list_array already exists, TODO reconcile *)

  Lemma spilling_correct (e1 e2 : env) (Ev : envs_related e1 e2)
        (s1 : stmt)
  (t1 : trace)
  (m1 : mem)
  (l1 : locals)
  (mc1 : MetricLog)
  (post : trace -> mem -> locals -> MetricLog -> Prop):
  exec e1 s1 t1 m1 l1 mc1 post ->
  forall (frame : mem -> Prop) (maxvar : Z),
  valid_vars_src maxvar s1 ->
  forall (t2 : trace) (m2 : mem) (l2 : locals) (mc1b mc2 mc2b : MetricLog),
  related maxvar frame false t1 m1 l1 mc1b t2 m2 l2 mc2b ->
  exec e2 (spill_stmt s1) t2 m2 l2 mc2
    (fun (t2' : trace) (m2' : mem) (l2' : locals) (mc2' : MetricLog) =>
       exists t1' m1' l1' mc1',
         related maxvar frame false t1' m1' l1' mc1' t2' m2' l2' mc2' /\
         post t1' m1' l1' mc1').
  Proof.
    induction 1; intros; cbn [spill_stmt valid_vars_src Forall_vars_stmt] in *; simp.
    - (* exec.interact *)
      unfold related in *. simp.
      spec (subst_split (ok := mem_ok) m) as A.
      1: eassumption. 1: ecancel_assumption.
      edestruct (@sep_def m2 (eq mGive)) as (mGive' & mKeepL & B & ? & C); simpl_param_projections.
      1: ecancel_assumption.
      subst mGive'.
      rename H3p0 into FR, H3p1 into FA.
      unfold sep in H4p3. destruct H4p3 as (lRegs' & lStack' & S2 & ? & ?). subst lRegs' lStack'.
      spec (map.getmany_of_list_zip_shrink l) as R. 1,2: eassumption. {
        intros k HI. destr (map.get lStack k); [exfalso|reflexivity].
        specialize H4p2 with (1 := E).
        eapply Forall_forall in FA. 2: exact HI. clear -H4p2 FA. blia.
      }
      edestruct (eq_sep_to_split l2) as (l2Rest & S22 & SP22). 1: ecancel_assumption.
      eapply @exec.interact with (mGive := mGive).
      + eapply map.split_comm. exact B.
      + eapply map.getmany_of_list_zip_grow. 2: exact R. 1: exact S22.
      + eassumption.
      + intros.
        match goal with
        | H: context[outcome], A: context[outcome] |- _ =>
          specialize H with (1 := A); move H at bottom
        end.
        simp.
        rename l into l1, l' into l1'.
        pose proof H2p0 as P.
        eapply map.putmany_of_list_zip_split in P. 2: eassumption. 2: {
          eapply Forall_impl. 2: eassumption.
          simpl.
          intros.
          destr (map.get lStack a). 2: reflexivity.
          match goal with
          | H: forall _, _ |- _ => specialize H with (1 := E)
          end.
          blia.
        }
        destruct P as (lRegs' & Spl1' & P).
        pose proof P as P0.
        eapply map.putmany_of_list_zip_grow with (l := l2) in P. 2: eassumption. 2: {
          eapply Forall_impl. 2: eassumption.
          clear -localsOk SP22. unfold fp, tmps, tmp1, tmp2 in *. intros.
          unfold sep, ptsto, map.split in *. simp.
          rewrite ?map.get_putmany_dec, ?map.get_put_dec, ?map.get_empty.
          repeat destruct_one_match; try congruence; repeat destruct_one_match_hyp; try congruence; try blia.
          destr (map.get mp a). 2: reflexivity.
          specialize SP22p1 with (1 := E1). blia.
        }
        destruct P as (l2' & ? & ?).
        eexists. split. 1: eassumption.
        intros.
        repeat match goal with
               | |- exists _, _ => eexists
               | |- _ /\ _ => split
               end.
        1: reflexivity.
        8: eapply H2p1.
        6: eassumption.
        6: eassumption.
        4: solve [unfold sep; eauto].
        4: {
          enough ((eq lRegs' * (tmps * ptsto fp fpval))%sep l2') as En. 1: ecancel_assumption.
          unfold sep at 1. eauto. }
        { eenough ((eq _ * (word_array fpval stackwords * frame))%sep m') as En.
          1: ecancel_assumption.
          move C before H5.
          eapply grow_eq_sep. 1: exact C. eassumption. }
        { intros x v G.
          edestruct map.putmany_of_list_zip_find_index. 1: exact P0. 1: exact G.
          - simp. apply nth_error_In in H6p0. eapply Forall_forall in FR. 1: exact FR. assumption.
          - eauto. }
        { assumption. }
        { unfold map.split. split; [reflexivity|].
          move C at bottom. move H5 at bottom.
          unfold sep at 1 in C. destruct C as (mKeepL' & mRest & SC & ? & _). subst mKeepL'.
          unfold map.split in H5. simp.
          eapply map.shrink_disjoint_l; eassumption. }
    - (* exec.call *)
      unfold related, envs_related in *. specialize Ev with (1 := H). simp.
      rename H4p0 into FR, H4p1 into FA.
      unfold sep in H5p3. destruct H5p3 as (lRegs' & lStack' & S2 & ? & ?). subst lRegs' lStack'.
      spec (map.getmany_of_list_zip_shrink l) as R. 1,2: eassumption. {
        intros k HI. destr (map.get lStack k); [exfalso|assumption].
        specialize H5p2 with (1 := E).
        eapply Forall_forall in FA. 2: exact HI. clear -H5p2 FA. blia.
      }
      edestruct (eq_sep_to_split l2) as (l2Rest & S22 & SP22). 1: ecancel_assumption.
      eapply exec.call with (outcome0 :=
         fun t2 m2 l2 mc2 => exists t1 m1 l1 mc1, outcome t1 m1 l1 mc1 /\
                                                  related maxvar frame false t1 m1 l1 mc1 t2 m2 l2 mc2).
      + eauto.
      + eapply map.getmany_of_list_zip_grow. 2: exact R. 1: exact S22.
      + eassumption.
      + unfold spill_fbody.
        eapply exec.stackalloc. {
          rewrite Z.mul_comm.
          apply Z_mod_mult.
        }
        intros *. intros A Sp.
        destruct (anybytes_to_array_1 (mem_ok := mem_ok) _ _ _ A) as (bytes & Pt & L).
        edestruct (byte_list_to_word_list_array bytes) as (words & L' & F). {
          rewrite L.
          unfold Memory.ftprint.
          destr (0 <=? (bytes_per_word * (max_var fbody - 31))).
          - rewrite Z2Nat.id by assumption. rewrite Z.mul_comm. apply Z_mod_mult.
          - replace (Z.of_nat (Z.to_nat (bytes_per_word * (max_var fbody - 31)))) with 0 by blia.
            apply Zmod_0_l.
        }
        eapply F in Pt.
        eapply exec.weaken. {
          eapply IHexec; try eassumption.
          eexists a, map.empty, st0, words. ssplit.
          { reflexivity. }
          { eapply join_sep. 1: exact Sp. 1: exact H5p0. 1: exact Pt.
            unfold word_array at 2. ecancel. }
          { intros x v G.
            eapply map.putmany_of_list_zip_find_index in H1. 2: exact G.
            rewrite map.get_empty in H1. destruct H1. 2: discriminate. simp.
            apply nth_error_In in H1p0.
            eapply Forall_forall in Evp1; eassumption. }
          { intros x v G. rewrite map.get_empty in G. discriminate. }
          { unfold sep. exists st0, map.empty. ssplit; eauto. apply map.split_empty_r. reflexivity. }
          { unfold tmps, sep.
            repeat eexists.
            - rewrite <- map.put_putmany_commute. do 2 rewrite map.putmany_empty_r. reflexivity.
            - rewrite map.putmany_empty_r. unfold map.disjoint. intros *. intros G1 G2.
              rewrite map.get_put_dec in G2. destruct_one_match_hyp.
              2: { rewrite map.get_empty in G2. discriminate. }
              subst k. simp.
              eapply map.putmany_of_list_zip_find_index in H1. 2: exact G1.
              rewrite map.get_empty in H1. destruct H1. 2: discriminate. simp.
              apply nth_error_In in H1p0.
              eapply Forall_forall in Evp1. 2: eassumption. blia.
            - eapply map.disjoint_empty_r.
            - intros k v G. rewrite map.get_empty in G. discriminate. }
          { intros. rewrite map.get_empty in H5. discriminate. }
          { apply (f_equal Z.to_nat) in L'. rewrite Nat2Z.id in L'. rewrite L'. rewrite L.
            clear. (* <- LIA performance *)
            assert (bytes_per_word = 4 \/ bytes_per_word = 8) as B48. {
              unfold bytes_per_word. destruct width_cases as [E | E]; rewrite E; cbv; auto.
            }
            Z.div_mod_to_equations. blia. }
        }
        cbv beta. intros. simp. admit.
      + unfold related. intros. simp. admit.
    - (* exec.load *)
      eapply seq_cps.
      eapply load_arg_reg_correct; (blia || eassumption || idtac).
      clear mc2 H3. intros.
      eapply seq_cps.
      pose proof H2 as A. unfold related in A. simp.
      unfold Memory.load, Memory.load_Z, Memory.load_bytes in *. simp.
      eapply exec.load. {
        rewrite map.get_put_same. reflexivity. }
      { edestruct (@sep_def m2 (eq m)) as (m' & m2Rest & Sp & ? & ?).
        1: simpl_param_projections; ecancel_assumption. unfold map.split in Sp. simp. subst m'.
        unfold Memory.load, Memory.load_Z, Memory.load_bytes.
        erewrite map.getmany_of_tuple_in_disjoint_putmany; eauto. }
      eapply save_res_reg_correct.
      + eassumption.
      + eassumption.
      + blia.
    - (* exec.store *)
      eapply seq_cps. eapply load_arg_reg_correct; (blia || eassumption || idtac).
      clear mc2 H4. intros.
      eapply seq_cps. eapply load_arg_reg_correct; (blia || eassumption || idtac).
      clear mc2 H3. intros.
      pose proof H3 as A. unfold related in A. simp.
      unfold Memory.store, Memory.store_Z, Memory.store_bytes in *. simp.
      edestruct (@sep_def m2 (eq m)) as (m' & m2Rest & Sp & ? & ?).
      1: simpl_param_projections; ecancel_assumption. unfold map.split in Sp. simp. subst m'.
      eapply exec.store.
      1: eapply get_arg_reg_1; eassumption.
      1: apply map.get_put_same.
      { unfold Memory.store, Memory.store_Z, Memory.store_bytes.
        unfold Memory.load_bytes in *.
        erewrite map.getmany_of_tuple_in_disjoint_putmany; eauto. }
      do 4 eexists. split. 2: eassumption.
      unfold related.
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             end.
      all: try eassumption || reflexivity.
      spec store_bytes_sep_hi2lo as A. 1: eassumption.
      all: simpl_param_projections; ecancel_assumption.
    - (* exec.inlinetable *)
      eapply seq_cps. eapply load_arg_reg_correct; (blia || eassumption || idtac).
      clear mc2b mc2 H4. intros.
      eapply seq_cps.
      eapply exec.inlinetable.
      { unfold res_reg, arg_reg, tmp1, fp in *. destr (32 <=? x); destr (32 <=? i); try blia. }
      { rewrite map.get_put_same. reflexivity. }
      { eassumption. }
      eapply save_res_reg_correct.
      + eassumption.
      + eassumption.
      + blia.
    - (* exec.stackalloc *)
      rename H1 into IH.
      eapply exec.stackalloc. 1: assumption.
      intros.
      eapply seq_cps.
      edestruct grow_related_mem as (mCombined1 & ? & ?). 1,2: eassumption.
      eapply save_res_reg_correct''. 1: eassumption. 1: blia.
      intros.
      eapply exec.weaken. {
        eapply IH; eassumption. }
      cbv beta. intros. simp.
      edestruct shrink_related_mem as (mSmall2 & ? & ?). 1,2: eassumption.
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             end.
      1,4,3,2: eassumption.
    - (* exec.lit *)
      eapply seq_cps. eapply exec.lit.
      eapply save_res_reg_correct.
      + eassumption.
      + eassumption.
      + blia.
    - (* exec.op *)
      eapply seq_cps. eapply load_arg_reg_correct; (blia || eassumption || idtac).
      clear mc2 H3. intros.
      eapply seq_cps. eapply load_arg_reg_correct; (blia || eassumption || idtac).
      clear mc2 H2. intros.
      eapply seq_cps.
      eapply exec.op.
      1: eapply get_arg_reg_1; eassumption.
      1: apply map.get_put_same.
      eapply save_res_reg_correct.
      + eassumption.
      + eassumption.
      + blia.
    - (* exec.set *)
      eapply seq_cps. eapply load_arg_reg_correct; (blia || eassumption || idtac).
      clear mc2 H2. intros.
      eapply seq_cps.
      eapply exec.set. 1: apply map.get_put_same.
      eapply save_res_reg_correct.
      + eassumption.
      + eassumption.
      + blia.
    - (* exec.if_true *)
      unfold prepare_bcond. destr cond; cbn [ForallVars_bcond eval_bcond spill_bcond] in *; simp.
      + eapply exec_seq_assoc.
        eapply seq_cps. eapply load_arg_reg_correct; (blia || eassumption || idtac).
        clear mc2 H2. intros.
        eapply seq_cps. eapply load_arg_reg_correct; (blia || eassumption || idtac).
        clear mc2 H. intros.
        eapply exec.if_true. {
          cbn. erewrite get_arg_reg_1 by eassumption. rewrite map.get_put_same. congruence.
        }
        eapply IHexec; eassumption.
      + eapply seq_cps. eapply load_arg_reg_correct; (blia || eassumption || idtac).
        clear mc2 H2. intros.
        eapply exec.if_true. {
          cbn. rewrite map.get_put_same. congruence.
        }
        eapply IHexec; eassumption.
    - (* exec.if_false *)
      unfold prepare_bcond. destr cond; cbn [ForallVars_bcond eval_bcond spill_bcond] in *; simp.
      + eapply exec_seq_assoc.
        eapply seq_cps. eapply load_arg_reg_correct; (blia || eassumption || idtac).
        clear mc2 H2. intros.
        eapply seq_cps. eapply load_arg_reg_correct; (blia || eassumption || idtac).
        clear mc2 H. intros.
        eapply exec.if_false. {
          cbn. erewrite get_arg_reg_1 by eassumption. rewrite map.get_put_same. congruence.
        }
        eapply IHexec; eassumption.
      + eapply seq_cps. eapply load_arg_reg_correct; (blia || eassumption || idtac).
        clear mc2 H2. intros.
        eapply exec.if_false. {
          cbn. rewrite map.get_put_same. congruence.
        }
        eapply IHexec; eassumption.
    - (* exec.loop *)
      rename IHexec into IH1, H3 into IH2, H5 into IH12.
      eapply loop_cps.
      eapply exec.seq.
      1: eapply IH1; eassumption.
      cbv beta. intros. simp.
      unfold prepare_bcond. destr cond; cbn [ForallVars_bcond] in *; simp.
      + specialize H0 with (1 := H3p1). cbn in H0. simp.
        eapply exec.seq. {
          eapply load_arg_reg_correct''; (blia || eassumption || idtac).
        }
        cbv beta. intros. simp.
        eapply exec.weaken. {
          eapply load_arg_reg_correct''; (blia || eassumption || idtac).
        }
        cbv beta. intros. simp. cbn [eval_bcond spill_bcond].
        erewrite get_arg_reg_1 by eassumption. rewrite map.get_put_same. eexists. split; [reflexivity|].
        split; intros.
        * do 4 eexists. split.
          -- exact H3p4.
          -- eapply H1. 1: eassumption. cbn. rewrite E, E0. congruence.
        * eapply exec.weaken. 1: eapply IH2.
          -- eassumption.
          -- cbn. rewrite E, E0. congruence.
          -- eassumption.
          -- eassumption.
          -- cbv beta. intros. simp. eauto 10. (* IH12 *)
      + specialize H0 with (1 := H3p1). cbn in H0. simp.
        eapply exec.weaken. {
          eapply load_arg_reg_correct''; (blia || eassumption || idtac).
        }
        cbv beta. intros. simp. cbn [eval_bcond spill_bcond].
        rewrite map.get_put_same. eexists. split; [reflexivity|].
        split; intros.
        * do 4 eexists. split.
          -- exact H3p3.
          -- eapply H1. 1: eassumption. cbn. rewrite E. simpl_param_projections; congruence.
        * eapply exec.weaken. 1: eapply IH2.
          -- eassumption.
          -- cbn. rewrite E. simpl_param_projections; congruence.
          -- eassumption.
          -- eassumption.
          -- cbv beta. intros. simp. eauto 10. (* IH12 *)
    - (* exec.seq *)
      cbn in *. simp.
      rename H1 into IH2, IHexec into IH1.
      eapply exec.seq.
      + eapply IH1. 1: eassumption. eauto 15.
      + cbn. intros. simp. eapply IH2. 1,2: eassumption. eauto 15.
    - (* exec.skip *)
      eapply exec.skip. eauto 20.
    all: fail.
  Abort.

End Spilling.
