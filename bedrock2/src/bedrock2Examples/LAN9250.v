Require Import bedrock2.Syntax bedrock2.NotationsCustomEntry.
Require Import coqutil.Z.prove_Zeq_bitwise.
Require Import bedrock2Examples.SPI.

From coqutil Require Import letexists.
Require Import bedrock2.AbsintWordToZ.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Z.div_mod_to_equations.
Require Import coqutil.Z.Lia.

Import BinInt String List.ListNotations.
Local Open Scope Z_scope. Local Open Scope string_scope. Local Open Scope list_scope.

Local Notation MMIOWRITE := "MMIOWRITE".
Local Notation MMIOREAD := "MMIOREAD".

Definition lan9250_readword : function :=
  ("lan9250_readword", (("addr"::nil), ("ret"::"err"::nil), bedrock_func_body:(
    SPI_CSMODE_ADDR = ($0x10024018);
    io! ret = MMIOREAD(SPI_CSMODE_ADDR);
    ret = (ret | $2);
    output! MMIOWRITE(SPI_CSMODE_ADDR, ret);

    (* manually register-allocated, apologies for variable reuse *)
    unpack! ret, err = spi_xchg($0x0b);        require !err; (* FASTREAD *)
    unpack! ret, err = spi_xchg(addr >> $8);     require !err;
    unpack! ret, err = spi_xchg(addr & $0xff); require !err;
    unpack! ret, err = spi_xchg(err);                    require !err; (* dummy *)

    unpack! ret, err = spi_xchg(err);                    require !err; (* read *)
    unpack! addr, err = spi_xchg(err);                   require !err; (* read *)
    ret = (ret | (addr << $8));
    unpack! addr, err = spi_xchg(err);                   require !err; (* read *)
    ret = (ret | (addr << $16));
    unpack! addr, err = spi_xchg(err);                   require !err; (* read *)
    ret = (ret | (addr << $24));

    io! addr = $MMIOREAD(SPI_CSMODE_ADDR);
    addr = (addr & coq:(Z.lnot 2));
    output! $MMIOWRITE(SPI_CSMODE_ADDR, addr)
  ))).

Definition lan9250_writeword : function :=
  ("lan9250_writeword", (("addr"::"data"::nil), ("err"::nil), bedrock_func_body:(
    SPI_CSMODE_ADDR = $0x10024018;
    io! ret = $MMIOREAD(SPI_CSMODE_ADDR);
    ret = (ret | $2);
    output! $MMIOWRITE(SPI_CSMODE_ADDR, ret);

    (* manually register-allocated, apologies for variable reuse *)
    Oxff = $0xff;
    eight = $8;
    unpack! ret, err = spi_xchg($0x02); require !err; (* FASTREAD *)
    unpack! ret, err = spi_xchg(addr >> eight);   require !err;
    unpack! ret, err = spi_xchg(addr & Oxff);     require !err;

    unpack! ret, err = spi_xchg(data & Oxff);     require !err; (* write *)
    data = (data >> eight);
    unpack! ret, err = spi_xchg(data & Oxff);     require !err; (* write *)
    data = (data >> eight);
    unpack! ret, err = spi_xchg(data & Oxff);     require !err; (* write *)
    data = (data >> eight);
    unpack! ret, err = spi_xchg(data);     require !err; (* write *)

    io! addr = $MMIOREAD(SPI_CSMODE_ADDR);
    addr = (addr & coq:(Z.lnot 2));
    output! $MMIOWRITE(SPI_CSMODE_ADDR, addr)
  ))).

Definition MAC_CSR_DATA : Z := 0x0A8.
Definition MAC_CSR_CMD : Z := 0x0A4.
Definition BYTE_TEST : Z := 0x64.

Definition lan9250_mac_write : function :=
  ("lan9250_mac_write", (("addr"::"data"::nil), ("err"::nil), bedrock_func_body:(
    unpack! err = lan9250_writeword($MAC_CSR_DATA, data);
    require !err;
unpack! err = lan9250_writeword($MAC_CSR_CMD, coq:(Z.shiftl 1 31)|addr);
    require !err;
          unpack! data, err = lan9250_readword($BYTE_TEST)
          (* while (lan9250_readword(0xA4) >> 31) { } // Wait until BUSY (= MAX_CSR_CMD >> 31) goes low *)
  ))).

Definition lan9250_wait_for_boot : function :=
  ("lan9250_wait_for_boot", (nil, ("err"::nil), bedrock_func_body:(
  err = ($0);
  byteorder = ($0);
  i = ($lightbulb_spec.patience); while (i) { i = (i - $1);
          unpack! byteorder, err = lan9250_readword($0x64);
    if err { i = (i^i) }
    else if (byteorder == $0x87654321) { i = (i^i) }
    else { err = ($-1) }
  }
  ))).

Definition lan9250_init : function :=
  ("lan9250_init", (nil, ("err"::nil), bedrock_func_body:(
          unpack! err = lan9250_wait_for_boot();
    require !err;
          unpack! hw_cfg, err = lan9250_readword($lightbulb_spec.HW_CFG);
    require !err;
    hw_cfg = (hw_cfg | coq:(Z.shiftl 1 20)); (* mustbeone *)
    hw_cfg = (hw_cfg & coq:(Z.lnot (Z.shiftl 1 21))); (* mustbezero *)
    unpack! err = lan9250_writeword($lightbulb_spec.HW_CFG, hw_cfg);
    require !err;

    (* 20: full duplex; 18: promiscuous; 2, 3: TXEN/RXEN *)
        unpack! err = lan9250_mac_write($1, coq:(Z.lor (Z.shiftl 1 20) (Z.lor (Z.shiftl 1 18) (Z.lor (Z.shiftl 1 3) (Z.shiftl 1 2)))));
    require !err;
          unpack! err = lan9250_writeword($0x070, coq:(Z.lor (Z.shiftl 1 2) (Z.shiftl 1 1)))
  ))).

Require Import bedrock2.ProgramLogic.
Require Import bedrock2.FE310CSemantics.
Require Import coqutil.Word.Interface.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.TracePredicate. Import TracePredicateNotations.
Require bedrock2Examples.lightbulb_spec.

Import coqutil.Map.Interface.
Import lightbulb_spec.
Import Loops.

Section WithParameters.
  Context {word: word.word 32} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Global Instance spec_of_lan9250_readword : ProgramLogic.spec_of "lan9250_readword" := fun functions => forall t m a,
    (0x0 <= Word.Interface.word.unsigned a < 0x400) ->
    WeakestPrecondition.call functions "lan9250_readword" t m [a] (fun T M RETS =>
      M = m /\
      exists ret err, RETS = [ret; err] /\
      exists iol, T = iol ++ t /\
      exists ioh, mmio_trace_abstraction_relation ioh iol /\ Logic.or
        (word.unsigned err <> 0 /\ (any +++ lightbulb_spec.spi_timeout _) ioh)
        (word.unsigned err = 0 /\ lightbulb_spec.lan9250_fastread4 _ a ret ioh)).

  Global Instance spec_of_lan9250_writeword : ProgramLogic.spec_of "lan9250_writeword" := fun functions =>
    forall t m a v,
      (0x0 <= Word.Interface.word.unsigned a < 0x400) ->
    (((WeakestPrecondition.call functions "lan9250_writeword"))) t m [a; v]
      (fun T M RETS =>
      M = m /\
      exists err, RETS = [err] /\
      exists iol, T = iol ++ t /\
      exists ioh, mmio_trace_abstraction_relation ioh iol /\ Logic.or
        (word.unsigned err <> 0 /\ (any +++ lightbulb_spec.spi_timeout _) ioh)
        (word.unsigned err = 0 /\ lightbulb_spec.lan9250_write4 _ a v ioh)).

  Import lightbulb_spec.

  Global Instance spec_of_lan9250_mac_write : ProgramLogic.spec_of "lan9250_mac_write" := fun functions =>
    forall t m a v,
      (0 <= Word.Interface.word.unsigned a < 2^31) ->
    (((WeakestPrecondition.call functions "lan9250_mac_write"))) t m [a; v]
      (fun T M RETS =>
      M = m /\
      exists err, RETS = [err] /\
      exists iol, T = iol ++ t /\
      exists ioh, mmio_trace_abstraction_relation ioh iol /\ Logic.or
        (word.unsigned err <> 0 /\ (any +++ lightbulb_spec.spi_timeout _) ioh)
        (word.unsigned err = 0 /\  lan9250_mac_write_trace _ a v ioh )).

  Global Instance spec_of_lan9250_wait_for_boot : ProgramLogic.spec_of "lan9250_wait_for_boot" := fun functions =>
    forall t m,
    (((WeakestPrecondition.call functions "lan9250_wait_for_boot"))) t m []
      (fun T M RETS =>
      M = m /\
      exists err, RETS = [err] /\
      exists iol, T = iol ++ t /\
      exists ioh, mmio_trace_abstraction_relation ioh iol /\ Logic.or
        (word.unsigned err <> 0 /\ (any +++ lightbulb_spec.spi_timeout _) ioh \/
        (word.unsigned err <> 0 /\ lan9250_boot_timeout _ ioh))
        (word.unsigned err = 0 /\ lan9250_wait_for_boot_trace _ ioh)).

  Global Instance spec_of_lan9250_init : ProgramLogic.spec_of "lan9250_init" := fun functions =>
    forall t m,
    (((WeakestPrecondition.call functions "lan9250_init"))) t m []
      (fun T M RETS =>
      M = m /\
      exists err, RETS = [err] /\
      exists iol, T = iol ++ t /\
      exists ioh, mmio_trace_abstraction_relation ioh iol /\ Logic.or
        (word.unsigned err <> 0 /\ (any +++ lightbulb_spec.spi_timeout _) ioh \/
        (word.unsigned err <> 0 /\ lan9250_boot_timeout _ ioh))
        (word.unsigned err = 0 /\ lan9250_init_trace _ ioh)).

  Local Ltac split_if :=
    lazymatch goal with
      |- WeakestPrecondition.cmd _ ?c _ _ _ ?post =>
      let c := eval hnf in c in
          lazymatch c with
          | cmd.cond _ _ _ => letexists; split; [solve[repeat straightline]|split]
          end
    end.

  Ltac evl := (* COQBUG(has_variable) *)
    repeat match goal with
      | |- context G[string_dec ?x ?y] =>
          let e := eval cbv in (string_dec x y) in
          let goal := context G [e] in
          change goal
      | |- context G[word.unsigned ?x] =>
          let x := rdelta x in
          let x := lazymatch x with word.of_Z ?x => x end in
          let x := rdelta x in
          let x := rdelta x in
          requireZcst x;
          let x := eval cbv in x in
          let goal := context G [x] in
          change goal
      | |- context G [app nil ?xs] =>
        let goal := context G [ xs ] in
        change goal
    end.

  Ltac trace_alignment :=
    repeat (eapply lightbulb_spec.align_trace_app
      || eapply lightbulb_spec.align_trace_cons
      || exact (eq_refl (app nil _))).

  Ltac mmio_trace_abstraction :=
    repeat match goal with
    | |- mmio_trace_abstraction_relation _ _ => cbv [mmio_trace_abstraction_relation]
    | |- Forall2 mmio_event_abstraction_relation _ _ =>
        eassumption || eapply Forall2_app || eapply Forall2_nil || eapply Forall2_cons
    | |- mmio_event_abstraction_relation _ _ =>
        (left + right); eexists _, _; split; exact eq_refl
    end.

  Local Ltac slv := solve [ trivial | eauto 2 using TracePredicate.any_app_more | assumption | blia | trace_alignment | mmio_trace_abstraction ].

  Ltac t :=
    match goal with
    | _ => slv
    | _ => progress evl

    | H :  _ /\ _ \/ ?Y /\ _, G : not ?X |- _ =>
        constr_eq X Y; let Z := fresh in destruct H as [|[Z ?]]; [|case (G Z)]
    | H :  not ?Y /\ _ \/ _ /\ _, G : ?X |- _ =>
        constr_eq X Y; let Z := fresh in destruct H as [[Z ?]|]; [case (Z G)|]
    | |- exists x, _ /\ _ => eexists; split; [repeat f_equal; slv|]
    | |- ?A /\ _ \/ ?B /\ _ =>
        match goal with
        | H: A |- _ => left  | H: not B |- _ => left
        | H: B |- _ => right | H: not A |- _ => right
        end

    | |- _ /\ _ => split; [repeat t|]

    | _ => straightline
    | _ => straightline_call; [  solve[repeat t].. | ]
    | _ => split_if; [  solve[repeat t].. | ]
    | |- WeakestPrecondition.cmd _ (cmd.interact _ _ _) _ _ _ _ => eapply WeakestPreconditionProperties.interact_nomem; [  solve[repeat t].. | ]
    end.

  Import Word.Properties.

  Lemma lan9250_init_ok : program_logic_goal_for_function! lan9250_init.
  Proof.
    repeat t.
    split_if; repeat t.
    { rewrite ?app_nil_r; intuition idtac. }
    straightline_call.
    { clear -word_ok; rewrite word.unsigned_of_Z; cbv; split; congruence. }
    repeat t.
    split_if; repeat t.
    { rewrite ?app_nil_r; intuition eauto using TracePredicate.any_app_more. }
    straightline_call.
    { clear -word_ok; rewrite word.unsigned_of_Z; cbv; split; congruence. }
    repeat t.
    split_if; repeat t.
    { rewrite ?app_nil_r; intuition eauto using TracePredicate.any_app_more. }
    straightline_call.
    { clear -word_ok; rewrite word.unsigned_of_Z; cbv; split; congruence. }
    repeat t.
    split_if; repeat t.
    { rewrite ?app_nil_r; intuition eauto using TracePredicate.any_app_more. }
          straightline_call.
    { clear -word_ok; rewrite word.unsigned_of_Z; cbv; split; congruence. }
    repeat t.
    rewrite ?app_nil_r; intuition eauto using TracePredicate.any_app_more.

    right.
    split; trivial.
    cbv [lan9250_init_trace].
    eexists.
    repeat eapply concat_app; eauto.
  Qed.

  Local Hint Mode map.map - - : typeclass_instances. (* COQBUG https://github.com/coq/coq/issues/14707 *)

  Lemma lan9250_writeword_ok : program_logic_goal_for_function! lan9250_writeword.
  Proof.
    repeat t.
    letexists; split; [exact eq_refl|]; split; [split; trivial|].
    { subst addr. cbv [isMMIOAddr SPI_CSMODE_ADDR].
      rewrite !word.unsigned_of_Z; cbv [word.wrap].
      split; [|exact eq_refl]; clear.
      cbv -[Z.le Z.lt]. blia. }
    repeat straightline; split; trivial.
    repeat straightline.
    eapply WeakestPreconditionProperties.interact_nomem; repeat straightline.
    letexists; letexists; split; [exact eq_refl|]; split; [split; trivial|].
    { subst addr. cbv [isMMIOAddr SPI_CSMODE_ADDR].
      rewrite !word.unsigned_of_Z; cbv [word.wrap].
      split; [|exact eq_refl]; clear.
      cbv -[Z.le Z.lt]. blia. }
    repeat straightline; split; trivial.
    repeat straightline.

    straightline_call.
    1: {
      match goal with |- word.unsigned ?x < _ => let H := unsigned.zify_expr x in rewrite H end.
      revert H7.
      evl.
      intros.
      Z.div_mod_to_equations. blia.
    }
    repeat t.
    straightline_call.
    1: {
      match goal with |- word.unsigned ?x < _ => let H := unsigned.zify_expr x in rewrite H end.
      revert H7.
      evl.
      intros.
      Z.div_mod_to_equations. blia.
    }
    repeat t.
    straightline_call.
    1: {
      match goal with |- word.unsigned ?x < _ => let H := unsigned.zify_expr x in rewrite H end.
      Z.div_mod_to_equations. blia.
    }
    repeat t.
    straightline_call.
    1: {
      match goal with |- word.unsigned ?x < _ => let H := unsigned.zify_expr x in rewrite H end.
      Z.div_mod_to_equations. blia.
    }
    repeat t.
    straightline_call.
    1: {
      match goal with |- word.unsigned ?x < _ => let H := unsigned.zify_expr x in rewrite H end.
      Z.div_mod_to_equations. blia.
    }
    repeat t.

    straightline_call.
    1: {
      match goal with |- word.unsigned ?x < _ => let H := unsigned.zify_expr x in rewrite H end.
      Z.div_mod_to_equations. blia.
    }
    repeat t.

    straightline_call.
    1: {
      match goal with |- word.unsigned ?x < _ => let H := unsigned.zify_expr x in rewrite H end.
      subst data4 data3 data2 data1.
      pose proof word.unsigned_range v.
      Z.div_mod_to_equations. blia.
    }

    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    letexists; split; [exact eq_refl|]; split; [split; trivial|].
    { subst addr. cbv [isMMIOAddr SPI_CSMODE_ADDR].
      rewrite !word.unsigned_of_Z; cbv [word.wrap].
      split; [|exact eq_refl]; clear.
      cbv -[Z.le Z.lt]. blia. }
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    t.
    letexists; letexists; split; [exact eq_refl|]; split; [split; trivial|].
    { subst addr addr0. cbv [isMMIOAddr SPI_CSMODE_ADDR].
      rewrite !word.unsigned_of_Z; cbv [word.wrap].
      split; [|exact eq_refl]; clear.
      cbv -[Z.le Z.lt]. blia. }
    repeat t.

    do 6 letexists.
    cbv [spi_begin spi_xchg_deaf spi_end one].
    Local Arguments spi_xchg {_ _}.

    (* aligning regex and mmiotrace, not sure how to do it in a principled way *)

    cbv [concat existsl].

    all : repeat match goal with
      | |- _ /\ _ => split
      | |- exists _, _ => eexists
      | |- ?e = _ => (let e := rdelta e in is_evar e); try subst e; reflexivity
      | |- _ = ?e => (let e := rdelta e in is_evar e); try subst e; reflexivity
    end.

    all : repeat match goal with
      |-  context[?e] => is_evar e; set e
          end.

    all:
    repeat match goal with |- context[@cons ?T ?x ?y] =>
        match y with
        | [] => fail 1
        | _=> change (@cons T x y) with (@app T (@cons T x nil) y) end end.

    1: rewrite !app_assoc.
    1: repeat f_equal.

    all : repeat match goal with
      |-  context[?e] => (let v := rdelta e in is_evar v); subst e
          end.
    all : trivial.
    all : eauto.

    all : try (rewrite Byte.byte.unsigned_of_Z; eapply Z.mod_small).

    all : pose proof word.unsigned_range a.
    all : rewrite ?word.unsigned_and_nowrap, ?word.unsigned_sru_nowrap, ?word.unsigned_of_Z; rewrite ?word.unsigned_of_Z.
    all : repeat match goal with |- context G[word.wrap ?x] => let g := context G [x] in change g end.
    all : change 255 with (Z.ones 8).
    all : rewrite ?Z.shiftr_div_pow2, ?Z.land_ones by blia.
    3,4,5: clear -H7 H36; Z.div_mod_to_equations; blia.
    { subst addr.
      cbv [SPI_CSMODE_HOLD].
      erewrite word.unsigned_of_Z.
      change (word.wrap 2) with 2.
      erewrite (word.of_Z_inj_mod _ (Z.lnot 2)); trivial. }
    { instantiate (1:=x1); move H11 at bottom.
      (* Local Arguments spi_xchg {_} _ _ _. *)
      erewrite word.unsigned_of_Z in H11.
      exact H11. }

    cbv [List.app].
    repeat match goal with x := _ |- _ => subst x end.
    cbv [LittleEndianList.le_combine].
    repeat rewrite ?word.unsigned_of_Z, word.unsigned_sru_nowrap by (rewrite word.unsigned_of_Z; exact eq_refl).

    try erewrite ?word.unsigned_of_Z.
    cbv [word.wrap].
    repeat match goal with |- context G [?a mod ?b] => let goal := context G [a] in change goal end.
    rewrite ?Z.shiftl_mul_pow2 by (clear; blia).

    change 255 with (Z.ones 8).
    rewrite <-!Z.shiftl_mul_pow2 by blia.
    pose proof (@word.unsigned_range _ _ word_ok v).
    set (@word.unsigned _ _ v) as X in *.
    rewrite ?Byte.byte.unsigned_of_Z.
    unfold Byte.byte.wrap.
    rewrite <- ?Z.land_ones by blia.
    prove_Zeq_bitwise.
  Qed.

  Lemma lan9250_mac_write_ok : program_logic_goal_for_function! lan9250_mac_write.
  Proof.
    repeat match goal with
      | _ => straightline
      | _ => straightline_call
      | _ => split_if
      | _ => rewrite word.unsigned_of_Z
      | |- context G [word.wrap ?a] =>
          requireZcst a;
          let t := eval cbv in (word.wrap a) in
          let g := context G [t] in
          change g
      | |- _ <= _ < _ => blia
      | |- _ /\ _ => split
    end.

    all : repeat t.

    intuition idtac; repeat t.

    eexists.
    rewrite app_nil_r.
    eauto using concat_app.
  Qed.

  Lemma lan9250_wait_for_boot_ok : program_logic_goal_for_function! lan9250_wait_for_boot.
  Proof.
    repeat straightline.
    refine ((atleastonce ["err"; "i"; "byteorder"] (fun v T M ERR I BUSY =>
       v = word.unsigned I /\ word.unsigned I <> 0 /\ M = m /\
       exists tl, T = tl++t /\
       exists th, mmio_trace_abstraction_relation th tl /\
       exists n, (multiple (lan9250_boot_attempt _) n) th /\
       Z.of_nat n + word.unsigned I = patience
            ))
            _ _ _ _ _ _ _);
      cbn [reconstruct map.putmany_of_list HList.tuple.to_list
           HList.hlist.foralls HList.tuple.foralls
           HList.hlist.existss HList.tuple.existss
           HList.hlist.apply  HList.tuple.apply
           HList.hlist
           List.repeat Datatypes.length
           HList.polymorphic_list.repeat HList.polymorphic_list.length
           PrimitivePair.pair._1 PrimitivePair.pair._2] in *; repeat straightline.
    { exact (Z.lt_wf 0). }
    { exfalso. subst i. rewrite word.unsigned_of_Z in H0; inversion H0. }
    { subst i; repeat t.
      { rewrite word.unsigned_of_Z. intro X. inversion X. }
      exists O; cbn; split; trivial.
      rewrite word.unsigned_of_Z. exact eq_refl. }
    { straightline_call.
      { rewrite word.unsigned_of_Z.
        repeat match goal with
        | |- context G [word.wrap ?a] =>
            requireZcst a;
            let t := eval cbv in (word.wrap a) in
            let g := context G [t] in
            change g
        end.
        clear; blia. }
      repeat straightline.
      split_if.
      {
        repeat (t; []); split.
        { intro X. exfalso. eapply X. subst i. rewrite word.unsigned_xor.
          rewrite Z.lxor_nilpotent. exact eq_refl. }
        repeat t; eauto using TracePredicate.any_app_more.
      }
      repeat straightline.
      split_if; repeat t.
      { exfalso. eapply H9. subst i. rewrite word.unsigned_xor.
        rewrite Z.lxor_nilpotent. exact eq_refl. }
      { right.
        split; trivial.
        cbv [lan9250_wait_for_boot_trace].
        rewrite app_nil_r.
        eapply concat_app; eauto using kleene_multiple.
        destruct (word.eqb_spec x5 (word.of_Z 2271560481)); subst.
        2: { subst v0. rewrite word.unsigned_of_Z in H3; case (H3 eq_refl). }
        eassumption. }
      { eexists. split.
        1: split; [exact eq_refl|].
        2: {
          pose proof word.unsigned_range i.
          pose proof word.unsigned_range x0.
          subst v. subst i.
          rewrite word.unsigned_sub, word.unsigned_of_Z.
          change (word.wrap 1) with 1.
          cbv [word.wrap]; rewrite Z.mod_small; blia. }
        repeat t.
        rewrite app_nil_r.
        eexists (S _).
        split.
        { eapply multiple_expand_right, concat_app; eauto.
          destruct (word.eqb_spec x5 (word.of_Z 2271560481)); subst.
          { subst v0. rewrite word.unsigned_of_Z in H3. inversion H3. }
          eexists. split; eauto.
          intro X.
          eapply H10.
          eapply word.unsigned_inj; rewrite word.unsigned_of_Z.
          setoid_rewrite X.
          exact eq_refl. }
        rewrite <-H6.
        rewrite Znat.Nat2Z.inj_succ.
        subst i.
        rewrite word.unsigned_sub, word.unsigned_of_Z.
        pose proof word.unsigned_range x0.
        change (word.wrap 1) with 1.
        cbv [word.wrap]; rewrite Z.mod_small; try blia. }
      { left. right.
        split. { intro X. subst err. rewrite word.unsigned_of_Z in X. inversion X. }
        rewrite app_nil_r.
        cbv [lan9250_boot_timeout].
        rewrite <-H6.
        replace (word.unsigned x0) with 1; cycle 1.
        { subst i.
          pose proof word.unsigned_range x0.
          rewrite word.unsigned_sub, word.unsigned_of_Z in H9.
          change (word.wrap 1) with 1 in H9.
          cbv [word.wrap] in H9; rewrite Z.mod_small in H9; try blia. }
        rewrite Z.add_1_r.
        rewrite Znat.Z2Nat.inj_succ by (clear; blia).
        rewrite Znat.Nat2Z.id.

        eapply multiple_expand_right, concat_app; eauto.
        eexists; split; eauto.
        destruct (word.eqb_spec x5 (word.of_Z 2271560481)); subst.
        { subst v0. rewrite word.unsigned_of_Z in H3. inversion H3. }
        intro X.
        eapply H10.
        eapply word.unsigned_inj; rewrite word.unsigned_of_Z.
        setoid_rewrite X.
        exact eq_refl. } }
  Qed.

  Lemma lan9250_readword_ok : program_logic_goal_for_function! lan9250_readword.
  Proof.
    Time repeat straightline.

    repeat match goal with
      | H :  _ /\ _ \/ ?Y /\ _, G : not ?X |- _ =>
          constr_eq X Y; let Z := fresh in destruct H as [|[Z ?]]; [|case (G Z)]
      | H :  not ?Y /\ _ \/ _ /\ _, G : ?X |- _ =>
          constr_eq X Y; let Z := fresh in destruct H as [[Z ?]|]; [case (Z G)|]
      | _ => progress cbv [MMIOREAD MMIOWRITE]
      | _ => progress cbv [SPI_CSMODE_ADDR]
      | |- _ /\ _ => split
      | |- context G[string_dec ?x ?x] =>
          let e := eval cbv in (string_dec x x) in
          let goal := context G [e] in
          change goal
      | |- context G[string_dec ?x ?y] =>
          unshelve erewrite (_ : string_dec x y = right _); [ | exact eq_refl | ]
      | _ => straightline_cleanup
      | |- WeakestPrecondition.cmd _ (cmd.interact _ _ _) _ _ _ _ => eapply WeakestPreconditionProperties.interact_nomem
      | |- ext_spec _ _ _ _ _ =>
    letexists; split; [exact eq_refl|]; split; [split; trivial|]
      | |- ext_spec _ _ _ _ _ =>
    letexists; letexists; split; [exact eq_refl|]; split; [split; trivial|]

      | H: ?x = 0 |-  _ => rewrite H
      | |- ?F ?a ?b ?c =>
          match F with WeakestPrecondition.get => idtac end;
          let f := (eval cbv beta delta [WeakestPrecondition.get] in F) in
          change (f a b c); cbv beta
      | _ => straightline
      | _ => straightline_call
      | _ => split_if
    end.
    all: try (eexists _, _; split; trivial).
    all: try (exact eq_refl).
    all: auto.
    1,2: subst addr.
    3,4: subst addr0.
    16,17:subst addr1.
    18,19:subst addr3.
    1,2,3,4,16,17,18,19: cbv [isMMIOAddr SPI_CSMODE_ADDR];
      rewrite !word.unsigned_of_Z; cbv [word.wrap];
      trivial; cbv -[Z.le Z.lt]; blia.

    all : try (
      repeat match goal with x := _ ++ _ |- _ => subst x end;
      eexists; split;
      [ repeat match goal with
        |- context G [cons ?a ?b] =>
          assert_fails (idtac; match b with nil => idtac end);
          let goal := context G [(app (cons a nil) b)] in
          change goal
        end;
      rewrite !app_assoc;
      repeat eapply (fun A => f_equal2 (@List.app A)); eauto |]).

    all : try (
      eexists; split; [
      repeat (eassumption || eapply Forall2_app || eapply Forall2_nil || eapply Forall2_cons) |]).
    all : try ((left + right); eexists _, _; split; exact eq_refl).


    all : try (left; split; [eassumption|]).
    all : repeat rewrite <-app_assoc.

    all : eauto using TracePredicate.any_app_more.
    { rewrite ?word.unsigned_of_Z; exact eq_refl. }
    { rewrite Properties.word.unsigned_sru_nowrap; cycle 1.
      { rewrite word.unsigned_of_Z; exact eq_refl. }
      rewrite word.unsigned_of_Z; cbv [word.wrap]; rewrite Z.mod_small by (cbv; split; congruence).
      rewrite Z.shiftr_div_pow2 by blia.
      clear -H8.
      change 0x400 with (4*256) in *.
      Z.div_mod_to_equations. blia. }
    { rewrite Properties.word.unsigned_and_nowrap.
      rewrite word.unsigned_of_Z; cbv [word.wrap]; rewrite Z.mod_small by (cbv; split; congruence).
      change 255 with (Z.ones 8).
      rewrite Z.land_ones;
      Z.div_mod_to_equations; blia. }

    right.
    eexists; eauto.
    eexists _, _,  _, _, _, _.

    cbv [
    lightbulb_spec.lan9250_fastread4
    lightbulb_spec.spi_begin
    lightbulb_spec.spi_xchg_mute
    lightbulb_spec.spi_xchg_dummy
    lightbulb_spec.spi_xchg_deaf
    lightbulb_spec.spi_end
    one
    existsl
    ].

    cbv [concat].
    repeat match goal with
      | |- _ /\ _ => eexists
      | |- exists _, _ => eexists
      | |- ?e = _ => is_evar e; exact eq_refl
      | |- _ = ?e => is_evar e; exact eq_refl
    end.

    1 : rewrite <-app_assoc.
    1 : cbv [SPI_CSMODE_HOLD] ; rewrite word.unsigned_of_Z; exact eq_refl.
    all : rewrite word.unsigned_of_Z in H12; try eassumption.
    1,2:
      repeat match goal with
      | _ => rewrite word.of_Z_unsigned
      | _ => rewrite Byte.byte.unsigned_of_Z
      | _ => cbv [Byte.byte.wrap]; rewrite Z.mod_small
      | _ => solve [trivial]
      end.
    { rewrite Properties.word.unsigned_sru_nowrap by (rewrite word.unsigned_of_Z; exact eq_refl).
      rewrite word.unsigned_of_Z; cbv [word.wrap]; rewrite Z.mod_small by (cbv; split; congruence).
      rewrite Z.shiftr_div_pow2 by blia.
      revert dependent a; clear; intros.
      change 0x400 with (4*256) in *.
      Z.div_mod_to_equations. blia. }
    { rewrite Properties.word.unsigned_and_nowrap.
      rewrite word.unsigned_of_Z; cbv [word.wrap]; rewrite Z.mod_small by (cbv; split; congruence).
      change 255 with (Z.ones 8); rewrite Z.land_ones by blia.
      Z.div_mod_to_equations. blia. }
    repeat match goal with x := _ |- _ => subst x end.
    cbv [LittleEndianList.le_combine].

    repeat rewrite ?Properties.word.unsigned_or_nowrap, <-?Z.lor_assoc by (rewrite ?word.unsigned_of_Z; exact eq_refl).
    change (Z.shiftl 0 8) with 0 in *; rewrite Z.lor_0_r.
    rewrite !Z.shiftl_lor, !Z.shiftl_shiftl in * by blia.
    repeat f_equal.

    (* little-endian word conversion, automatable (bitwise Z and word) *)
    all : try rewrite word.unsigned_slu by (rewrite ?word.unsigned_of_Z; exact eq_refl).
    all : rewrite ?word.unsigned_of_Z.
    all : cbv [word.wrap].
    all : repeat match goal with |- context G [?a mod ?b] => let goal := context G [a] in change goal end.
    all : repeat match goal with |- context[Byte.byte.unsigned ?x] => is_var x; replace (Byte.byte.unsigned x) with (Byte.byte.wrap (Byte.byte.unsigned x)) by eapply Byte.byte.wrap_unsigned; set (Byte.byte.unsigned x) as X; clearbody X end.
    all : change (8+8) with 16.
    all : change (8+16) with 24.
    all : cbv [Byte.byte.wrap].
    all : clear.
    all : rewrite ?Z.shiftl_mul_pow2 by blia.
    all : try (Z.div_mod_to_equations; blia).
  Qed.
End WithParameters.
