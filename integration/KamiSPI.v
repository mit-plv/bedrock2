Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.TracePredicate.

Module List. Section __.
  Context {T : Type}.
  Definition interleave_body interleave (zs xs ys : list T) : Prop :=
    match zs with
    | nil => xs = nil /\ zs = nil
    | cons z zs' =>
        (exists xs', xs = cons z xs' /\ interleave zs' xs' ys ) \/
        (exists ys', ys = cons z ys' /\ interleave zs' xs  ys')
    end.
  Definition interleave (xs ys zs : list T) : Prop :=
    (fix interleave zs := interleave_body interleave zs) zs xs ys.

  Lemma interleave_rcons z zs xs ys y (H : z = y) (HH : interleave xs ys zs) : interleave xs (y::ys) (z::zs).
  Proof. subst; cbn; eauto. Qed.
  Lemma interleave_lcons z zs xs ys x (H : z = x) (HH : interleave xs ys zs) : interleave (x::xs) ys (z::zs).
  Proof. subst; cbn; eauto. Qed.

  Lemma interleave_rapp z zs xs ys y (H : z = y) (HH : interleave xs ys zs) : interleave xs (y++ys) (z++zs).
  Proof. subst; induction y; cbn; eauto. Qed.
  Lemma interleave_lapp z zs xs ys x (H : z = x) (HH : interleave xs ys zs) : interleave (x++xs) ys (z++zs).
  Proof. subst; induction x; cbn; eauto. Qed.

  Lemma interleave_nil_r zs : interleave zs nil zs.
  Proof. induction zs; cbn; eauto. Qed.
  Lemma interleave_nil_l zs : interleave nil zs zs.
  Proof. induction zs; cbn; eauto. Qed.
End __. End List.


Require Import Coq.Classes.Morphisms.
Module TracePredicate.
  Definition flat_map {A B} (P:A->list B->Prop) xs :=
    List.fold_right app (eq nil) (List.map P xs).

  (* [interleave] trace of *arbitrarily small slices of* [P] and [Q].
     This sometimes makes sense for completely independent streams of
     events, but consider [(P \/ Q)^*] instead first. *)
  Definition interleave {T} (P Q : list T -> Prop) :=
    fun zs => exists xs ys, List.interleave xs ys zs /\ P xs /\ Q ys.

  Global Instance Proper_interleave_impl {T} :
    Proper (pointwise_relation _ Basics.impl==>pointwise_relation _ Basics.impl==>pointwise_relation _ Basics.impl) (@TracePredicate.interleave T).
  Proof.
    intros a b c d e f g h.
    cbv [interleave pointwise_relation Basics.impl] in *.
    firstorder idtac.
  Qed.
  Global Instance Proper_interleave_iff {T} :
    Proper (pointwise_relation _ iff==>pointwise_relation _ iff==>pointwise_relation _ iff) (@TracePredicate.interleave T).
  Proof.
    intros a b c d e f g.
    cbv [interleave pointwise_relation iff] in *.
    firstorder idtac.
  Qed.

  Local Infix "||" := TracePredicate.interleave.
  Lemma interleave_rapp {T} {P QQ Q : list T -> Prop} z zs
    (H : Q z) (HH : interleave P QQ zs) : interleave P (QQ +++ Q) (z++zs).
  Proof.
    destruct HH as (?&?&?&?&?).
    eexists _, _; split.
    eapply List.interleave_rapp; eauto.
    split; eauto.
  Admitted.
  
  Lemma interleave_lapp {T} {PP P Q : list T -> Prop} z zs
    (H : P z) (HH : interleave PP Q zs) : interleave (PP +++ P) Q (z++zs).
  Proof.
    destruct HH as (?&?&?&?&?).
    eexists _, _; split.
    eapply List.interleave_lapp; eauto.
    split; eauto.
  Admitted.

  Definition interleave_rcons {T} {P QQ Q} (z:T) zs H HH : interleave _ _ (cons _ _) :=
    @interleave_rapp T P QQ Q [z] zs H HH.
  Definition interleave_lcons {T} {PP P Q} (z:T) zs H HH : interleave _ _ (cons _ _):=
    @interleave_lapp T PP P Q [z] zs H HH.

  Lemma interleave_rkleene {T} {P Q : list T -> Prop} z zs
    (H : Q^* z) (HH : interleave P (Q^* ) zs) : interleave P (Q^* ) (z++zs).
  Proof.
    destruct HH as (?&?&?&?&?).
    eexists _, _; split.
    eapply List.interleave_rapp; eauto.
    split; eauto.
  Admitted.
  
  Lemma interleave_lkleene {T} {P Q : list T -> Prop} z zs
    (H : P^* z) (HH : interleave (P^* ) Q zs) : interleave (P^* ) Q (z++zs).
  Proof.
    destruct HH as (?&?&?&?&?).
    eexists _, _; split.
    eapply List.interleave_lapp; eauto.
    split; eauto.
  Admitted.

  Lemma interleave_rkleene_back {T} {P Q : list T -> Prop} z zs
    (H : Q^* z) (HH : interleave P (Q^* ) zs) : interleave P (Q^* ) (zs++z).
  Proof.
  Admitted.
  
  Lemma interleave_lkleene_back {T} {P Q : list T -> Prop} z zs
    (H : P^* z) (HH : interleave (P^* ) Q zs) : interleave (P^* ) Q (zs++z).
  Proof.
  Admitted.

  Definition interleave_rkleene_cons {T} {P Q} (z:T) zs H HH : interleave _ _ (cons _ _) :=
    @interleave_rkleene T P Q [z] zs H HH.
  Definition interleave_lkleene_cons {T} {P Q} (z:T) zs H HH : interleave _ _ (cons _ _):=
    @interleave_lkleene T P Q [z] zs H HH.

  Lemma interleave_kleene_l_app_r {T} (A B C : list T -> Prop) (bs cs : list T)
    (HB : TracePredicate.interleave (kleene A) B bs)
    (HC : TracePredicate.interleave (kleene A) C cs)
    : TracePredicate.interleave (kleene A) (B +++ C) (cs ++ bs).
  Admitted.
  (* TODO: how do I actually prove this in a loop *)

  Lemma interleave_exist_r {T V} P Q (t : list T) : (exist (fun v:V => P || Q v)) t -> (P || exist Q) t.
  Proof.
    cbv [exist].
    intros (?&?&?&?&?&?).
    eexists _, _; eauto.
  Qed.

  Lemma interleave_exist_l {T V} P Q (t : list T) : (exist (fun v:V => P v || Q)) t -> (exist P || Q) t.
  Proof.
    cbv [exist].
    intros (?&?&?&?&?&?).
    eexists _, _; eauto.
  Qed.

  Lemma app_exist_r {T V} P Q (t : list T) : (exist (fun v:V => P +++ Q v)) t <-> (P +++ exist Q) t.
  Admitted.

  Lemma app_exist_l {T V} P Q (t : list T) : (exist (fun v:V => P v +++ Q)) t <-> (exist P +++ Q) t.
  Admitted.
End TracePredicate.
Local Infix "||" := TracePredicate.interleave.

Require Import Kami.All.

Definition bits {w} : word w -> list bool. Admitted.
Lemma length_bits w x : List.length (@bits w x) = w. Admitted.
Lemma bits_nil x : @bits 0 x = nil.
Proof.
  pose proof length_bits x as H.
  destruct (bits x); [trivial | inversion H].
Qed.

Section Named.
  Context (name : string).
  Local Open Scope kami_action.
  Local Open Scope kami_expr.
  Local Notation "@^ x" := (name ++ "_" ++ x)%string (at level 0).

  Definition SPI := MODULE {
         Register @^"hack_for_sequential_semantics" : Bit 0 <- Default
    with Register @^"i"           : Bit 4 <- Default
    with Register @^"sck"         : Bool  <- Default
    with Register @^"tx"     : Bit 8 <- Default
    with Register @^"rx"     : Bit 8 <- Default
    with Register @^"rx_valid"    : Bool  <- Default
    
    with Rule @^"cycle" := (
      Write @^"hack_for_sequential_semantics" : Bit 0 <- $$(WO);
      Read sck <- @^"sck";
      Read i : Bit 4 <- @^"i";
      Read tx : Bit 8 <- @^"tx";
      If (*!*) #i == $$@natToWord 4 0 then Retv else (
        If (#sck) then (
          Write @^"sck" : Bool <- $$false;
          Call "PutSCK"($$false : Bool);
          Call "PutMOSI"((UniBit (TruncMsb 7 1) #tx) : Bit 1);
          Retv
        ) else (
          Read rx : Bit 8 <- @^"rx";
          Call miso : Bit 1 <- "GetMISO"();
          Write @^"rx" : Bit 8 <- BinBit (Concat 7 1) (UniBit (TruncLsb 7 1) #rx) #miso;
          Write @^"sck" : Bool <- $$true;
          Call "PutSCK"($$true : Bool);
          Call "PutMOSI"((UniBit (TruncMsb 7 1) #tx) : Bit 1);
          Write @^"tx" : Bit 8 <- BinBit (Concat 7 1) (UniBit (TruncLsb 7 1) #tx) $$(@ConstBit 1 $0);
          Write @^"rx_valid" <- #i == $$@natToWord 4 1;
          Write @^"i" <- #i - $1;
          Retv
        );
      Retv);

    Retv)
    
    with Method "write" (data : Bit 8) : Bool := (
      Write @^"hack_for_sequential_semantics" : Bit 0 <- $$(WO);
      Read i <- @^"i";
      If #i == $$@natToWord 4 0 then (
        Write @^"tx" : Bit 8 <- #data;
        Write @^"i" <- $$@natToWord 4 8;
        Write @^"rx_valid" <- $$false;
        Write @^"sck" <- $$true; (* not actually, just internal fiction to be consistent with the draining case *)
        Ret $$false
      ) else (
        Ret $$true
      ) as b;
      Ret #b
    )
    
    with Method "read" () : Bool := ( (* TODO return pair *)
      Write @^"hack_for_sequential_semantics" : Bit 0 <- $$(WO);
      Read rx_valid <- @^"rx_valid";
      If #rx_valid then (
        Read data : Bit 8 <- @^"rx";
        Write @^"rx_valid" <- $$false;
        Call "ReturnData"(#data : Bit 8);
        Ret $$false (* TODO: return (data, false) *)
      ) else (
        Call "ReturnData"($0 : Bit 8);
        Ret $$true
      ) as r;
      Ret #r
    )
  }.

  Definition cmd_write arg err := exist (fun r : RegsT =>
    eq [[(r, (Meth ("write", existT SignT (Bit 8, Bool) (arg, err)), @nil MethT))]]).
  Definition cmd_read ret err := exist (fun r : RegsT =>
    eq [[(r, (Meth ("read", existT SignT (Void, Bool) (wzero 0, err)), [("ReturnData", existT SignT (Bit 8, Void) (ret, WO))]))]]).
  Definition silent : list (list (RegsT * (RuleOrMeth * list MethT))) -> Prop :=
    exist (fun r : RegsT => eq [[(r, (Rle (name ++ "_cycle"), []))]]).

  Definition nop x := silent x \/ (exists arg, cmd_write arg true x) \/ (exists ret, cmd_read ret true x).
  
  Inductive p :=
  | getmiso (_ : forall miso : bool, p)
  | putsck (_ : bool) (_ : p)
  | putmosi (_ : word 1) (_ : p)

  | yield (_ : p)
  | ret (_ : word 8).

  Fixpoint xchg_prog (n : nat) : forall (tx : word 8) (rx : word 8), p :=
    match n with
    | O => fun _ rx => ret rx
    | S n => fun tx rx =>
      let mosi := split2 7 1 tx in
      putsck false (
      putmosi mosi (
      yield (
      getmiso (fun miso =>
      let rx := combine (WS miso WO) (split1 7 1 rx) in
      putsck true (
      putmosi mosi (
      let tx := combine (WS false WO) (split1 7 1 tx) in
      yield (
      @xchg_prog n tx rx
      )))))))
    end.

  Fixpoint interp (e : p) : list MethT -> word 8 -> list (list FullLabel) -> Prop :=
    match e with
    | getmiso k => fun l w => exist (fun miso => interp (k miso) (l++[("GetMISO", existT SignT (Void, Bit 1) (wzero 0, WS miso WO))]) w)
    | putsck sck k => fun l w => interp k (l++[("PutSCK", existT SignT (Bool, Void) (sck, wzero 0))]) w
    | putmosi mosi k => fun l w => interp k (l++[("PutMOSI", existT SignT (Bit 1, Void) (mosi, wzero 0))]) w
    | yield k => fun l w => exist (fun r => (eq [[(r, (Rle (name ++ "_cycle"), l))]] +++ interp k nil w))
    | ret w => fun l' w' t => w' = w /\ t = nil
    end.

  Definition spi_xchg tx rx := 
    cmd_write tx false +++
    interp (xchg_prog 8 tx (wzero 8)) nil rx +++
    maybe (cmd_read rx false).
  Definition spi_xchgs := kleene (exist (fun tx => (exist (fun rx => spi_xchg tx rx)))).
  Definition spec := TracePredicate.interleave (kleene nop) spi_xchgs.

  Definition enforce_regs (regs:RegsT) i sck tx rx rx_valid := regs =
    [
    (@^"hack_for_sequential_semantics", existT _ (SyntaxKind (Bit 0)) WO);
     (@^"i", existT _ (SyntaxKind (Bit 4)) i);
     (@^"sck", existT _ (SyntaxKind Bool) sck);
     (@^"tx", existT _ (SyntaxKind (Bit 8)) tx);
     (@^"rx", existT _ (SyntaxKind (Bit 8)) rx);
     (@^"rx_valid", existT _ (SyntaxKind Bool) rx_valid)
     ].

  Definition xchg_prog_sckfalse (n : nat) (tx : word 8) (rx : word 8) (mosi : word 1) : p :=
    getmiso (fun miso =>
    let rx := combine (WS miso WO) (split1 7 1 rx) in
    putsck true (
    putmosi mosi (
    let tx := combine (WS false WO) (split1 7 1 tx) in
    yield (
    @xchg_prog n tx rx)))).

  Definition xchg_prog_as_sckfalse (n : nat) (tx : word 8) (rx : word 8) :
    xchg_prog (S n) tx rx =
    let mosi := split2 7 1 tx in
    putsck false (
    putmosi mosi (
    yield (
    xchg_prog_sckfalse n tx rx mosi)))
    := eq_refl.

  Ltac solve_enforce_regs :=
    solve[cbv [doUpdRegs enforce_regs] in *; subst; clear;
    repeat match goal with
    | _ => progress discharge_string_dec
    | _ => progress cbn [fst snd]
    | |- context G [match ?x with _ => _ end] =>
       let X := eval hnf in x in
       progress change x with X
    | _ => progress (f_equal; [])
    | |- ?l = ?r =>
        let l := eval hnf in l in
        let r := eval hnf in r in
        progress change (l = r)
    | _ => exact eq_refl
    end].

  (* draining case only *)
  Goal forall s past,
    Trace SPI s past ->
    exists i sck tx rx rx_valid,
    enforce_regs s i sck tx rx rx_valid /\
    Logic.or
    (wordToNat i <> 0 /\
    rx_valid = false /\
    let i := wordToNat i in
    forall frx future,
    (if sck
    then TracePredicate.interleave (kleene nop) (interp (xchg_prog i tx rx) nil frx) future
    else TracePredicate.interleave (kleene nop) (interp (xchg_prog_sckfalse (pred i)  tx rx (split2 7 1 tx)) nil frx) future)
    -> TracePredicate.interleave (kleene nop) (spi_xchgs +++ exist (fun tx => cmd_write tx false +++ interp (xchg_prog 8 tx rx) nil frx)) (future ++ past))
    (
     rx_valid = true /\ wordToNat i = 0
     /\ TracePredicate.interleave (kleene nop) (spi_xchgs +++ exist (fun tx => cmd_write tx false +++ interp (xchg_prog 8 tx rx) nil rx)) past
    \/
     rx_valid = false /\  wordToNat i = 0 /\ spec past
    )
  .
  Proof.
    intros s past.
    pose proof eq_refl s as MARKER.
    induction 1 as [A B C D | regsBefore t regUpds regsAfter E _ IHTrace HStep K I].
    { subst. admit. }

    rename t into past.
    specialize (IHTrace eq_refl). destruct IHTrace as (i&sck&tx&rx&rx_valid&Hregs&IH).

    unshelve epose proof InvertStep (@Build_BaseModuleWf SPI _) _ _ _ HStep as HHS;
      clear HStep; [abstract discharge_wf|..|rename HHS into HStep].
    1,2,3: admit.

    destruct IH as [(Hi&Hrx_valid&IHTrace)|];
    repeat match goal with
      | _ => progress intros
      | _ => progress subst
      | _ => progress clean_hyp_step
      | _ => progress discharge_string_dec
      | _ => progress cbn [fst snd] in *
      | _ => progress cbn [Init.Nat.pred evalExpr evalBinBit evalUniBit evalConstT getBool isEq] in *
      | _ => progress cbv [enforce_regs] in *
      | K: UpdRegs _ _ ?z |- _ =>
          let H := fresh K in
          unshelve epose proof (NoDup_UpdRegs _ _ K); clear K; [> ..| progress subst z]
      | |- NoDup _ => admit
      | |- exists _ _ _ _ _, doUpdRegs _ _ = _ /\ _ =>
          eexists _, _, _, _, _; eapply conj; [> solve_enforce_regs| ]
      | |- context G [@cons ?T ?a ?b] =>
          assert_fails (idtac; match b with nil => idtac end);
          let goal := context G [@List.app T (@cons T a nil) b] in
          change goal
      | _ => progress rewrite ?app_assoc, ?app_nil_r
      | H : ?T -> _ |- _ => assert_succeeds (idtac; match type of T with Prop => idtac end); specialize (H ltac:(auto))
    end.

    all:
    repeat match goal with
      | |- _ /\ _ => split; try solve [auto 2]; (let n := numgoals in guard n <= 1)
    end.

    all : try (
      rename Hi into Hi'; destruct (wordToNat rv0) as [|?i] eqn:Hi; [>congruence|]; clear Hi').

    all: try
    match goal with
    | H: wordToNat ?x <> 0, G: getBool (isEq _ ?x ($0)%word) = true |- _ => exfalso; revert H; revert G; admit
    | H: wordToNat ?x = 0, G: getBool (isEq _ ?x ($0)%word) = false |- _ => exfalso; revert H; revert G; admit
    end.

    { (* i = 0 *)
      unshelve epose proof ((_ : forall x y, getBool (weq x y) = true -> x = y) _ _ H3); [>admit|].
      subst rv0.
      inversion Hi. }
    {
      left; split; [Lia.lia|].
      (* trace construction *)
      rename Hi into Hi'; destruct (wordToNat rv0) as [|?i] eqn:Hi; [>congruence|]; clear Hi'.
      cbn [Init.Nat.pred] in *.
      subst.
      split;trivial; [].
      intros frx future Hfuture.
      rewrite app_assoc.
      revert Hfuture; revert future; revert frx.
      intros; refine (IHTrace _ _ _); clear IHTrace; revert Hfuture; revert future; revert frx.

      rewrite xchg_prog_as_sckfalse; cbn zeta beta.

      intros.
      cbn [interp].
      eapply TracePredicate.interleave_exist_r; eexists.
      eapply TracePredicate.interleave_kleene_l_app_r; [|eassumption].
      eexists nil, _; split; [|split].
      { eapply List.interleave_nil_l. }
      { eapply kleene_nil. }
      cbv [List.app]. f_equal. f_equal. f_equal. f_equal.
      repeat f_equal.
      eapply f_equal.
      2:eapply f_equal.       
      1,2: rewrite word0, (word0 (wzero 0)); reflexivity. }

    destruct (weq rv0 $1); subst; cycle 1.
    {
      left.
      split. { admit. } (* word *)
      split. admit. (* word *)
      replace (wordToNat (wminus_simple rv0 $1)) with i in * by admit. (* word *)
      cbn [Init.Nat.pred] in *.
      intros frx future Hfuture__________________________________________________.
      rewrite app_assoc.
      revert Hfuture__________________________________________________; revert future; revert frx.
      intros; refine (IHTrace _ _ _); clear IHTrace; revert Hfuture__________________________________________________; revert future; revert frx.

      cbv [xchg_prog_sckfalse].
      intros.
      cbn [interp].
      eapply TracePredicate.interleave_exist_r; eexists.
      (* setoid_rewrite <-TracePredicate.app_exist_l. *) (* WHY does this fail? *)
      eapply TracePredicate.Proper_interleave_impl; [reflexivity|intros ? H; eapply TracePredicate.app_exist_l; eapply H|].
      eapply TracePredicate.interleave_kleene_l_app_r.
      {
        eexists nil, _; split; [|split].
        { eapply List.interleave_nil_l. }
        { (* kleene_nil *) admit. }
        eexists. cbv [List.app]. f_equal. f_equal. f_equal. f_equal.
        repeat f_equal.
        eapply f_equal.
        2:eapply f_equal.       
        3:eapply f_equal.       
        2,3:rewrite word0, (word0 (wzero 0)); reflexivity.
        instantiate (1:=whd mret). admit. (* forall x : word 1, WS (whd x) WO = x *)
      }
      replace (WS (whd mret) WO) with mret by admit (* word as above *).
      eassumption. }

    { right.
      replace i with 0 in * by admit; clear i.
      left.
      split. { exact eq_refl. }
      split. { exact eq_refl. }
      eapply IHTrace.

      cbn [pred]; cbv [xchg_prog_sckfalse].
      change (xchg_prog 0) with (fun _ : word 8 => ret); cbv beta.
      cbn [interp].
      eapply TracePredicate.interleave_exist_r; eexists.
      eapply TracePredicate.interleave_exist_r; eexists.
      eapply TracePredicate.Proper_interleave_impl; [eapply reflexivity| |].
      { intros ? H. eapply app_empty_r; [exact H|].
        split; trivial.
        instantiate (1:=whd mret).
        repeat f_equal.
        admit (* forall x : word 1, WS (whd x) WO = x *) . }
      eexists nil, _; split; [|split].
      { eapply List.interleave_nil_l. }
      { eapply kleene_nil. }
      cbn [List.app].
      repeat f_equal; eapply f_equal.
      { admit. (* forall x : word 1, WS (whd x) WO = x *) }
      1,2:rewrite word0, (word0 (wzero 0)); reflexivity. }

    5: { (* idle -> draining *)
      left.
      split.
      1:cbv; clear; congruence.
      split. solve[trivial].

      change (wordToNat $8) with 8.

      intros ? ? H.

      eapply TracePredicate.Proper_interleave_impl; [eapply reflexivity| |].
      { intros ? ?. eapply TracePredicate.app_exist_r; eassumption. }
      rewrite List.app_assoc.
      eapply TracePredicate.interleave_exist_r; eexists.
      eapply TracePredicate.interleave_kleene_l_app_r.
      { (* past *)
        cbv [spi_xchgs spi_xchg fst] in *.
        revert i0.
        admit.
      }
      eapply TracePredicate.interleave_kleene_l_app_r; [|exact H].
      eexists nil, _; split; [|split].
      { eapply List.interleave_nil_l. }
      { eapply kleene_nil. }
      cbv [cmd_write exist].
      eexists.
      exact eq_refl. }

    5: {
      right.
      right.
      split; trivial; [].
      split; trivial; [].
      cbv [spec spi_xchgs spi_xchg].

      assert ( HH:
      exists tx, TracePredicate.interleave (kleene nop) (spi_xchgs +++ cmd_write tx false +++ interp (xchg_prog 8 tx rv0) [] rv0) past
      ) by admit; destruct HH as [? HH].

      enough (
      exists tx0 rx,
TracePredicate.interleave (kleene nop)
  ((spi_xchgs +++ 
         cmd_write tx0 false +++ interp (xchg_prog 8 tx0 (wzero 8)) [] rx +++
         maybe (cmd_read rx false)))
  ([[([((name ++ "_hack_for_sequential_semantics")%string,
       existT (fullType type) (SyntaxKind Void) WO)] ++
      [((name ++ "_rx_valid")%string,
       existT (fullType type) (SyntaxKind Bool) false)],
     (Meth ("read", existT SignT (Void, Bool) (arg, false)),
     [("ReturnData", existT SignT (Bit 8, Void) (rv0, mret))]))]] ++ past)
     ) by admit.

     eexists ?[tx], ?[rx].
     refine (TracePredicate.interleave_rapp _ _ _ _); [|exact HH].

     enough ((cmd_read rv0 false)
       [[([((name ++ "_hack_for_sequential_semantics")%string,
        existT (fullType type) (SyntaxKind Void) WO)] ++
       [((name ++ "_rx_valid")%string,
        existT (fullType type) (SyntaxKind Bool) false)],
      (Meth ("read", existT SignT (Void, Bool) (arg, false)),
      [("ReturnData", existT SignT (Bit 8, Void) (rv0, mret))]))]]) by admit.

      cbv [cmd_read]. eexists. repeat f_equal.
      replace arg with (wzero 0) by admit. 2:replace mret with WO by admit. 1,2:solve[trivial].
    }

    5: { (* idle -> draining , COPYPASTE FROM ABOVE *)
      left.
      split.
      1:cbv; clear; congruence.
      split. solve[trivial].

      change (wordToNat $8) with 8.

      intros ? ? H.

      eapply TracePredicate.Proper_interleave_impl; [eapply reflexivity| |].
      { intros ? ?. eapply TracePredicate.app_exist_r; eassumption. }
      rewrite List.app_assoc.
      eapply TracePredicate.interleave_exist_r; eexists.
      eapply TracePredicate.interleave_kleene_l_app_r.
      { eassumption. }
      eapply TracePredicate.interleave_kleene_l_app_r; [|exact H].
      eexists nil, _; split; [|split].
      { eapply List.interleave_nil_l. }
      { eapply kleene_nil. }
      cbv [cmd_write exist].
      eexists.
      exact eq_refl. }

    3: { (* nop cycle, rx_valid = true *)
      right.
      left.
      repeat (split; trivial; [>]).
      eapply TracePredicate.interleave_lkleene; [|eassumption].
      eapply kleene_one.
      cbv [nop].
      left.
      cbv [silent].
      eexists.
      repeat f_equal.
    }

    3: { (* nop cycle, rx_valid = false *)
      right.
      right.
      repeat (split; trivial; [>]).
      eapply TracePredicate.interleave_lkleene; [|eassumption].
      eapply kleene_one.
      cbv [nop].
      left.
      cbv [silent].
      eexists.
      repeat f_equal.
    }

    1,2,3: (left + (right;left) + (right;right)); do 2 (split; trivial; []); intros.
    1,2: rewrite app_assoc; eapply IHTrace; clear IHTrace; destruct sck.
    1,2,3,4: (eapply TracePredicate.interleave_rkleene + eapply TracePredicate.interleave_lkleene_back); try eassumption; [].
    1,2,3,4 : eapply kleene_one; cbv [nop silent].
    all: try ((left + (right;left) + (right;right)); repeat eexists; solve[repeat f_equal]).
    {
      right; right.
      repeat eexists.
      repeat f_equal.
      1,2:eapply f_equal2; eauto.
    }
    {
      right.
      right.
      eexists.
      eexists.
      repeat f_equal.
      1,2:eapply f_equal2; eauto.
    }
    {
      eapply TracePredicate.interleave_lkleene; try eassumption; [].
      eapply kleene_one.
      right. right. eexists. eexists. repeat f_equal; eapply f_equal2; eauto.
    }


    Grab Existential Variables.
    all : try match goal with
      | |- NoDup _ => admit
          end.
  
Abort.

End Named.

(* scheduling order: cycle, read, write ? *)

  (* Notation "( x , y , .. , z )" := (existT _ .. (existT _ x y) .. z) : core_scope. *)
