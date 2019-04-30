From coqutil Require Import sanity.
Local Unset Universe Minimization ToSet.
Require Import Coq.Strings.String.
Require Import coqutil.Z.Lia.
Require Import Coq.ZArith.BinInt.
Require Import bedrock2.Syntax.

Definition MMIOAction: Type := String.string.
Notation MMInput := "MMInput"%string.
Notation MMOutput := "MMOutput"%string.

Local Instance syntax_parameters : Syntax.parameters := {|
  varname := Z;
  funname := String.string;
  actname := MMIOAction;
|}.





From coqutil.Map Require SortedListWord SortedListString Z_keyed_SortedListMap Empty_set_keyed_map.
From coqutil Require Import Word.Interface Word.Naive Z.HexNotation String.
Require Import bedrock2.Semantics.
Import List.ListNotations.

Definition otp_base   := Ox"0x00020000". Definition otp_pastend   := Ox"0x00022000".
Definition hfrosccfg  := Ox"10008000".
Definition gpio0_base := Ox"0x10012000". Definition gpio0_pastend := Ox"0x10013000".
Definition uart0_base := Ox"0x10013000". Definition uart0_pastend := Ox"0x10014000".
Definition uart0_rxdata := Ox"10013004". Definition uart0_txdata  := Ox"10013000".

Local Instance parameters : parameters :=
  let word := Naive.word32 in
  let byte := Naive.word8 in
  {|
  width := 32;
  syntax := syntax_parameters;
  mem := SortedListWord.map _ _;
  locals := Z_keyed_SortedListMap.Zkeyed_map _;
  funname_env := SortedListString.map;
  funname_eqb := String.eqb;
  ext_spec t mGive action args post :=
    mGive = Map.Interface.map.empty /\
    match action, List.map word.unsigned args with
    | MMInput, [addr] => (
      if addr =? hfrosccfg                                then True else
      if (  otp_base <=? addr) && (addr <?   otp_pastend) then True else
      if (gpio0_base <=? addr) && (addr <? gpio0_pastend) then True else
      if (uart0_base <=? addr) && (addr <? uart0_pastend) then True else
      False )
      /\ addr mod 4 = 0
      /\ forall v, post Map.Interface.map.empty [v]
    | MMOutput, [addr; value] => (
      if addr =? hfrosccfg                                then True else
      if (gpio0_base <=? addr) && (addr <? gpio0_pastend) then True else
      if (uart0_base <=? addr) && (addr <? uart0_pastend) then True else
      False )
      /\ addr mod 4 = 0
      /\ post Map.Interface.map.empty []
    | _, _ =>
      False
    end%list%bool;
  |}.




Require Import bedrock2.NotationsCustomEntry.
(* both variable names and literals are Z in this file, disambiguate... *)
Local Coercion var {p} (x : @varname p) : expr := expr.var x. (* COQBUG(4593) *)
Local Coercion literal (x : Z) : expr := expr.literal x.

Definition swap_chars_over_uart: cmd :=
  let prev : varname := 1%Z in
  let rx : varname := 2%Z in
  let tx : varname := 3%Z in
  let running : varname := 4%Z in

  let bit31 : varname := 5%Z in
  let one : varname := 6%Z in
  let dot : varname := 7%Z in
  let uart_tx : varname := 8%Z in
  let polling : varname := 9%Z in

  let MMIOREAD  := MMInput in (* COQBUG(9514) ... *)
  let MMIOWRITE := MMOutput in
  let hfrosccfg := hfrosccfg in
  let uart0_base := uart0_base in
  let gpio0_base := gpio0_base in

  bedrock_func_body:(
    (* ring oscillator: enable, trim to 72MHZ using value from OTP, divider=0+1 *)
    io! rx = MMIOREAD (constr:(Ox"0x00021fec"));
    output! MMIOWRITE(hfrosccfg, constr:(2^30) | (rx & constr:(2^5-1)) << constr:(16));
    constr:(cmd.unset rx);

    one = (constr:(1));
    output! MMIOWRITE(constr:(uart0_base + Ox"018"), constr:(624)); (* --baud=115200 # = 72MHz/(0+1)/(624+1) *)
    output! MMIOWRITE(constr:(uart0_base + Ox"008"), one); (* tx enable *)
    output! MMIOWRITE(constr:(uart0_base + Ox"00c"), one); (* rx enable *)
    output! MMIOWRITE(constr:(gpio0_base + Ox"038"), constr:(2^17 + 2^16)); (* pinmux uart tx rx *)

    dot = (constr:(46));
    prev = (dot);
    running = (one-dot);
    while (running) {
      bit31 = (constr:(2^31));
      rx = (bit31);
      polling = (one-dot);
      while (polling & rx & bit31) { io! rx = MMIOREAD(constr:(uart0_base + Ox"004")); polling = (polling-one) };

      uart_tx = (constr:(uart0_base + Ox"000"));
      tx = (bit31);
      polling = (one-dot);
      while (polling & tx & bit31) { io! tx = MMIOREAD(uart_tx); polling = (polling-one) };
      output! MMIOWRITE(uart_tx, prev);

      prev = (rx);
      running = (running - one);
      if (prev == dot) { running = (running ^ running) };

      constr:(cmd.unset uart_tx); constr:(cmd.unset rx); constr:(cmd.unset tx); constr:(cmd.unset bit31); constr:(cmd.unset polling)
    }
  ).

(*
Compute swap_chars_over_uart.
*)

Require Import bedrock2.ProgramLogic coqutil.Map.Interface.
Import Coq.Lists.List. Import ListNotations.

Local Opaque word.of_Z.
Module Z.
  Lemma land_nonzero a b : Z.land a b <> 0 -> a <> 0 /\ b <> 0.
  Proof.
    destruct (Z.eq_dec a 0), (Z.eq_dec b 0); subst;
      repeat rewrite ?Z.land_0_r, ?Z.land_0_l; bomega.
  Qed.
End Z.

Module word.
  Lemma well_founded_lt_unsigned : well_founded (fun a b : word => word.unsigned a < word.unsigned b).
  Proof.
    simple refine (Wf_nat.well_founded_lt_compat _ (fun x => Z.to_nat (word.unsigned x)) _ _).
    cbv beta; intros a b H.
    epose proof proj1 (Properties.word.unsigned_range a); epose proof proj1 (Properties.word.unsigned_range b).
    eapply Znat.Z2Nat.inj_lt; trivial.
    Unshelve.
    all: unfold word; typeclasses eauto.
  Qed.
End word.

From coqutil Require Import Z.div_mod_to_equations.

Ltac t :=
  match goal with
  | |- WeakestPrecondition.cmd _ (cmd.interact _ _ _) _ _ _ _ => eexists; split; [solve[repeat straightline]|]
  | |- map.split _ _ _ => eapply Properties.map.split_empty_r; reflexivity
  | H: map.of_list ?ks ?vs = Some ?m |- _ => cbn in H; injection H; clear H; intro H; symmetry in H
  | H: map.putmany_of_list ?ks ?vs ?m0 = Some ?m |- _ => cbn in H; injection H; clear H; intro H; symmetry in H
  | _ => straightline
  | |- map.of_list _ _ = Some _ => exact eq_refl
  | |- map.putmany_of_list _ _ _ = Some _ => exact eq_refl
  | |- exists _, _ => eexists
  | |- _ /\ _ => split
  | |- well_founded _ => eapply word.well_founded_lt_unsigned
  | |- ext_spec _ _ _ _ _ => refine (conj eq_refl (conj I (conj eq_refl _)))
  | |- _ < _ => solve[
    repeat match goal with
           | x := _ |- _ => subst x
           | H: _ |- _ => progress rewrite ?Properties.word.unsigned_and_nowrap, ?Properties.word.wrap_unsigned in H; unfold word.wrap in H
           | _ => progress repeat (rewrite Properties.word.unsigned_xor_nowrap, Z.lxor_nilpotent)
           | H: Z.land _ _ <> 0 |- _ => unshelve eapply Z.land_nonzero in H; destruct H; []
           | |- _ < word.unsigned ?x => pose proof Properties.word.unsigned_range x;
                                          repeat (rewrite ?word.unsigned_sub, ?word.unsigned_of_Z || unfold word.wrap);
                                          repeat rewrite ?Z.mod_small;
                                            (bomega || clear; cbv; split; congruence)
           end]
  | _ => solve [trivial]
  end.

(* TODO COQBUG? why does typeclass search not succeed here?
   It used to work with primitive projections on *)
Local Instance mapok: map.ok mem := SortedListWord.ok Naive.word32 (@rep 8).

Local Instance wordok: word.ok word := Naive.word32_ok.

Lemma swap_chars_over_uart_correct m :
  WeakestPrecondition.cmd (fun _ _ _ _ _ => False) swap_chars_over_uart nil m map.empty
  (fun t m l => True).
Proof.
  repeat t.


  refine (
  let prev : varname := 1%Z in
  let rx : varname := 2%Z in
  let tx : varname := 3%Z in
  let running : varname := 4%Z in

  let bit31 : varname := 5%Z in
  let one : varname := 6%Z in
  let dot : varname := 7%Z in
  let uart_tx : varname := 8%Z in
  let polling : varname := 9%Z in

  _).
  (* SearchAbout I (* ANOMALY *) *)
  eexists _, _, (fun v t _ l => exists p, map.of_list [running; prev; one; dot] [v; p; word.of_Z(1); word.of_Z(46)] = Some l ); repeat t.
  eexists _, _, (fun v t _ l => exists rxv, map.putmany_of_list [polling; rx] [v; rxv] l0 = Some l); repeat t.
  eexists _, _, (fun v t _ l => exists txv, map.putmany_of_list [polling; tx] [v; txv] l0 = Some l); repeat t.
  eexists; split; repeat t.
Defined.
















Import List. Import ListNotations.
Fixpoint echo_server_spec (t : trace) (output_to_explain : option word) : Prop := let spec := echo_server_spec in
  match t with
  | nil => output_to_explain = None
  | (_, MMInput, [addr], (_, [value]))::trace =>
    if (word.unsigned addr =? uart0_base + Ox"004") && (word.unsigned (word.and value (word.of_Z (2 ^ 31))) =? 0)
    then output_to_explain = Some value /\ spec trace None
    else spec trace output_to_explain
  | (_, MMOutput, [addr; value], (_, []))::trace => (
    if word.unsigned addr =? hfrosccfg
      then Z.testbit (word.unsigned value) 30 = true /\ spec trace output_to_explain else
    if word.unsigned addr =? uart0_base + Ox"018"
      then word.unsigned value = 624 /\ spec trace output_to_explain else
    if (word.unsigned addr =? uart0_base + Ox"000")
    then match trace with
         | (_, MMInput, [addr'], (_, [value']))::trace =>
           word.unsigned addr' = uart0_base + Ox"000" /\
           word.unsigned (word.and value' (word.of_Z (2 ^ 31))) = 0 /\
           output_to_explain = None /\ spec trace (Some value)
         | _ => False end else
    spec trace output_to_explain
    )
  | _ => False
  end%bool%list.

Definition echo_server: cmd :=
  let rx : varname := 2%Z in
  let tx : varname := 3%Z in
  let running : varname := 4%Z in

  let bit31 : varname := 5%Z in
  let one : varname := 6%Z in
  let dot : varname := 7%Z in
  let uart_tx : varname := 8%Z in
  let polling : varname := 9%Z in

  let MMIOREAD  := MMInput in (* COQBUG(9514) ... *)
  let MMIOWRITE := MMOutput in
  let hfrosccfg := hfrosccfg in
  let uart0_base := uart0_base in
  let gpio0_base := gpio0_base in

  bedrock_func_body:(
    (* ring oscillator: enable, trim to 72MHZ using value from OTP, divider=0+1 *)
    io! rx = MMIOREAD (constr:(Ox"0x00021fec"));
    output! MMIOWRITE(hfrosccfg, constr:(2^30) | (rx & constr:(2^5-1)) << constr:(16));
    constr:(cmd.unset rx);

    one = (constr:(1));
    output! MMIOWRITE(constr:(uart0_base + Ox"018"), constr:(624)); (* --baud=115200 # = 72MHz/(0+1)/(624+1) *)
    output! MMIOWRITE(constr:(uart0_base + Ox"008"), one); (* tx enable *)
    output! MMIOWRITE(constr:(uart0_base + Ox"00c"), one); (* rx enable *)
    output! MMIOWRITE(constr:(gpio0_base + Ox"038"), constr:(2^17 + 2^16)); (* pinmux uart tx rx *)

    running = (constr:(-1));
    while (running) {
      bit31 = (constr:(2^31));
      rx = (bit31);
      polling = (constr:(-1));
      while (polling & rx & bit31) { io! rx = MMIOREAD(constr:(uart0_base + Ox"004")); polling = (polling-one) };
      if (rx & bit31) { constr:(cmd.skip) } else {
        uart_tx = (constr:(uart0_base + Ox"000"));
        tx = (bit31);
        polling = (constr:(-1));
        while (polling & tx & bit31) { io! tx = MMIOREAD(uart_tx); polling = (polling-one) };
        output! MMIOWRITE(uart_tx, tx)
      };
      running = (running - one);
      constr:(cmd.unset uart_tx); constr:(cmd.unset rx); constr:(cmd.unset tx); constr:(cmd.unset bit31); constr:(cmd.unset polling)
    }
  ).

Lemma echo_server_correct m :
  WeakestPrecondition.cmd (fun _ _ _ _ _ => False) echo_server nil m map.empty
  (fun t m l => echo_server_spec t None).
Proof.
  repeat t.

  refine (
  let prev : varname := 1%Z in
  let rx : varname := 2%Z in
  let tx : varname := 3%Z in
  let running : varname := 4%Z in

  let bit31 : varname := 5%Z in
  let one : varname := 6%Z in
  let dot : varname := 7%Z in
  let uart_tx : varname := 8%Z in
  let polling : varname := 9%Z in

  _).
  (* SearchAbout I (* ANOMALY *) *)

  eexists _, _, (fun v t _ l => map.of_list [running; one] [v; word.of_Z(1)] = Some l /\ echo_server_spec t None ); repeat t.
  { repeat split. admit. (* hfrosccfg*) }
  eexists _, _, (fun v t _ l => exists rxv, map.putmany_of_list [polling; rx] [v; rxv] l0 = Some l /\
                                            if Z.eq_dec (word.unsigned (word.and rxv (word.of_Z (2^31)))) 0
                                            then echo_server_spec t (Some rxv)
                                            else echo_server_spec t None); repeat t.
  { match goal with |- if ?D then _ else _ => destruct D end; cbn [Z.eq_dec echo_server_spec ].
    all: try rewrite e, ?Bool.andb_true_r.
    all: repeat match goal with |- if _ then ?A else ?B => change A end.
    { split; auto. destruct (Z.eq_dec (word.unsigned (word.and x (word.of_Z (2 ^ 31))))) in H2; trivial.
      exfalso; revert H1 e0; clear. subst b v3. admit. }
    { rewrite (proj2 (Z.eqb_neq _ 0)), Bool.andb_false_r by eassumption.
      destruct (Z.eq_dec (word.unsigned (word.and x (word.of_Z (2 ^ 31))))) in H2; trivial.
      exfalso; revert H1 e; clear. subst b v3. admit. } }
  eexists; split; repeat t.
  { destruct (Z.eq_dec (word.unsigned (word.and x (word.of_Z (2 ^ 31))))) in H2; trivial.
    exfalso; revert H1 e; clear. subst b v3. admit. }
  eexists _, _, (fun v t _ l => exists txv, map.putmany_of_list [polling; tx] [v; txv] l0 = Some l /\
                                            if Z.eq_dec (word.unsigned (word.and txv (word.of_Z (2^31)))) 0
                                            then echo_server_spec ((m, MMInput, [word.of_Z (uart0_base + Ox"000")], (m, [txv]))::t) None
                                            else echo_server_spec t (Some x)); repeat t.
  { subst v3.
    rewrite word.unsigned_and, ?word.unsigned_of_Z by admit; cbn.
    destruct (Z.eq_dec (word.unsigned (word.and x (word.of_Z (2 ^ 31))))) in H2; (trivial||contradiction). }
  { admit. }
  { admit. }
Abort.
