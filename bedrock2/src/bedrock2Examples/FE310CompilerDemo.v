From coqutil Require Import sanity.
Local Unset Universe Minimization ToSet.
Require Import Coq.Strings.String.
Require Import coqutil.Z.Lia.
Require Import Coq.ZArith.BinInt.
Require Import bedrock2.Syntax.

Definition MMIOAction: Type := String.string.
Notation MMInput := "MMInput"%string.
Notation MMOutput := "MMOutput"%string.

From coqutil.Map Require SortedListWord SortedListString Z_keyed_SortedListMap Empty_set_keyed_map.
From coqutil Require Import Word.Interface Word.Naive String.
Require Import coqutil.Word.Bitwidth32.
Require Import bedrock2.Semantics.
Import List.ListNotations.

Definition otp_base   := 0x00020000. Definition otp_pastend   := 0x00022000.
Definition hfrosccfg  := 0x10008000.
Definition gpio0_base := 0x10012000. Definition gpio0_pastend := 0x10013000.
Definition uart0_base := 0x10013000. Definition uart0_pastend := 0x10014000.
Definition uart0_rxdata := 0x10013004. Definition uart0_txdata  := 0x10013000.

#[global] Instance word: word.word 32 := Naive.word32.
#[global] Instance mem: Interface.map.map word Byte.byte := SortedListWord.map _ _.
#[global] Instance locals: Interface.map.map String.string word := SortedListString.map _.
#[global] Instance env: Interface.map.map String.string (list String.string * list String.string * cmd) :=
  SortedListString.map _.

#[global] Instance ext_spec: ExtSpec :=
  fun t mGive action args post =>
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
    end%list%bool.


Require Import bedrock2.NotationsCustomEntry.

Definition swap_chars_over_uart: cmd :=
  let prev : String.string := "prev"%string in
  let rx : String.string := "rx"%string in
  let tx : String.string := "tx"%string in
  let running : String.string := "running"%string in

  let bit31 : String.string := "bit31"%string in
  let one : String.string := "one"%string in
  let dot : String.string := "dot"%string in
  let uart_tx : String.string := "uart_tx"%string in
  let polling : String.string := "polling"%string in

  let MMIOREAD  := MMInput in (* COQBUG(9514) ... *)
  let MMIOWRITE := MMOutput in
  let hfrosccfg := hfrosccfg in
  let uart0_base := uart0_base in
  let gpio0_base := gpio0_base in

  bedrock_func_body:(
    (* ring oscillator: enable, trim to 72MHZ using value from OTP, divider=0+1 *)
    io! rx = $MMIOREAD (coq:(0x00021fec));
    output! $MMIOWRITE($hfrosccfg, coq:(2^30) | (rx & coq:(2^5-1)) << $16);
    coq:(cmd.unset rx);

    one = $1;
    output! $MMIOWRITE(coq:(uart0_base + 0x018), $624); (* --baud=115200 # = 72MHz/(0+1)/(624+1) *)
    output! $MMIOWRITE(coq:(uart0_base + 0x008), one); (* tx enable *)
    output! $MMIOWRITE(coq:(uart0_base + 0x00c), one); (* rx enable *)
    output! $MMIOWRITE(coq:(gpio0_base + 0x038), coq:(2^17 + 2^16)); (* pinmux uart tx rx *)

    dot = $46;
    prev = dot;
    running = one-dot;
    while (running) {
      bit31 = coq:(2^31);
      rx = bit31;
      polling = one-dot;
      while (polling & rx & bit31) { io! rx = $MMIOREAD(coq:(uart0_base + 0x004)); polling = polling-one };

      uart_tx = coq:(uart0_base + 0x000);
      tx = bit31;
      polling = one-dot;
      while (polling & tx & bit31) { io! tx = $MMIOREAD(uart_tx); polling = polling-one };
      output! $MMIOWRITE(uart_tx, prev);

      prev = rx;
      running = running - one;
      if (prev == dot) { running = running ^ running };

      coq:(cmd.unset uart_tx); coq:(cmd.unset rx); coq:(cmd.unset tx); coq:(cmd.unset bit31); coq:(cmd.unset polling)
    }
  ).

(*
Compute swap_chars_over_uart.
*)

Require Import bedrock2.ProgramLogic coqutil.Map.Interface.
Import Coq.Lists.List. Import ListNotations.

Local Opaque Word.Interface.word.of_Z.
Module Z.
  Lemma land_nonzero a b : Z.land a b <> 0 -> a <> 0 /\ b <> 0.
  Proof.
    destruct (Z.eq_dec a 0), (Z.eq_dec b 0); subst;
      repeat rewrite ?Z.land_0_r, ?Z.land_0_l; blia.
  Qed.
End Z.

From coqutil Require Import Z.div_mod_to_equations.

Ltac t :=
  match goal with
  | |- WeakestPrecondition.cmd _ (cmd.interact _ _ _) _ _ _ _ => eexists; split; [solve[repeat straightline]|]
  | |- map.split _ _ _ => eapply Properties.map.split_empty_r; reflexivity
  | H: map.of_list_zip ?ks ?vs = Some ?m |- _ => cbn in H; injection H; clear H; intro H; symmetry in H
  | H: map.putmany_of_list_zip ?ks ?vs ?m0 = Some ?m |- _ => cbn in H; injection H; clear H; intro H; symmetry in H
  | _ => straightline
  | |- map.of_list_zip _ _ = Some _ => exact eq_refl
  | |- map.putmany_of_list_zip _ _ _ = Some _ => exact eq_refl
  | |- exists _, _ => eexists
  | |- _ /\ _ => split
  | |- well_founded _ => eapply Properties.word.well_founded_lt_unsigned
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
                                            (blia || clear; cbv; split; congruence)
           end]
  | _ => solve [trivial]
  end.

(* TODO COQBUG? why does typeclass search not succeed here?
   It used to work with primitive projections on *)
Local Instance mapok: map.ok mem := SortedListWord.ok Naive.word32 _.

Local Instance wordok: word.ok word := Naive.word32_ok.

Lemma swap_chars_over_uart_correct m :
  WeakestPrecondition.cmd (fun _ _ _ _ _ => False) swap_chars_over_uart nil m map.empty
  (fun t m l => True).
Proof.
  repeat t.
  eexists _, _, (fun v t _ l => exists p, map.of_list_zip ["running"; "prev"; "one"; "dot"]%string [v; p; word.of_Z(1); word.of_Z(46)] = Some l ); repeat t.
  eexists _, _, (fun v t _ l => exists rxv, map.putmany_of_list_zip ["polling"; "rx"]%string [v; rxv] l0 = Some l); repeat t.
  eexists _, _, (fun v t _ l => exists txv, map.putmany_of_list_zip ["polling"; "tx"]%string [v; txv] l0 = Some l); repeat t.
  eexists; split; repeat t.
Defined.


Import List. Import ListNotations.
Fixpoint echo_server_spec (t : trace) (output_to_explain : option word) : Prop := let spec := echo_server_spec in
  match t with
  | nil => output_to_explain = None
  | (_, MMInput, [addr], (_, [value]))::trace =>
    if (word.unsigned addr =? uart0_base + 0x004) && (word.unsigned (word.and value (word.of_Z (2 ^ 31))) =? 0)
    then output_to_explain = Some value /\ spec trace None
    else spec trace output_to_explain
  | (_, MMOutput, [addr; value], (_, []))::trace => (
    if word.unsigned addr =? hfrosccfg
      then Z.testbit (word.unsigned value) 30 = true /\ spec trace output_to_explain else
    if word.unsigned addr =? uart0_base + 0x018
      then word.unsigned value = 624 /\ spec trace output_to_explain else
    if (word.unsigned addr =? uart0_base + 0x000)
    then match trace with
         | (_, MMInput, [addr'], (_, [value']))::trace =>
           word.unsigned addr' = uart0_base + 0x000 /\
           word.unsigned (word.and value' (word.of_Z (2 ^ 31))) = 0 /\
           output_to_explain = None /\ spec trace (Some value)
         | _ => False end else
    spec trace output_to_explain
    )
  | _ => False
  end%bool%list.

Definition echo_server: cmd :=
  let rx : String.string := "rx"%string in
  let tx : String.string := "tx"%string in
  let running : String.string := "running"%string in

  let bit31 : String.string := "bit31"%string in
  let one : String.string := "one"%string in
  let dot : String.string := "dot"%string in
  let uart_tx : String.string := "uart_tx"%string in
  let polling : String.string := "polling"%string in

  let MMIOREAD  := MMInput in (* COQBUG(9514) ... *)
  let MMIOWRITE := MMOutput in
  let hfrosccfg := hfrosccfg in
  let uart0_base := uart0_base in
  let gpio0_base := gpio0_base in

  bedrock_func_body:(
    (* ring oscillator: enable, trim to 72MHZ using value from OTP, divider=0+1 *)
    io! rx = $MMIOREAD (coq:(0x00021fec));
    output! $MMIOWRITE($hfrosccfg, coq:(2^30) | (rx & coq:(2^5-1)) << $16);
    coq:(cmd.unset rx);

    one = $1;
    output! $MMIOWRITE(coq:(uart0_base + 0x018), $624); (* --baud=115200 # = 72MHz/(0+1)/(624+1) *)
    output! $MMIOWRITE(coq:(uart0_base + 0x008), one); (* tx enable *)
    output! $MMIOWRITE(coq:(uart0_base + 0x00c), one); (* rx enable *)
    output! $MMIOWRITE(coq:(gpio0_base + 0x038), coq:(2^17 + 2^16)); (* pinmux uart tx rx *)

    running = $-1;
    while (running) {
      bit31 = coq:(2^31);
      rx = bit31;
      polling = $-1;
      while (polling & rx & bit31) { io! rx = $MMIOREAD(coq:(uart0_base + 0x004)); polling = polling-one };
      if (rx & bit31) { coq:(cmd.skip) } else {
        uart_tx = coq:(uart0_base + 0x000);
        tx = bit31;
        polling = $-1;
        while (polling & tx & bit31) { io! tx = $MMIOREAD(uart_tx); polling = polling-one };
        output! $MMIOWRITE(uart_tx, tx)
      };
      running = running - one;
      coq:(cmd.unset uart_tx); coq:(cmd.unset rx); coq:(cmd.unset tx); coq:(cmd.unset bit31); coq:(cmd.unset polling)
    }
  ).

Lemma echo_server_correct m :
  WeakestPrecondition.cmd (fun _ _ _ _ _ => False) echo_server nil m map.empty
  (fun t m l => echo_server_spec t None).
Proof.
  repeat t.
  eexists _, _, (fun v t _ l => map.of_list_zip ["running"; "one"]%string [v; word.of_Z(1)] = Some l /\ echo_server_spec t None ); repeat t.
  { repeat split. admit. (* hfrosccfg*) }
  eexists _, _, (fun v t _ l => exists rxv, map.putmany_of_list_zip ["polling"; "rx"]%string [v; rxv] l0 = Some l /\
                                            if Z.eq_dec (word.unsigned (word.and rxv (word.of_Z (2^31)))) 0
                                            then echo_server_spec t (Some rxv)
                                            else echo_server_spec t None); repeat t.
  { match goal with |- if ?D then _ else _ => destruct D end; cbn [Z.eq_dec echo_server_spec ].
    all: try rewrite e, ?Bool.andb_true_r.
    all: repeat match goal with |- if _ then ?A else ?B => change A end.
   (*
    { split; auto. destruct (Z.eq_dec (word.unsigned (word.and x (word.of_Z (2 ^ 31))))) in H2; trivial.
      exfalso; revert H1 e0; clear. subst b v3. admit. }
    { rewrite (proj2 (Z.eqb_neq _ 0)), Bool.andb_false_r by eassumption.
      destruct (Z.eq_dec (word.unsigned (word.and x (word.of_Z (2 ^ 31))))) in H2; trivial.
      exfalso; revert H1 e; clear. subst b v3. admit. } }
  eexists; split; repeat t.
  { destruct (Z.eq_dec (word.unsigned (word.and x (word.of_Z (2 ^ 31))))) in H2; trivial.
    exfalso; revert H1 e; clear. subst b v3. admit. }
  eexists _, _, (fun v t _ l => exists txv, map.putmany_of_list_zip [polling; tx] [v; txv] l0 = Some l /\
                                            if Z.eq_dec (word.unsigned (word.and txv (word.of_Z (2^31)))) 0
                                            then echo_server_spec ((m, MMInput, [word.of_Z (uart0_base + 0x000)], (m, [txv]))::t) None
                                            else echo_server_spec t (Some x)); repeat t.
  { subst v3.
    rewrite word.unsigned_and, ?word.unsigned_of_Z by admit; cbn.
    destruct (Z.eq_dec (word.unsigned (word.and x (word.of_Z (2 ^ 31))))) in H2; (trivial||contradiction). }
  { admit. }
  { admit. }
  *)
Abort.
