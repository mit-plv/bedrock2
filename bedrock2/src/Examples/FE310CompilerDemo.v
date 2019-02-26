From coqutil Require Import sanity.
Local Unset Universe Minimization ToSet.
Require Import Coq.ZArith.BinInt.
Require Import bedrock2.Syntax.

Definition MMIOAction: Type := bool.
Definition MMInput: MMIOAction := false.
Definition MMOutput: MMIOAction := true.

Local Instance syntax_parameters : Syntax.parameters := {|
  varname := Z;
  funname := Empty_set;
  actname := MMIOAction;
|}.





From coqutil.Map Require SortedListWord Z_keyed_SortedListMap Empty_set_keyed_map.
From coqutil Require Import Word.Interface Word.Naive Z.HexNotation String.
Require Import bedrock2.Semantics.
Import List.ListNotations.

Definition otp_base   := Ox"0x00020000". Definition otp_pastend   := Ox"0x00022000".
Definition hfrosccfg  := Ox"10008000".
Definition gpio0_base := Ox"0x10012000". Definition gpio0_pastend := Ox"0x10013000".
Definition uart0_base := Ox"0x10013000". Definition uart0_pastend := Ox"0x10014000".
Definition uart0_rxdata := Ox"10013004". Definition uart0_txdata  := Ox"10013000".

Local Instance parameters : parameters :=
  let word := Word.Naive.word 32 eq_refl in
  let byte := Word.Naive.word 8 eq_refl in
  {|
  width := 32;
  syntax := syntax_parameters;
  mem := SortedListWord.map _ _;
  locals := Z_keyed_SortedListMap.Zkeyed_map _;
  funname_env := Empty_set_keyed_map.map;
  funname_eqb := fun _ _ => true;
  ext_spec t m action args post :=
    match action, List.map word.unsigned args with
    | MMInput, [addr] => (
      if addr =? hfrosccfg                                then True else
      if (  otp_base <=? addr) && (addr <?   otp_pastend) then True else
      if (gpio0_base <=? addr) && (addr <? gpio0_pastend) then True else
      if (uart0_base <=? addr) && (addr <? uart0_pastend) then True else
      False )
      /\ addr mod 4 = 0
      /\ forall v, post m [v]
    | MMOutput, [addr; value] => (
      if addr =? hfrosccfg                                then True else
      if (gpio0_base <=? addr) && (addr <? gpio0_pastend) then True else
      if (uart0_base <=? addr) && (addr <? uart0_pastend) then True else
      False )
      /\ addr mod 4 = 0
      /\ post m []
    | _, _ =>
      False
    end%list%bool;
  |}.
(* hfrosccfg: Z.testbit value 30 = true  *)





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
      while (running & rx & bit31) { io! rx = MMIOREAD(constr:(uart0_base + Ox"004")); running = (running-one) };

      uart_tx = (constr:(uart0_base + Ox"000"));
      tx = (bit31);
      while (running & tx & bit31) { io! tx = MMIOREAD(uart_tx); running = (running-one) };
      output! MMIOWRITE(uart_tx, prev);

      prev = (rx);
      running = (running - one);
      if (prev == dot) { running = (running ^ running) };

      constr:(cmd.unset uart_tx); constr:(cmd.unset rx); constr:(cmd.unset tx); constr:(cmd.unset bit31)
    }
  ).

(*
Compute swap_chars_over_uart.
*)

Require Import bedrock2.ProgramLogic coqutil.Map.Interface.
Import Coq.Lists.List. Import ListNotations.

Definition invert_Some {A} (x : option A)
  : match x with Some _ => A | None => True end :=
    match x with Some x => x | None => I end.
Lemma swap_chars_over_uart_correct m :
  WeakestPrecondition.cmd (Empty_set_rect _) swap_chars_over_uart nil m map.empty
  (fun t m l => True).
Proof.
  repeat (straightline || refine (conj I (conj eq_refl _))).
  cbv [WeakestPrecondition.cmd_body].

  refine (
  let prev : varname := 1%Z in
  let rx : varname := 2%Z in
  let tx : varname := 3%Z in
  let running : varname := 4%Z in

  let bit31 : varname := 5%Z in
  let one : varname := 6%Z in
  let dot : varname := 7%Z in
  let uart_tx : varname := 8%Z in

  _).

  let keys := eval cbv in [running; prev; one; dot] in
  eexists Z, _, (fun v t _ l => exists p, map.of_list keys [word.of_Z v; p; word.of_Z(1); word.of_Z(46)] = Some l ).
  split; [unshelve eapply (Z.lt_wf 0)|].
  split.
  { eexists. eexists. cbn. reflexivity. }
  { intros V t ? ? H.
    destruct H. cbn in H. injection H; clear H; intro H; symmetry in H.
    repeat straightline.
    split; repeat straightline.
    (* FIXME: inner loops do not terminate intrinsically *)
    admit. }
Abort.