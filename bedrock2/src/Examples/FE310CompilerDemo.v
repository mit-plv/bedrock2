Require Import Coq.ZArith.BinInt.
Require Import bedrock2.Syntax.

(* Require Import riscv.MMIOTrace. *)
(* -*- coq-prog-args: ("-Q" "/home/fiat/plv/bedrock2/deps/riscv-coq/src" "riscv"); -*- *)
Monomorphic Inductive MMIOAction : Set :=
  MMInput : MMIOAction | MMOutput : MMIOAction.

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
  syntax := syntax_parameters;
  mem := SortedListWord.map _ _;
  locals := Z_keyed_SortedListMap.Zkeyed_map _;
  funname_env := Empty_set_keyed_map.map;
  funname_eqb := fun _ _ => true;
  ext_spec t m action args post :=
    match action, List.map word.unsigned args with
    | MMInput, [addr] =>
      if addr =? hfrosccfg                                then True else
      if (  otp_base <=? addr) && (addr <?   otp_pastend) then True else
      if (gpio0_base <=? addr) && (addr <? gpio0_pastend) then True else
      if (uart0_base <=? addr) && (addr <? uart0_pastend) then True else
      False
      /\ addr mod 4 = 0
      /\ forall v, post m [v]
    | MMOutput, [addr; value] =>
      if addr =? hfrosccfg                                then True else
      if (gpio0_base <=? addr) && (addr <? gpio0_pastend) then True else
      if (uart0_base <=? addr) && (addr <? uart0_pastend) then True else
      False
      /\ addr mod 4 = 0
      /\ post m []
    | _, _ =>
      False
    end%list%bool;
|}.
(* hfrosccfg: Z.testbit value 30 = true  *)





Require Import bedrock2.NotationsCustomEntry.
(* both variable names and literals are Z in this file, disambiguate... *)
Local Coercion literal (x : Z) : expr := expr.literal x.
Local Notation "$ a" := (expr.var a) (in custom bedrock_expr at level 10, a ident).


Definition swap_chars_over_uart :=
  let trim : varname := 1%Z in
  let MMIOREAD  := MMInput in (* COQBUG(9514) *)
  let MMIOWRITE := MMOutput in (* COQBUG(9514) *)
  bedrock_func_body:(
    io! trim = MMIOREAD (constr:(Ox"0x00021fec"))
  ).

(*
Unset Printing Notations.
Compute swap_chars_over_uart.
*)