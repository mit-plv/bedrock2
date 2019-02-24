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

Definition patience : Z.                                     exact (10^150). Qed.

Definition otp_base   := Ox"0x00020000". Definition otp_pastend   := Ox"0x00022000".
Definition hfrosccfg  := Ox"10008000".
Definition gpio0_base := Ox"0x10012000". Definition gpio0_pastend := Ox"0x10013000".
Definition uart0_base := Ox"0x10013000". Definition uart0_pastend := Ox"0x10014000".
Definition uart0_rxdata := Ox"10013004". Definition uart0_txdata := Ox"10013000".

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
    | MMOutput, [addr; value] =>
      if addr =? hfrosccfg                                then Z.testbit value 30 = true else
      if (gpio0_base <=? addr) && (addr+3 <? gpio0_pastend) then True else
      if (uart0_base <=? addr) && (addr+3 <? uart0_pastend) then True else
      False
      /\ post m []
    | MMInput, [addr] =>
      if addr =? hfrosccfg                                  then True else
      if (  otp_base <=? addr) && (addr+3 <?   otp_pastend) then True else
      if (gpio0_base <=? addr) && (addr+3 <? gpio0_pastend) then True else
      if (uart0_base <=? addr) && (addr+3 <? uart0_pastend) then True else
      False
      /\ forall v,
          (patience < Z.of_nat (List.length t) -> addr = uart0_rxdata ->
            word.and v (word.of_Z 255) = word.of_Z 46) /\
          (patience < Z.of_nat (List.length t) -> addr = uart0_txdata ->
            word.and v (word.slu (word.of_Z 1) (word.of_Z 31)) = (word.slu (word.of_Z 1) (word.of_Z 31))) /\
          post m [v]
    | _, _ =>
      False
    end%list%bool;
|}.