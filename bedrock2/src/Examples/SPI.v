Require Import bedrock2.Syntax bedrock2.StringNamesSyntax bedrock2.BasicCSyntax.
Require Import bedrock2.NotationsCustomEntry coqutil.Z.HexNotation.

Import BinInt String List.ListNotations.
Local Open Scope Z_scope. Local Open Scope string_scope. Local Open Scope list_scope.
Local Existing Instance BasicCSyntax.StringNames_params.
Local Coercion literal (z : Z) : expr := expr.literal z.
Local Coercion var (x : String.string) : expr := expr.var x.

Local Notation MMIOWRITE := "MMIOWRITE".
Local Notation MMIOREAD := "MMIOREAD".

Definition spi_write : function :=
  let b : varname := "b" in
  let busy : varname := "busy" in
  let i : varname := "i" in
  let patience := -1 in
  let SPI_WRITE_ADDR := Ox"10024048" in
  ("spi_write", ((b::nil), (busy::nil), bedrock_func_body:(
    busy = (constr:(-1));
    i = (patience); while (i) { i = (i - constr:(1));
      io! busy = MMIOREAD(SPI_WRITE_ADDR);
      if !(busy >> constr:(31)) {
        i = (i^i);
        busy = (busy ^ busy)
      }
    };
    if !busy {
      output! MMIOWRITE(SPI_WRITE_ADDR, b)
    }
  ))).

Definition spi_read : function :=
  let b : varname := "b" in
  let busy : varname := "busy" in
  let i : varname := "i" in
  let patience := -1 in
  let SPI_READ_ADDR := Ox"0x1002404c" in
  ("spi_read", (nil, (b::busy::nil), bedrock_func_body:(
    busy = (constr:(-1));
    b = (busy);
    i = (patience); while (i) { i = (i - constr:(1));
      io! busy = MMIOREAD(SPI_READ_ADDR);
      if !(busy >> constr:(31)) {
        b = (busy & constr:(Ox"ff"));
        i = (i^i);
        busy = (busy ^ busy)
      }
    }
  ))).

Require Import bedrock2.ProgramLogic.
Require Import bedrock2.FE310CSemantics.
Require Import coqutil.Word.Interface.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.ReversedListNotations bedrock2.TracePredicate. Import TracePredicateNotations.
Require Import bedrock2.Examples.lightbulb_spec.
Fail
Instance spec_of_spi_write : spec_of "spi_write" := fun functions => forall t m b,
  WeakestPrecondition.call functions "spi_write" t m [b] (fun T M RETS =>
    M = m /\ Logic.or
      ((exists err, word.unsigned err <> 0 /\ RETS = [err]) /\ (eq t +++ (spi_write_full^* )) T)
      (RETS = [word.of_Z 0] /\ T = t ++ (*FIXME*)nil)).
(* The term "spi_write_full" has type *)
(*  "word 8 -> forall word : word 32, list (OP word) -> Prop" *)
(* while it is expected to have type "list ?T -> Prop". *)

(*
Require Import coqutil.Map.Interface.
Lemma spi_write_ok : program_logic_goal_for_function! spi_write.
Proof.
  repeat straightline.
 *)
