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
  ("spi_read", ((b::nil), (b::busy::nil), bedrock_func_body:(
    busy = (constr:(-1));
    b = (busy);
    i = (patience); while (i) { i = (i - constr:(1));
      io! busy = MMIOREAD(SPI_READ_ADDR);
      if !(busy >> constr:(31)) {
        b = (busy & constr:(Ox"ff"));
        i = (i^i)
      }
    }
  ))).
