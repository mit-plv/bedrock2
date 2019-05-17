Require Import bedrock2.Syntax bedrock2.StringNamesSyntax bedrock2.BasicCSyntax.
Require Import bedrock2.NotationsCustomEntry coqutil.Z.HexNotation.
Require Import bedrock2.Examples.SPI.

Import BinInt String List.ListNotations.
Local Open Scope Z_scope. Local Open Scope string_scope. Local Open Scope list_scope.
Local Existing Instance BasicCSyntax.StringNames_params.
Local Coercion literal (z : Z) : expr := expr.literal z.
Local Coercion var (x : String.string) : expr := expr.var x.
Local Coercion name_of_func (f : function) := fst f.

Local Notation MMIOWRITE := "MMIOWRITE".
Local Notation MMIOREAD := "MMIOREAD".

Definition lan9250_readword : function :=
  let addr : varname := "addr" in
  let ret : varname := "ret" in
  let err : varname := "err" in
  let SPI_CSMODE_ADDR := Ox"10024018" in
  ("lan9250_readword", ((addr::nil), (ret::nil), bedrock_func_body:(
    io! ret = MMIOREAD(SPI_CSMODE_ADDR);
    ret = (ret | constr:(2));
    output! MMIOWRITE(SPI_CSMODE_ADDR, ret);

    unpack! err = spi_write(constr:(Ox"0b"));        require !err; (* FASTREAD *)
    unpack! err = spi_write(addr >> constr:(8));     require !err;
    unpack! err = spi_write(addr & constr:(Ox"ff")); require !err;
    unpack! err = spi_write(err);                    require !err; (* dummy *)
    unpack! err = spi_write(err);                    require !err; (* read *)
    unpack! err = spi_write(err);                    require !err; (* read *)
    unpack! err = spi_write(err);                    require !err; (* read *)
    unpack! err = spi_write(err);                    require !err; (* read *)

    unpack! ret, err = spi_read(); require !err; (* write *)
    unpack! ret, err = spi_read(); require !err; (* write *)
    unpack! ret, err = spi_read(); require !err; (* write *)
    unpack! ret, err = spi_read(); require !err; (* write *)

    (* manually register-allocated, apologies for variable reuse *)
    unpack! ret, err = spi_read();   require !err;
    (* ret = ret << 0 *)
    unpack! addr, err = spi_read();  require !err;
    ret = (ret | (addr << constr:(8)));
    unpack! addr, err = spi_read();  require !err;
    ret = (ret | (addr << constr:(16)));
    unpack! addr, err = spi_read();  require !err;
    ret = (ret | (addr << constr:(24)));

    io! addr = MMIOREAD(SPI_CSMODE_ADDR);
    addr = (addr & constr:(Z.lnot 2));
    output! MMIOWRITE(SPI_CSMODE_ADDR, addr)
  ))).

Instance spec_of_lan9250_readword : ProgramLogic.spec_of "lan9250_readword" :=
  fun functions => forall t m addr,
    (Ox"0" <= Word.Interface.word.unsigned addr < Ox"400") ->
    WeakestPrecondition.call functions "lan9250_readword" t m [addr] (fun T M RETS =>
      M = m /\ exists v, RETS = [v]).
