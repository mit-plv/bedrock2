Require bedrock2.BasicC64Semantics bedrock2.NotationsCustomEntry.
Import BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Require Import coqutil.Macros.ident_to_string.

Section chacha20.
  Import bedrock2.Syntax Syntax.Coercions NotationsCustomEntry.

  Local Notation "x <<<= n" := (cmd.set (ident_to_string! x) (expr.op bopname.slu (ident_to_string! x) n)) (in custom bedrock_cmd at level 0, x ident, n bigint).
  Local Notation "x ^= e" := (cmd.set (ident_to_string! x) (expr.op bopname.xor (ident_to_string! x) e)) (in custom bedrock_cmd at level 0, x ident, e custom bedrock_expr).
  Local Notation "x += e" := (cmd.set (ident_to_string! x) (expr.op bopname.add (ident_to_string! x) e)) (in custom bedrock_cmd at level 0, x ident, e custom bedrock_expr).

  Definition chacha20_quarter : func :=
    ("chacha20_quarter", (["a";"b";"c";"d"], ["a";"b";"c";"d"], bedrock_func_body:(
      a += b; d ^= a; d <<<= 16;
      c += d; b ^= c; b <<<= 12;
      a += b; d ^= a; d <<<= 8;
      c += d; b ^= c; b <<<= 7
    ))).

  Definition QUARTERROUND (a b c d : String.string) : cmd
    := ltac:(let body := (eval cbv [chacha20_quarter] in (let '(_, (_, _, body)) := chacha20_quarter in body)) in
             lazymatch (eval pattern "a", "b", "c", "d" in body) with
             | ?x "a" "b" "c" "d"
               => let y := (eval cbv beta in (x a b c d)) in
                  exact y
             end).

  Local Notation "'xorout' o x" := (
      let addr := bedrock_expr:(out+coq:(expr.literal(4*o))) in
      bedrock_cmd:(store4($addr, load4($addr)^$(expr.var (ident_to_string! x)))))
      (in custom bedrock_cmd at level 0, o bigint, x ident).

  Definition chacha20_block_separate : func :=
    (* NOTE: I (andreser) don't understand why xorout needs these *)
    let x0  := "x0" in let x1  := "x1" in let x2  := "x2" in let x3  := "x3" in
    let x4  := "x4" in let x5  := "x5" in let x6  := "x6" in let x7  := "x7" in
    let x8  := "x8" in let x9  := "x9" in let x10 := "x10" in let x11 := "x11" in
    let x12 := "x12" in let x13 := "x13" in let x14 := "x14" in let x15 := "x15" in
    ("chacha20_block", (["out"; "key"; "nonce"; "countervalue"], [], bedrock_func_body:(
      x0 = $0x61707865;   x1 = $0x3320646e;   x2 = $0x79622d32;    x3 = $0x6b206574;
      x4 = load4(key);           x5 = load4(key+$4);   x6 = load4(key+$8);    x7 = load4(key+$12);
      x8 = load4(key+$16);  x9 = load4(key+$20); x10 = load4(key+$24);  x11 = load4(key+$28);
      x12 = countervalue;       x13 = load4(nonce);        x14 = load4(nonce+$4); x15 = load4(nonce+$8);
      i = $0; while (i < $10) { i += $1;
        (x0, x4,  x8, x12) = chacha20_quarter( x0, x4, x8,  x12);
        (x1, x5,  x9, x13) = chacha20_quarter( x1, x5, x9,  x13);
        (x2, x6, x10, x14) = chacha20_quarter( x2, x6, x10, x14);
        (x3, x7, x11, x15) = chacha20_quarter( x3, x7, x11, x15);
        (x0, x5, x10, x15) = chacha20_quarter( x0, x5, x10, x15);
        (x1, x6, x11, x12) = chacha20_quarter( x1, x6, x11, x12);
        (x2, x7,  x8, x13) = chacha20_quarter( x2, x7, x8,  x13);
        (x3, x4,  x9, x14) = chacha20_quarter( x3, x4, x9,  x14)
      };
      x0 += $0x61707865;  x1 += $0x3320646e;   x2 += $0x79622d32;    x3 += $0x6b206574;
      x4 += load4(key);          x5 += load4(key+$4);   x6 += load4(key+$8);    x7 += load4(key+$12);
      x8 += load4(key+$16); x9 += load4(key+$20); x10 += load4(key+$24);  x11 += load4(key+$28);
      x12 += countervalue;      x13 += load4(nonce);        x14 += load4(nonce+$4); x15 += load4(nonce+$8);
      xorout  0  x0;   xorout 1 x1; xorout 2   x2;  xorout 3  x3;
      xorout  4  x4;   xorout 5 x5; xorout 6   x6;  xorout 7  x7;
      xorout  8  x8;   xorout 9 x9; xorout 10 x10; xorout 11 x11;
      xorout 12 x12; xorout 13 x13; xorout 14 x14; xorout 15 x15
  ))).

  Local Ltac repquarterround body :=
    lazymatch body with
    | context body[cmd.call [?x1; ?x2; ?x3; ?x4] "chacha20_quarter" [expr.var ?x1; expr.var ?x2; expr.var ?x3; expr.var ?x4] ]
      => let body := context body[QUARTERROUND x1 x2 x3 x4] in
         repquarterround body
    | context body[cmd.call ?ls "chacha20_quarter" ?ls' ]
      => let v := constr:(cmd.call ls "chacha20_quarter" ls') in
         fail 0 "could not replace ""chacha20_quarter"" in" v
    | context["chacha20_quarter"]
      => fail 0 "could not replace ""chacha20_quarter"" in" body
    | _ => body
    end.
  Definition chacha20_block : func :=
    ltac:(let body := (eval cbv delta [chacha20_block_separate] in chacha20_block_separate) in
          let body := repquarterround body in
          exact body).
End chacha20.

(*
Require bedrock2.ToCString.
Example chacha20_block_c_string := Eval vm_compute in
  ToCString.c_module [chacha20_quarter; chacha20_block_separate].
Print chacha20_block_c_string.
*)
