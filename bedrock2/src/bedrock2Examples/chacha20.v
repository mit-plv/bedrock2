Require bedrock2.BasicC64Semantics bedrock2.NotationsCustomEntry coqutil.Z.HexNotation.
Import BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Section chacha20.
  Import bedrock2.Syntax Syntax.Coercions NotationsCustomEntry HexNotation.

  Local Notation "x <<< n" := (bedrock_expr:((x<<coq:(expr.literal n)) | (x>>coq:(expr.literal (32-(n:Z)))))) (in custom bedrock_expr at level 2, left associativity).
  Local Notation "x <<<= n" := (bedrock_cmd:(x = (x<<<n))) (in custom bedrock_cmd at level 0, x global, n bigint).
  Local Notation "x ^= e" := (bedrock_cmd:(x = (x^e))) (in custom bedrock_cmd at level 0, x global, e custom bedrock_expr at level 999).
  Local Notation "x += e" := (bedrock_cmd:(x = (x+e))) (in custom bedrock_cmd at level 0, x global, e custom bedrock_expr at level 999).

  Definition chacha20_quarter : func :=
    let a := "a" in let b := "b" in let c := "c" in let d := "d" in
    ("chacha20_quarter", ([a;b;c;d], [a;b;c;d], bedrock_func_body:(
      a += b; d ^= a; d <<<= 16;
      c += d; b ^= c; b <<<= 12;
      a += b; d ^= a; d <<<= 8;
      c += d; b ^= c; b <<<= 7
    ))).

  Definition chacha20_block : func :=
    let key := "key" in let countervalue := "countervalue" in let nonce := "nonce" in let i := "i" in
    let x0  := "x0" in let x1  := "x1" in let x2  := "x2" in let x3  := "x3" in
    let x4  := "x4" in let x5  := "x5" in let x6  := "x6" in let x7  := "x7" in
    let x8  := "x8" in let x9  := "x9" in let x10 := "x10" in let x11 := "x11" in
    let x12 := "x12" in let x13 := "x13" in let x14 := "x14" in let x15 := "x15" in
    let out := "out" in
    let xorout o x : cmd :=
      let addr := bedrock_expr:((out+coq:(expr.literal(4*o)))) in
      bedrock_cmd:(store4(addr, load4(addr)^x)) in
    ("chacha20_block", ([out; key; nonce; countervalue], [], bedrock_func_body:(
      x0 = coq:(Ox"61707865");   x1 = coq:(Ox"3320646e");   x2 = coq:(Ox"79622d32");    x3 = coq:(Ox"6b206574");
      x4 = load4(key);           x5 = load4(key+coq:(4));   x6 = load4(key+coq:(8));    x7 = load4(key+coq:(12));
      x8 = load4(key+coq:(16));  x9 = load4(key+coq:(20)); x10 = load4(key+coq:(24));  x11 = load4(key+coq:(28));
      x12 = countervalue;       x13 = load4(nonce);        x14 = load4(nonce+coq:(4)); x15 = load4(nonce+coq:(8));
      i = coq:(0); while (i < coq:(10)) { i += coq:(1);
        (x0, x4,  x8, x12) = chacha20_quarter( x0, x4, x8,  x12);
        (x1, x5,  x9, x13) = chacha20_quarter( x1, x5, x9,  x13);
        (x2, x6, x10, x14) = chacha20_quarter( x2, x6, x10, x14);
        (x3, x7, x11, x15) = chacha20_quarter( x3, x7, x11, x15);
        (x0, x5, x10, x15) = chacha20_quarter( x0, x5, x10, x15);
        (x1, x6, x11, x12) = chacha20_quarter( x1, x6, x11, x12);
        (x2, x7,  x8, x13) = chacha20_quarter( x2, x7, x8,  x13);
        (x3, x4,  x9,  x1) = chacha20_quarter( x3, x4, x9,  x14)
      };
      x0 += coq:(Ox"61707865");  x1 += coq:(Ox"3320646e");   x2 += coq:(Ox"79622d32");    x3 += coq:(Ox"6b206574");
      x4 += load4(key);          x5 += load4(key+coq:(4));   x6 += load4(key+coq:(8));    x7 += load4(key+coq:(12));
      x8 += load4(key+coq:(16)); x9 += load4(key+coq:(20)); x10 += load4(key+coq:(24));  x11 += load4(key+coq:(28));
      x12 += countervalue;      x13 += load4(nonce);        x14 += load4(nonce+coq:(4)); x15 += load4(nonce+coq:(8));
      coq:(xorout  0  x0);   coq:(xorout 1 x1); coq:(xorout 2   x2);  coq:(xorout 3  x3);
      coq:(xorout  4  x4);   coq:(xorout 5 x5); coq:(xorout 6   x6);  coq:(xorout 7  x7);
      coq:(xorout  8  x8);   coq:(xorout 9 x9); coq:(xorout 10 x10); coq:(xorout 11 x11);
      coq:(xorout 12 x12); coq:(xorout 13 x13); coq:(xorout 14 x14); coq:(xorout 15 x15)
  ))).
End chacha20.

(*
Require bedrock2.ToCString.
Example chacha20_block_c_string := Eval vm_compute in
  ToCString.c_module [chacha20_quarter; chacha20_block].
Print chacha20_block_c_string.
*)
