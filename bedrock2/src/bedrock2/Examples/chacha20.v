Require Import bedrock2.BasicC64Semantics bedrock2.NotationsInConstr coqutil.Z.HexNotation.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Coercion var (x : string) : Syntax.expr := Syntax.expr.var x.

From coqutil.Macros Require Import unique subst.

Import BinInt String.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Section chacha20.
  Import bedrock2.NotationsInConstr.
  Local Coercion literal (z : Z) : expr := expr.literal z.

  Notation "x <<< n" := ((x << (n%Z)%bedrock_expr) .| (x >> (32 - n%Z)))%bedrock_expr (at level 100) : bedrock_expr.
  Notation "a <<<= b" := (subst! a for x in (x = (x <<< b)))%bedrock_cmd (at level 75) : bedrock_cmd.
  Notation "a ^= b" := (subst! a for x in (x = (x .^ b)))%bedrock_cmd (at level 75) : bedrock_cmd.
  Notation "a += b" := (subst! a for x in (x = (x + b)))%bedrock_cmd (at level 75) : bedrock_cmd.

  Definition QUARTERROUND (a b c d : varname) : cmd :=
    a += b;; d ^= a;; d <<<= 16;;
    c += d;; b ^= c;; b <<<= 12;;
    a += b;; d ^= a;; d <<<= 8;;
    c += d;; b ^= c;; b <<<= 7.

  Let out := "out". Let key := "key". Let countervalue := "countervalue". Let nonce := "nonce".
  Let i := "i".
  Let x0  := "x0". Let x1  := "x1". Let x2  := "x2". Let x3  := "x3".
  Let x4  := "x4". Let x5  := "x5". Let x6  := "x6". Let x7  := "x7".
  Let x8  := "x8". Let x9  := "x9". Let x10 := "x10". Let x11 := "x11".
  Let x12 := "x12". Let x13 := "x13". Let x14 := "x14". Let x15 := "x15".
  Definition xorout o x : cmd := *(uint32_t*)((out+literal(4*o))%bedrock_expr) = *(uint32_t*)((out+literal(4*o))) .^ x.
  Definition chacha20_block := ((out::key::nonce::countervalue::nil), @nil varname, bedrock_func_body:(
    x0 = Ox"61707865";;          x1 = Ox"3320646e";;          x2 = Ox"79622d32";;            x3 = Ox"6b206574";;
    x4 = *(uint32_t*) key;;      x5 = *(uint32_t*) (key+4);;  x6 = *(uint32_t*) (key+8);;    x7 = *(uint32_t*) (key+12);;
    x8 = *(uint32_t*) (key+16);; x9 = *(uint32_t*) (key+20);; x10 = *(uint32_t*) (key+24);;  x11 = *(uint32_t*) (key+28);;
    x12 = countervalue;;         x13 = *(uint32_t*) nonce;;   x14 = *(uint32_t*) (nonce+4);; x15 = *(uint32_t*) (nonce+8);;
    i = 0;; while (i < 10) {{ i += 1;;
      QUARTERROUND x0 x4 x8  x12;;
      QUARTERROUND x1 x5 x9  x13;;
      QUARTERROUND x2 x6 x10 x14;;
      QUARTERROUND x3 x7 x11 x15;;
      QUARTERROUND x0 x5 x10 x15;;
      QUARTERROUND x1 x6 x11 x12;;
      QUARTERROUND x2 x7 x8  x13;;
      QUARTERROUND x3 x4 x9  x14
    }};;
    x0 += Ox"61707865";;          x1 += Ox"3320646e";;          x2 += Ox"79622d32";;            x3 += Ox"6b206574";;
    x4 += *(uint32_t*) key;;      x5 += *(uint32_t*) (key+4);;  x6 += *(uint32_t*) (key+8);;    x7 += *(uint32_t*) (key+12);;
    x8 += *(uint32_t*) (key+16);; x9 += *(uint32_t*) (key+20);; x10 += *(uint32_t*) (key+24);;  x11 += *(uint32_t*) (key+28);;
    x12 += countervalue;;         x13 += *(uint32_t*) nonce;;   x14 += *(uint32_t*) (nonce+4);; x15 += *(uint32_t*) (nonce+8);;
    xorout  0  x0;;   xorout 1 x1;; xorout 2   x2;;  xorout 3 x3;;
    xorout  4  x4;;   xorout 5 x5;; xorout 6   x6;;  xorout 7 x7;;
    xorout  8  x8;;   xorout 9 x9;; xorout 10 x10;; xorout 11 x11;;
    xorout 12 x12;; xorout 13 x13;; xorout 14 x14;; xorout 15 x15
  )).
End chacha20.

(*
Example chacha20_block_c_string := Eval vm_compute in
  BasicC64Syntax.c_func ("chacha20_block", (chacha20_block )).
Print chacha20_block_c_string.
*)
