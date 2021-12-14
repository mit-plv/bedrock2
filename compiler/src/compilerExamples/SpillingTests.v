Require Import bedrock2.NotationsCustomEntry.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition swap : func := let a := "a" in let b := "b" in let t := "t" in
  ("swap", ([a; b], [], bedrock_func_body:(
  t = load(b);
  store(b, load(a));
  store(a, t)
))).

Definition long1 : func :=
  let a0 := "a0" in let b0 := "b0" in
  let a1 := "a1" in let b1 := "b1" in
  let a2 := "a2" in let b2 := "b2" in
  let a3 := "a3" in let b3 := "b3" in
  let a4 := "a4" in let b4 := "b4" in
  let a5 := "a5" in let b5 := "b5" in
  let a6 := "a6" in let b6 := "b6" in
  let a7 := "a7" in let b7 := "b7" in
  let a8 := "a8" in let b8 := "b8" in
  let a9 := "a9" in let b9 := "b9" in
  let a10 := "a10" in let b10 := "b10" in
  let a11 := "a11" in let b11 := "b11" in
  let a12 := "a12" in let b12 := "b12" in
  let a13 := "a13" in let b13 := "b13" in
  let a14 := "a14" in let b14 := "b14" in
  let a15 := "a15" in let b15 := "b15" in
  let a16 := "a16" in let b16 := "b16" in
  let a17 := "a17" in let b17 := "b17" in
  let a18 := "a18" in let b18 := "b18" in
  let a19 := "a19" in let b19 := "b19" in
  ("long1", ([a0; b0], [a19;b19], bedrock_func_body:(

  (* TODO once spilling is improved, test that it still works if these two lines are removed
     (currently the test that all resnames are <32 fails if these two lines are removed) *)
  a19 = $0;
  b19 = $0;

  swap(a0, b0);
  a1 = a0 + b0 * b0;
  swap(a1, b0);
  a12 = a1 - a0 - b0;
  b12 = a1 + a12 * b0;
  a5 = a12 * b12;
  a9 = a5 - a0 - b0;
  a4 = a1;
  b3 = a4 + a12 * b0;
  b4 = a4;
  a10 = a1 - a0 - b4;
  b12 = a1 + a12 * b0;
  a3 = a1;
  a6 = a10 + b12;
  a15 = a3 - a0 - b0;
  a2 = a1;
  b12 = a2 + a12 * b0;
  a11 = a10 - a0 - b0;
  b5 = a1;
  b4 = a6 + a12 * b5;
  a2 = a11 - a0 - b0;
  b12 = a1 + a12 * b0;
  a16 = a12 - a0 - b0;
  a7 = a2;
  b14 = a7 + a12 * b0;
  a13 = b4;
  a17 = $2;
  b6 = $33;
  a12 = a13 - a17 - b6;
  b12 = a1 + a12 * b0;
  a18 = $18;
  b19 = $19;
  a17 = a1 - a18 - b19;
  b12 = a1 + a9 * b0;
  a14 = $14;
  a12 = a14 - a0 - b0;
  a8 = b12;
  b13 = a8 + a12 * b0;
  a12 = a1 - a0 - b0;
  b2 = a1 + a12 * b0;
  a18 = a1 - a0 - b0;
  b16 = $23;
  b12 = a15 + a8 * b16;
  a12 = a1 - a0 - b3;
  b12 = a1 + a12 * b0;

  a19 = a1 - a0 - b0;
  b19 = a9 + a7 * b0;

  b0 = b0 + a1;
  b0 = b0 + a12;
  b0 = b0 + b12;
  b0 = b0 + a5;
  b0 = b0 + a9;
  b0 = b0 + a4;
  b0 = b0 + b3;
  b0 = b0 + b4;
  b0 = b0 + a10;
  b0 = b0 + b12;
  b0 = b0 + a3;
  b0 = b0 + a6;
  b0 = b0 + a15;
  b0 = b0 + a2;
  b0 = b0 + b12;
  b0 = b0 + a11;
  b0 = b0 + b5;
  b0 = b0 + b4;
  b0 = b0 + a2;
  b0 = b0 + b12;
  b0 = b0 + a16;
  b0 = b0 + a7;
  b0 = b0 + b14;
  b0 = b0 + a13;
  b0 = b0 + a17;
  b0 = b0 + b6;
  b0 = b0 + a12;
  b0 = b0 + b12;
  b0 = b0 + a18;
  b0 = b0 + b19;
  b0 = b0 + a17;
  b0 = b0 + b12;
  b0 = b0 + a14;
  b0 = b0 + a12;
  b0 = b0 + a8;
  b0 = b0 + b13;
  b0 = b0 + a12;
  b0 = b0 + b2;
  b0 = b0 + a18;
  b0 = b0 + b16;
  b0 = b0 + b12;
  b0 = b0 + a12;
  b0 = b0 + b12;
  b0 = b0 + a19;
  b0 = b0 + b19;

  a19 = b0;
  b19 = b0
))).
