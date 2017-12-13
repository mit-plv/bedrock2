Require Import bbv.Word.

Notation "'for' m 'from' 0 'to' N 'updating' ( s1 ) {{ b }} ;; rest" :=
  (let s1 :=
    (fix rec(n: nat) := match n with
     | 0 => s1
     | S m => let s1 := rec m in
              let m := natToWord _ m in
              b
     end) (wordToNat N)
  in rest)
  (at level 20, right associativity).
