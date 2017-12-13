
Notation "'for' m 'from' 0 'to' N 'updating' ( s1 ) {{ b }} ;; rest" :=
  (let s1 :=
    (fix rec(n: nat) := match n with
     | 0 => s1
     | S m => let s1 := rec m in b
     end) N
  in rest)
  (at level 20, right associativity).
