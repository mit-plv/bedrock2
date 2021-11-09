Require Import Rupicola.Lib.Core.

Declare Scope word.
Notation "~w w" := (word.not w) (at level 30, no associativity): word.
Infix "*w" := word.mul (at level 40, left associativity): word.
Infix "/w" := word.divu (at level 40, left associativity): word.
Infix "/sw" := word.divs (at level 40, left associativity): word.
Infix "+w" := word.add (at level 50, left associativity): word.
Infix "-w" := word.sub (at level 50, left associativity): word.
Infix ">>w" := word.sru (at level 60, no associativity): word.
Infix ">>>w" := word.srs (at level 60, no associativity): word.
Infix "<<w" := word.slu (at level 60, no associativity): word.
Notation "w1 <w w2" := (word.b2w (word.ltu w1 w2)) (at level 70, no associativity): word.
Notation "w1 >w w2" := (word.b2w (word.gtu w1 w2)) (at level 70, no associativity): word.
Notation "w1 <sw w2" := (word.b2w (word.lts w1 w2)) (at level 70, no associativity): word.
Notation "w1 >sw w2" := (word.b2w (word.gts w1 w2)) (at level 70, no associativity): word.
Notation "w1 ==w w2" := (word.b2w (word.eqb w1 w2)) (at level 80, no associativity): word.
Infix "&w" := word.and (at level 90, left associativity): word.
Infix "^w" := word.xor (at level 92, left associativity): word.
Infix "|w" := word.or (at level 94, left associativity): word.

Open Scope word.
