Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Word.Naive coqutil.Word.Interface.
Require Import coqutil.Datatypes.List.
Require Import bedrock2.ReversedListNotations.

Import ListNotations.
Open Scope Z_scope.

Notation word := Naive.word32.

Inductive MMIO :=
| MMInput(addr value: word)
| MMOutput(addr value: word).

Notation ForeverSilent := (eq nil).

Declare Scope trace_scope.

Notation "'OUT' [ a ]  'const' c ;; P" :=
  (fun t => exists t', t = [MMOutput a c] ;++ t' /\ P t')
    (at level 11, c at level 0, P at level 11, left associativity) : trace_scope.

Notation "'OUT' [ a ] v 'st' cond ;; P" :=
  (fun t => exists v t', t = [MMOutput a v] ;++ t' /\ cond /\ P t')
    (at level 11, cond at level 0, P at level 11, left associativity): trace_scope.

(* note how 'st' results in '->' in IN but '/\' in OUT *)

Open Scope trace_scope.

Notation "'IN' [ a ] v 'st' cond ;; P" :=
  (fun t => exists v t', t = [MMInput a v] ;++ t' /\ cond -> P t')
    (at level 11, cond at level 0, P at level 11, left associativity): trace_scope.

Notation "'IN' [ a ]  'const' c ;; P" :=
  (IN[a] v st (v = c) ;; P)
    (at level 11, c at level 0, P at level 11, left associativity): trace_scope.

Notation "'IN' [ a ]  'arbitrary' v ;; P" :=
  (IN[a] v st True;; P)
    (at level 11, P at level 11, left associativity): trace_scope.

Inductive zip{A B C: Type}(f: A -> B -> C): list A -> list B -> list C -> Prop :=
| zip_nil: zip f nil nil nil
| zip_cons: forall x y xs ys zs,
    zip f xs ys zs ->
    zip f (x :: xs) (y :: ys) (f x y :: zs).

Notation "'INs' [ addrs ] vs 'st' cond ;; P" :=
  (fun t => exists vs t1 t2, t = t1 ;++ t2 /\ zip MMInput addrs vs t1 /\ cond -> P t2)
    (at level 11, cond at level 0, P at level 11, left associativity): trace_scope.

Notation "'INs' [ addrs ] 'const' cs ;; P" :=
  (INs [ addrs ] vs st (vs = cs);; P)
    (at level 11, P at level 11, left associativity): trace_scope.

Example addr100: word := word.of_Z 100.
Example value42: word := word.of_Z 42.

Goal forall t, (IN[addr100] v st (v = value42) ;; ForeverSilent) t.
Abort.

(* Read as "This program first makes a load request at addr100, and if you answer this request
   with a small enough value, it will output its square, and then not output anything more" *)
Goal forall t, (IN[addr100] v st (word.unsigned v < 2 ^ 16);;
                OUT[addr100] r st (word.unsigned r = word.unsigned v * word.unsigned v);;
                ForeverSilent) t.
Abort.

(* trace property which holds for program execution *)
Definition execProp: list MMIO -> Prop. Admitted.

Definition GetPrgSzAddr: word. Admitted.
Definition FirstPrgAddr: word. Admitted.

(* Trace property which holds for a processor which first uses MMIO to load a program and
   then runs that program.
   Read as "if you wait for the processor to request a load at GetPrgSzAddr and answer that
   load with the length of the program, then the processor will continue to request addresses
   FirstPrgAddr through FirstProgAddr+(length prog), and if you answer these requests with
   the values of prg, then the rest of the processor's IO behavior will satisfy traceProp". *)
Goal forall prg t,
  (IN[GetPrgSzAddr] const (word.of_Z (Z.of_nat (length prg)));;
   INs[List.unfoldn (word.add (word.of_Z 4)) (length prg) FirstPrgAddr] const prg;;
   execProp) t.
Proof.
  intros.
  (* in case you prefer reading it in plain logic rather than with notations: *)
  cbv beta.
Abort.
