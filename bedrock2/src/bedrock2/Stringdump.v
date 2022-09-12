(* Supports printing strings containing only \t, \n, \r, and ASCII 32..126,
   without surrounding quotes. Sample usage: See StringdumpDemo.v *)
Require Coq.Strings.String Coq.Strings.Ascii.

Declare Scope stringdump_scope.
Declare Scope stringdumpchar_scope.

Delimit Scope stringdump_scope with stringdump.
Delimit Scope stringdumpchar_scope with stringdumpchar.

Notation "a b" := (String.String a%stringdumpchar b%stringdump)
  (only printing, right associativity, at level 3, format "a b")
  : stringdump_scope.

Undelimit Scope stringdumpchar_scope.
Undelimit Scope stringdump_scope.

Notation "" := String.EmptyString (only printing, format "") : stringdump_scope.

(* Helpful to generate this file:
Require Import Coq.Lists.List. Import ListNotations.
Compute List.map Ascii.ascii_of_nat (List.seq 32 (127-32)). *)


Notation "'	'" := (Ascii.Ascii true false false true false false false false)
  (only printing) : stringdumpchar_scope.

Notation "'
'" := (Coq.Strings.Ascii.Ascii false true false true false false false false)
  (only printing) : stringdumpchar_scope.

Notation "''" := (Ascii.Ascii true false true true false false false false)
  (only printing) : stringdumpchar_scope.

Notation " " := (Ascii.Ascii false false false false false true false false)
  (format " ", only printing) : stringdumpchar_scope.

Notation "'!'" := (Ascii.Ascii true  false false false false true  false false) (only printing) : stringdumpchar_scope.
Notation "'""'":= (Ascii.Ascii false true  false false false true  false false) (only printing) : stringdumpchar_scope.
Notation "'#'" := (Ascii.Ascii true  true  false false false true  false false) (only printing) : stringdumpchar_scope.
Notation "'$'" := (Ascii.Ascii false false true  false false true  false false) (only printing) : stringdumpchar_scope.
Notation "'%'" := (Ascii.Ascii true  false true  false false true  false false) (only printing) : stringdumpchar_scope.
Notation "'&'" := (Ascii.Ascii false true  true  false false true  false false) (only printing) : stringdumpchar_scope.
Notation "'''" := (Ascii.Ascii true  true  true  false false true  false false) (only printing) : stringdumpchar_scope.
Notation "'('" := (Ascii.Ascii false false false true  false true  false false) (only printing) : stringdumpchar_scope.
Notation "')'" := (Ascii.Ascii true  false false true  false true  false false) (only printing) : stringdumpchar_scope.
Notation "'*'" := (Ascii.Ascii false true  false true  false true  false false) (only printing) : stringdumpchar_scope.
Notation "'+'" := (Ascii.Ascii true  true  false true  false true  false false) (only printing) : stringdumpchar_scope.
Notation "','" := (Ascii.Ascii false false true  true  false true  false false) (only printing) : stringdumpchar_scope.
Notation "'-'" := (Ascii.Ascii true  false true  true  false true  false false) (only printing) : stringdumpchar_scope.
Notation "'.'" := (Ascii.Ascii false true  true  true  false true  false false) (only printing) : stringdumpchar_scope.
Notation "'/'" := (Ascii.Ascii true  true  true  true  false true  false false) (only printing) : stringdumpchar_scope.
Notation "'0'" := (Ascii.Ascii false false false false true  true  false false) (only printing) : stringdumpchar_scope.
Notation "'1'" := (Ascii.Ascii true  false false false true  true  false false) (only printing) : stringdumpchar_scope.
Notation "'2'" := (Ascii.Ascii false true  false false true  true  false false) (only printing) : stringdumpchar_scope.
Notation "'3'" := (Ascii.Ascii true  true  false false true  true  false false) (only printing) : stringdumpchar_scope.
Notation "'4'" := (Ascii.Ascii false false true  false true  true  false false) (only printing) : stringdumpchar_scope.
Notation "'5'" := (Ascii.Ascii true  false true  false true  true  false false) (only printing) : stringdumpchar_scope.
Notation "'6'" := (Ascii.Ascii false true  true  false true  true  false false) (only printing) : stringdumpchar_scope.
Notation "'7'" := (Ascii.Ascii true  true  true  false true  true  false false) (only printing) : stringdumpchar_scope.
Notation "'8'" := (Ascii.Ascii false false false true  true  true  false false) (only printing) : stringdumpchar_scope.
Notation "'9'" := (Ascii.Ascii true  false false true  true  true  false false) (only printing) : stringdumpchar_scope.
Notation "':'" := (Ascii.Ascii false true  false true  true  true  false false) (only printing) : stringdumpchar_scope.
Notation "';'" := (Ascii.Ascii true  true  false true  true  true  false false) (only printing) : stringdumpchar_scope.
Notation "'<'" := (Ascii.Ascii false false true  true  true  true  false false) (only printing) : stringdumpchar_scope.
Notation "'='" := (Ascii.Ascii true  false true  true  true  true  false false) (only printing) : stringdumpchar_scope.
Notation "'>'" := (Ascii.Ascii false true  true  true  true  true  false false) (only printing) : stringdumpchar_scope.
Notation "'?'" := (Ascii.Ascii true  true  true  true  true  true  false false) (only printing) : stringdumpchar_scope.
Notation "'@'" := (Ascii.Ascii false false false false false false true  false) (only printing) : stringdumpchar_scope.
Notation "'A'" := (Ascii.Ascii true  false false false false false true  false) (only printing) : stringdumpchar_scope.
Notation "'B'" := (Ascii.Ascii false true  false false false false true  false) (only printing) : stringdumpchar_scope.
Notation "'C'" := (Ascii.Ascii true  true  false false false false true  false) (only printing) : stringdumpchar_scope.
Notation "'D'" := (Ascii.Ascii false false true  false false false true  false) (only printing) : stringdumpchar_scope.
Notation "'E'" := (Ascii.Ascii true  false true  false false false true  false) (only printing) : stringdumpchar_scope.
Notation "'F'" := (Ascii.Ascii false true  true  false false false true  false) (only printing) : stringdumpchar_scope.
Notation "'G'" := (Ascii.Ascii true  true  true  false false false true  false) (only printing) : stringdumpchar_scope.
Notation "'H'" := (Ascii.Ascii false false false true  false false true  false) (only printing) : stringdumpchar_scope.
Notation "'I'" := (Ascii.Ascii true  false false true  false false true  false) (only printing) : stringdumpchar_scope.
Notation "'J'" := (Ascii.Ascii false true  false true  false false true  false) (only printing) : stringdumpchar_scope.
Notation "'K'" := (Ascii.Ascii true  true  false true  false false true  false) (only printing) : stringdumpchar_scope.
Notation "'L'" := (Ascii.Ascii false false true  true  false false true  false) (only printing) : stringdumpchar_scope.
Notation "'M'" := (Ascii.Ascii true  false true  true  false false true  false) (only printing) : stringdumpchar_scope.
Notation "'N'" := (Ascii.Ascii false true  true  true  false false true  false) (only printing) : stringdumpchar_scope.
Notation "'O'" := (Ascii.Ascii true  true  true  true  false false true  false) (only printing) : stringdumpchar_scope.
Notation "'P'" := (Ascii.Ascii false false false false true  false true  false) (only printing) : stringdumpchar_scope.
Notation "'Q'" := (Ascii.Ascii true  false false false true  false true  false) (only printing) : stringdumpchar_scope.
Notation "'R'" := (Ascii.Ascii false true  false false true  false true  false) (only printing) : stringdumpchar_scope.
Notation "'S'" := (Ascii.Ascii true  true  false false true  false true  false) (only printing) : stringdumpchar_scope.
Notation "'T'" := (Ascii.Ascii false false true  false true  false true  false) (only printing) : stringdumpchar_scope.
Notation "'U'" := (Ascii.Ascii true  false true  false true  false true  false) (only printing) : stringdumpchar_scope.
Notation "'V'" := (Ascii.Ascii false true  true  false true  false true  false) (only printing) : stringdumpchar_scope.
Notation "'W'" := (Ascii.Ascii true  true  true  false true  false true  false) (only printing) : stringdumpchar_scope.
Notation "'X'" := (Ascii.Ascii false false false true  true  false true  false) (only printing) : stringdumpchar_scope.
Notation "'Y'" := (Ascii.Ascii true  false false true  true  false true  false) (only printing) : stringdumpchar_scope.
Notation "'Z'" := (Ascii.Ascii false true  false true  true  false true  false) (only printing) : stringdumpchar_scope.
Notation "'['" := (Ascii.Ascii true  true  false true  true  false true  false) (only printing) : stringdumpchar_scope.
Notation "'\'" := (Ascii.Ascii false false true  true  true  false true  false) (only printing) : stringdumpchar_scope.
Notation "']'" := (Ascii.Ascii true  false true  true  true  false true  false) (only printing) : stringdumpchar_scope.
Notation "'^'" := (Ascii.Ascii false true  true  true  true  false true  false) (only printing) : stringdumpchar_scope.
Notation "'_'" := (Ascii.Ascii true  true  true  true  true  false true  false) (only printing) : stringdumpchar_scope.
Notation "'`'" := (Ascii.Ascii false false false false false true  true  false) (only printing) : stringdumpchar_scope.
Notation "'a'" := (Ascii.Ascii true  false false false false true  true  false) (only printing) : stringdumpchar_scope.
Notation "'b'" := (Ascii.Ascii false true  false false false true  true  false) (only printing) : stringdumpchar_scope.
Notation "'c'" := (Ascii.Ascii true  true  false false false true  true  false) (only printing) : stringdumpchar_scope.
Notation "'d'" := (Ascii.Ascii false false true  false false true  true  false) (only printing) : stringdumpchar_scope.
Notation "'e'" := (Ascii.Ascii true  false true  false false true  true  false) (only printing) : stringdumpchar_scope.
Notation "'f'" := (Ascii.Ascii false true  true  false false true  true  false) (only printing) : stringdumpchar_scope.
Notation "'g'" := (Ascii.Ascii true  true  true  false false true  true  false) (only printing) : stringdumpchar_scope.
Notation "'h'" := (Ascii.Ascii false false false true  false true  true  false) (only printing) : stringdumpchar_scope.
Notation "'i'" := (Ascii.Ascii true  false false true  false true  true  false) (only printing) : stringdumpchar_scope.
Notation "'j'" := (Ascii.Ascii false true  false true  false true  true  false) (only printing) : stringdumpchar_scope.
Notation "'k'" := (Ascii.Ascii true  true  false true  false true  true  false) (only printing) : stringdumpchar_scope.
Notation "'l'" := (Ascii.Ascii false false true  true  false true  true  false) (only printing) : stringdumpchar_scope.
Notation "'m'" := (Ascii.Ascii true  false true  true  false true  true  false) (only printing) : stringdumpchar_scope.
Notation "'n'" := (Ascii.Ascii false true  true  true  false true  true  false) (only printing) : stringdumpchar_scope.
Notation "'o'" := (Ascii.Ascii true  true  true  true  false true  true  false) (only printing) : stringdumpchar_scope.
Notation "'p'" := (Ascii.Ascii false false false false true  true  true  false) (only printing) : stringdumpchar_scope.
Notation "'q'" := (Ascii.Ascii true  false false false true  true  true  false) (only printing) : stringdumpchar_scope.
Notation "'r'" := (Ascii.Ascii false true  false false true  true  true  false) (only printing) : stringdumpchar_scope.
Notation "'s'" := (Ascii.Ascii true  true  false false true  true  true  false) (only printing) : stringdumpchar_scope.
Notation "'t'" := (Ascii.Ascii false false true  false true  true  true  false) (only printing) : stringdumpchar_scope.
Notation "'u'" := (Ascii.Ascii true  false true  false true  true  true  false) (only printing) : stringdumpchar_scope.
Notation "'v'" := (Ascii.Ascii false true  true  false true  true  true  false) (only printing) : stringdumpchar_scope.
Notation "'w'" := (Ascii.Ascii true  true  true  false true  true  true  false) (only printing) : stringdumpchar_scope.
Notation "'x'" := (Ascii.Ascii false false false true  true  true  true  false) (only printing) : stringdumpchar_scope.
Notation "'y'" := (Ascii.Ascii true  false false true  true  true  true  false) (only printing) : stringdumpchar_scope.
Notation "'z'" := (Ascii.Ascii false true  false true  true  true  true  false) (only printing) : stringdumpchar_scope.
Notation "'{'" := (Ascii.Ascii true  true  false true  true  true  true  false) (only printing) : stringdumpchar_scope.
Notation "'|'" := (Ascii.Ascii false false true  true  true  true  true  false) (only printing) : stringdumpchar_scope.
Notation "'}'" := (Ascii.Ascii true  false true  true  true  true  true  false) (only printing) : stringdumpchar_scope.
Notation "'~'" := (Ascii.Ascii false true  true  true  true  true  true  false) (only printing) : stringdumpchar_scope.
