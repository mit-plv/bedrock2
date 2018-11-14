Require Coq.NArith.BinNatDef.

Require Export Coq.Strings.String.
Definition eqb a b := andb (String.prefix a b) (String.prefix b a).

Module Ascii.
  Import Coq.NArith.BinNatDef.
  Definition eqb (c d : Ascii.ascii) : bool := N.eqb (Ascii.N_of_ascii c) (Ascii.N_of_ascii d).
  Definition ltb (c d : Ascii.ascii) : bool := N.ltb (Ascii.N_of_ascii c) (Ascii.N_of_ascii d).
End Ascii.

Fixpoint ltb (a b : string) : bool :=
  match a, b with
    | EmptyString, String _ _ => true
    | String x a', String y b' =>
      if Ascii.eqb x y
      then ltb a' b'
      else Ascii.ltb x y
    | _, _ => false
  end.