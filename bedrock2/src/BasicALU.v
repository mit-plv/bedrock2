Require Import coqutil.subst coqutil.unique bedrock2.Syntax.

Local Set Primitive Projections.
Class operations {p: unique! Syntax.parameters} :=
  {
    bop_add : bopname;
    bop_sub : bopname;
    bop_mul : bopname;

    bop_and : bopname;
    bop_or : bopname;
    bop_xor : bopname;

    (* no information about return value of long shifts, but they are allowed *)
    bop_sru : bopname;
    bop_slu : bopname;
    bop_srs : bopname;

    bop_lts : bopname;
    bop_ltu : bopname;
    bop_eq : bopname;
  }.