Require Export compiler.Decidable.

Class NameWithEq := mkNameWithEq {
  name: Set;
  eq_name_dec: DecidableEq name
}.
