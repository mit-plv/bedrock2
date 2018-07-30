Require Import Coq.Strings.String.
Definition string_eqb a b := andb (String.prefix a b) (String.prefix b a).