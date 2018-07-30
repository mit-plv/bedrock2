Require Import Coq.Strings.String.
Definition eqb a b := andb (String.prefix a b) (String.prefix b a).