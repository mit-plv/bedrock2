Require Import compiler.Common.

Section lemmas.

  Context {T E: Type}.
  Context {setInst: set T E}.

  Section union_intersect_diff_contains_lemmas.

    Variable s: E.
    Variable t1 t2: T.

    Lemma in_intersect_l: s \in (intersect t1 t2) -> s \in t1. Admitted.

    Lemma in_intersect_r: s \in (intersect t1 t2) -> s \in t2. Admitted.

    Lemma notin_intersect_l: ~ s \in t1 -> ~ s \in (intersect t1 t2). Admitted.

    Lemma notin_intersect_r: ~ s \in t2 -> ~ s \in (intersect t1 t2). Admitted.

    Lemma notin_intersect_other_l: ~ s \in (intersect t1 t2) -> s \in t1 -> ~ s \in t2. Admitted.

    Lemma notin_intersect_other_r: ~ s \in (intersect t1 t2) -> s \in t2 -> ~ s \in t1. Admitted.

    Lemma in_intersect: s \in t1 -> s \in t2 -> s \in (intersect t1 t2). Admitted.

    Lemma notin_union_l: ~ s \in (union t1 t2) -> ~ s \in t1. Admitted.

    Lemma notin_union_r: ~ s \in (union t1 t2) -> ~ s \in t2. Admitted.

    Lemma in_union_l: s \in t1 -> s \in (union t1 t2). Admitted.

    Lemma in_union_r: s \in t2 -> s \in (union t1 t2). Admitted.

    Lemma in_union_other_l: s \in (union t1 t2) -> ~ s \in t1 -> s \in t2. Admitted.

    Lemma in_union_other_r: s \in (union t1 t2) -> ~ s \in t2 -> s \in t1. Admitted.

    Lemma notin_union: ~ s \in t1 -> ~ s \in t2 -> ~ s \in (union t1 t2). Admitted.

    Lemma invert_in_diff_l: s \in (diff t1 t2) -> s \in t1. Admitted.

    Lemma invert_in_diff_r: s \in (diff t1 t2) -> ~ s \in t2. Admitted.

    Lemma notin_diff_l: ~ s \in t1 -> ~ s \in (diff t1 t2). Admitted.

    Lemma notin_diff_r: s \in t2 -> ~ s \in (diff t1 t2). Admitted.

    Lemma notin_diff_other_l: ~ s \in (diff t1 t2) -> s \in t1 -> s \in t2. Admitted.

    Lemma notin_diff_other_r: ~ s \in (diff t1 t2) -> ~ s \in t2 -> ~ s \in t1. Admitted.

    Lemma notin_diff: s \in t1 -> ~ s \in t2 -> s \in (diff t1 t2). Admitted.

  End union_intersect_diff_contains_lemmas.

End lemmas.
