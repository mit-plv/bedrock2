(* -*- eval: (load-file "../../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Load LiveVerif.

Variable foo: word -> word -> mem -> Prop.

Goal forall (p v1 v2: word) R (m' m1 m: mem),
    m1 |= R ->
    mmap.du m1 m = m' ->
    m |= foo v1 p ->
  <{ * foo v2 p
     * R }> m'.
Proof.
  intros. steps.
  lazymatch goal with
  | _: warning_marker (PredicateSize_not_found (foo _)) |- _ => idtac
  end.
Abort.

#[local] Hint Extern 1 (PredicateSize foo) => exact 4 : typeclass_instances.

Goal forall (p v1 v2: word) R (m' m1 m: mem),
    m1 |= R ->
    mmap.du m1 m = m' ->
    m |= foo v1 p ->
  <{ * foo v2 p
     * R }> m'.
Proof.
  intros. steps.
  test_error Error:("Cannot cancel" (foo v2 p) "with" (foo v1 p)
                      "even though both span the same range:" 4 "bytes from" p).
Abort.

Goal forall n l (i j count p: word) R (m' m1 m: mem),
    m1 |= R ->
    mmap.du m1 m = m' ->
    m |= array (uint 16) n
           (l[:\[i]] ++
            l[\[j]:][:\[count]] ++
            l[\[i] + \[count] : \[j]] ++ l[\[i]:][:\[count]] ++ l[\[count] + \[j]:]) p ->
  <{ * array (uint 16) n
         (l[:\[i]] ++
          l[\[j]:][:\[count]] ++
          l[\[i] + \[count] : \[j]] ++ l[\[i]:][:\[count] + 123] ++ l[\[count] + \[j]:]) p
     * R }> m'.
Proof.
  intros. steps.
  lazymatch goal with
  | |- don't_know_how_to_prove eq \[count] (\[count] + 123) =>
      idtac
  end.
Abort.

End LiveVerif. Comments .**/ //.
