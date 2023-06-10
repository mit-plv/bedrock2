(* -*- eval: (load-file "../../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Load LiveVerif.

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
  | |- don't_know_how_to_prove_equal (l[\[i]:][:\[count]]) (l[\[i]:][:\[count] + 123]) =>
      idtac
  end.
Abort.

End LiveVerif. Comments .**/ //.
