Require Import Coq.ZArith.ZArith Coq.micromega.Lia coqutil.Z.div_mod_to_equations.
Lemma div10_by_mul a : (0 <= a < 2^32 -> a/10 = (a*3435973837)/2^35)%Z.
Proof. intros. Z.div_mod_to_equations. Lia.lia. Qed.