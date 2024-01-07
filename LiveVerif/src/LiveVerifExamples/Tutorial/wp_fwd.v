Require Import LiveVerif.LiveVerifLib.
Require Import bedrock2.NotationsCustomEntry.

Load LiveVerif.

Notation "{{{ c }}}" := c (at level 0, c custom bedrock_cmd, format "{{{  c  }}}").
Notation wp := exec.

Lemma ex1: forall fs t m a,
    wp fs {{{ $"b" = $"a" - $42; $"c" = $"b" + $42 }}}
       t m (map.of_list [|("a", a)|])
       (fun t' m' l' => t' = t /\ m' = m /\
          l' = map.of_list [|("a", a); ("b", a ^- /[42]); ("c", a)|]).
Proof.
  intros.
  eapply wp_seq.
  eapply wp_set00.
  eapply dexpr_binop.
  eapply dexpr_var. compute. reflexivity.
  eapply dexpr_literal.

  change (map.put (map.of_list [|("a", a)|]) "b" (interp_binop bopname.sub a /[42]))
    with (map.of_list [|("a", a); ("b", a ^- /[42])|]).

  eapply wp_set00.
  eapply dexpr_binop.
  eapply dexpr_var. reflexivity.
  eapply dexpr_literal.
  ssplit.
  reflexivity.
  reflexivity.
  unfold interp_binop.
  replace (a ^- /[42] ^+ /[42]) with a by ring.
  reflexivity.
Qed.

End LiveVerif.
