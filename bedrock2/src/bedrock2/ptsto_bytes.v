Require Import Coq.ZArith.BinInt Coq.setoid_ring.Ring_tac.
Require Import coqutil.Word.Interface coqutil.Word.Properties Coq.Init.Byte.
Require Import coqutil.Map.Interface bedrock2.Map.SeparationLogic. 
Import Map.Separation.Coercions.
Require Import bedrock2.Memory.
Local Open Scope Z_scope.

Require Import coqutil.Map.OfListWord.
Section WithWord.
  Local Coercion Z.of_nat : nat >-> Z.
  Local Open Scope sep_scope.
  Context {width : Z} {word : Word.Interface.word width} {word_ok : word.ok word}.
  Context [value] [map : map.map word value] {ok : map.ok map}.
  Add Ring __wring: (@word.ring_theory width word word_ok).
  Lemma sep_of_app (a : word) (xs ys : list value)
    lxs (Hlxs : Z.of_nat (length xs) = lxs) (Htotal : length xs + length ys <= 2^width)
    : Lift1Prop.iff1 ((xs ++ ys)$@a)
      (sep (xs$@a) (ys$@(word.add a (word.of_Z lxs)))).
  Proof.
    etransitivity.
    2: eapply sep_comm.
    etransitivity.
    2: eapply sep_eq_putmany, map.adjacent_arrays_disjoint_n; trivial.
    erewrite map.of_list_word_at_app_n by eauto; reflexivity.
  Qed.

  Lemma app_of_sep (a b : word) (xs ys : list value)
    (Hl: word.unsigned (word.sub b a) = Z.of_nat (length xs))
    (Htotal : length xs + length ys <= 2^width)
    : Lift1Prop.iff1 (xs$@a * ys$@b) ((xs++ys)$@a).
  Proof.
    etransitivity.
    2:symmetry; eapply sep_of_app; trivial.
    do 3 Morphisms.f_equiv. rewrite <-Hl, word.of_Z_unsigned. ring.
  Qed.
End WithWord.

Section WithMem.
  Context {width : Z} {word : Word.Interface.word width} {word_ok : word.ok word}.
  Context {mem : map.map word byte} {mem_ok : map.ok mem}.
  Lemma load_bytes_of_sep a n bs (Hn : length bs = n) (Hl : Z.of_nat n <= 2^width)
    R (m : mem) (Hsep : sep (bs$@a) R m) : Memory.load_bytes m a n = Some bs.
  Proof.
    eapply sep_comm in Hsep.
    case Hsep as (mR&?&(?&?)&?&Hmbs); destruct Hmbs; subst m.
    eauto using load_bytes_of_putmany_bytes_at.
  Qed.

  Lemma unchecked_store_bytes_of_sep(a: word)(oldbs bs: list byte)(R: mem -> Prop)(m: mem)
    (Hsep : sep (oldbs$@a) R m)(H:length bs = length oldbs)
    : sep (bs$@a) R (Memory.unchecked_store_bytes m a bs).
  Proof.
    cbv [unchecked_store_bytes].
    case Hsep as (mo&mR&(?&?)&?&?); subst m.
    destruct H2. (* subst mo *)
    eexists (bs$@a), mR; Tactics.ssplit; trivial; try reflexivity.
    assert (map.disjoint (bs$@a) mR).
    { cbv [map.disjoint] in *.
      intros k v1 v2; specialize (H1 k).
      erewrite map.get_of_list_word_at in *.
      intros HSome.
      eapply List.nth_error_Some_bound_index in HSome.
      destruct List.nth_error eqn:Hd in H1; eauto.
      eapply List.nth_error_None in Hd; Lia.lia. }
    split; trivial.
    rewrite <-Properties.map.putmany_assoc.
    rewrite (Properties.map.putmany_comm mR) by (eapply Properties.map.disjoint_comm; assumption).
    rewrite Properties.map.putmany_assoc.
    f_equal.
    eapply map.map_ext; intros k.
    erewrite Properties.map.get_putmany_dec; case map.get eqn:?; trivial.
    erewrite map.get_of_list_word_at in *.
    erewrite List.nth_error_None in *.
    Lia.lia.
  Qed.
End WithMem.
