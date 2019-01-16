Require Import Coq.Strings.String Coq.ZArith.ZArith.
From bedrock2 Require Import NotationsInConstr ProgramLogic Map.Separation Array TailRecursion.

Require bedrock2.Examples.Demos.
Definition bsearch := @Demos.bsearch _ Demos.BinarySearch.StringNames.Inst.

From coqutil Require Import Word.Interface Map.Interface. (* coercions word and rep *)
From bedrock2 Require Import Semantics BasicC64Semantics.

Import HList List.
Definition littleendian (n : nat) (addr : word) (value : Z) : mem -> Prop :=
  array ptsto (word.of_Z 1) addr (tuple.to_list (LittleEndian.split n value)).
Definition scalar sz addr value : mem -> Prop :=
  littleendian (bytes_per (width:=width) sz) addr (word.unsigned value).

Lemma load_bytes_sep a n bs R m
  (Hsep : sep (array ptsto (word.of_Z 1) a (tuple.to_list bs)) R m)
  : Memory.load_bytes n m a = Some bs.
Proof.
  cbv [load_bytes footprint].
  revert dependent a; revert dependent R; revert dependent m; revert dependent n.
  induction n; [solve[cbn; intros []; trivial]|].
  intros [b0 bs] m R a Hsep.
  cbn in Hsep; eapply SeparationLogic.sep_assoc in Hsep.
  cbn [map.getmany_of_tuple tuple.option_all tuple.map tuple.unfoldn].
  erewrite SeparationLogic.get_sep by exact Hsep.
  setoid_rewrite IHn; [exact eq_refl|].
  cbn.
  refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ Hsep); clear Hsep.
  SeparationLogic.ecancel.
Admitted.

Lemma combine_split n z :
 LittleEndian.combine n (LittleEndian.split n z) = (z mod 2^(Z.of_nat n*8))%Z.
Proof.
  revert z; induction n.
  { cbn. intros. rewrite Z.mod_1_r. trivial. }
  { cbn [LittleEndian.split LittleEndian.combine PrimitivePair.pair._1 PrimitivePair.pair._2]; intros.
    erewrite IHn; clear IHn.
    rewrite word.unsigned_of_Z, Nat2Z.inj_succ, Z.mul_succ_l by Lia.lia.
    (* bitwise proof, automatable: *)
    eapply Z.bits_inj'; intros i Hi.
    repeat rewrite ?Z.lor_spec, ?Properties.Z.testbit_mod_pow2, ?Z.shiftl_spec, ?Z.shiftr_spec by Lia.lia.
    destruct (Z.ltb_spec0 i 8); cbn [andb orb].
    { rewrite (Z.testbit_neg_r _ (i-8)) by Lia.lia.
      rewrite Bool.andb_false_r, Bool.orb_false_r.
      destruct (Z.ltb_spec0 i (Z.of_nat n * 8 + 8)); trivial; Lia.lia. }
    { rewrite Z.shiftr_spec by Lia.lia.
      replace (i - 8 + 8)%Z with i by Lia.lia; f_equal.
      destruct
        (Z.ltb_spec0 (i-8) (Z.of_nat n * 8)),
        (Z.ltb_spec0 i (Z.of_nat n * 8 + 8));
        trivial; Lia.lia. } }
Qed.

Lemma load_sep sz addr value R m
  (Hsep : sep (scalar sz addr value) R m)
  : Memory.load sz m addr = Some (word.and value (word.of_Z (Z.ones (Z.of_nat (bytes_per (width:=width) sz)*8)))).
Proof.
  cbv [load scalar littleendian] in *.
  erewrite load_bytes_sep by exact Hsep; apply f_equal.
  eapply Properties.word.unsigned_inj.
  rewrite combine_split.
  rewrite word.unsigned_and.
  rewrite !word.unsigned_of_Z.
  set (x := (Z.of_nat (bytes_per sz) * 8)%Z).
  assert ((0 <= x)%Z) by (subst x; destruct sz; Lia.lia).
  (* bitwise proof, automatable: *)
  eapply Z.bits_inj'; intros i Hi.
  repeat rewrite ?Properties.Z.testbit_mod_pow2, ?Properties.Z.testbit_ones, ?Z.lor_spec, ?Z.shiftl_spec, ?Z.shiftr_spec, ?Z.land_spec by (cbn; Lia.lia).
  repeat match goal with |- context[(?a <? ?b)%Z]
                         => destruct (Z.ltb_spec0 a b)
         end; try Btauto.btauto.
  destruct (Z.leb_spec0 0 i); cbn; try Btauto.btauto.
  Lia.lia.
Qed.

Lemma load_word_sep (sz := Syntax.access_size.word) addr value R m 
  (Hsep : sep (scalar sz addr value) R m)
  : Memory.load sz m addr = Some value.
Proof.
  erewrite load_sep by exact Hsep; f_equal.
  cbv [bytes_per sz].
  eapply Properties.word.unsigned_inj.
  rewrite !word.unsigned_and, !word.unsigned_of_Z.
  rewrite <-Properties.word.wrap_unsigned at 2.
  eapply Z.bits_inj'; intros i Hi.
  repeat rewrite ?Properties.Z.testbit_mod_pow2, ?Properties.Z.testbit_ones, ?Z.lor_spec, ?Z.shiftl_spec, ?Z.shiftr_spec, ?Z.land_spec by (cbn; Lia.lia).
  destruct (Z.ltb_spec0 i width); cbn [andb]; trivial; [].
  destruct (Z.testbit (word.unsigned value) i); cbn [andb]; trivial; [].
  destruct (Z.leb_spec0 0 i); try Lia.lia; cbn [andb]; [].
  eapply Z.ltb_lt.
  pose proof (word.width_pos : (0 < width)%Z) as H; clear - l H.
  rewrite Z2Nat.id.
Admitted.

Axiom ptsto_word :  word -> word -> mem -> Prop.
Instance spec_of_bsearch : spec_of "bsearch"%string := fun functions =>
  forall left right target xs R t m,
    sep (array ptsto_word (word.of_Z 4) left xs) R m ->
    WeakestPrecondition.call (fun _ => True) (fun _ => False) (fun _ _ => True) functions
      "bsearch"%string t m (left::right::target::nil)%list
      (fun t' m' rets => t=t' /\ sep (array ptsto_word (word.of_Z 4) left xs) R m' /\ exists i, rets = (i::nil)%list /\
      ((*sorted*)False -> True)
      ).

From coqutil.Tactics Require Import eabstract letexists rdelta.

Lemma swap_swap_ok : program_logic_goal_for_function! bsearch.
Proof.
  bind_body_of_function bsearch. cbv [spec_of_bsearch].

  intros.
  letexists. split. exact eq_refl. (* argument initialization *)

  Import Markers.hide.
  Import PrimitivePair.
  refine (
    tailrec (HList.polymorphic_list.cons (list word) (HList.polymorphic_list.nil)) ("left"::"right"::"target"::nil)%list%string
        (fun l xs t m left right target => PrimitivePair.pair.mk
          (List.length xs = l /\ sep (array ptsto_word (word.of_Z 4) left xs) R m)
        (fun      T M LEFT RIGHT TARGET => True))
        _ lt_wf _ _ _ _ _);
    
    cbn [reconstruct map.putmany_of_list HList.tuple.to_list
         HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
  { repeat straightline. }
  { admit. }
  { repeat straightline.
    (* TODO: fix seprewrite to actually rewrite not just factor *)
    evar (i:word.rep).
    eapply SeparationLogic.Proper_sep_iff1 in H1.
    3:reflexivity.
    2:symmetry.
    2:unshelve eapply (array_index_inbounds _ _ _ _ _ i _); shelve_unifiable.
    4:let i := rdelta i in unify i (word.divu (word.sub v0 left) (word.of_Z 4)).
    (* TODO: array rule:
    forall size left, p-left < length -> p-left mod size = 0 ->
    forall i, i = (p-left)/size -> *)
Abort All.
