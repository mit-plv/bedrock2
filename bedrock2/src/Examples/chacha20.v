Require Import bedrock2.BasicC64Syntax bedrock2.NotationsInConstr coqutil.Z.HexNotation.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Existing Instance bedrock2.BasicC64Syntax.StringNames_params.
Local Coercion var (x : string) : Syntax.expr := Syntax.expr.var x.

From coqutil.Macros Require Import unique subst.

Import BinInt String.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Section chacha20.
  Import bedrock2.NotationsInConstr.
  Local Coercion literal (z : Z) : expr := expr.literal z.

  Notation "x <<< n" := ((x << (n%Z)%bedrock_expr) .| (x >> (32 - n%Z)))%bedrock_expr (at level 100) : bedrock_expr.
  Notation "a <<<= b" := (subst! a for x in (x = (x <<< b)))%bedrock_cmd (at level 75) : bedrock_cmd.
  Notation "a ^= b" := (subst! a for x in (x = (x .^ b)))%bedrock_cmd (at level 75) : bedrock_cmd.
  Notation "a += b" := (subst! a for x in (x = (x + b)))%bedrock_cmd (at level 75) : bedrock_cmd.

  Definition QUARTERROUND (a b c d : varname) : cmd :=
    a += b;; d ^= a;; d <<<= 16;;
    c += d;; b ^= c;; b <<<= 12;;
    a += b;; d ^= a;; d <<<= 8;;
    c += d;; b ^= c;; b <<<= 7.

  Let out := "out". Let key := "key". Let countervalue := "countervalue". Let nonce := "nonce".
  Let i := "i".
  Let x0  := "x0". Let x1  := "x1". Let x2  := "x2". Let x3  := "x3".
  Let x4  := "x4". Let x5  := "x5". Let x6  := "x6". Let x7  := "x7".
  Let x8  := "x8". Let x9  := "x9". Let x10 := "x10". Let x11 := "x11".
  Let x12 := "x12". Let x13 := "x13". Let x14 := "x14". Let x15 := "x15".
  Definition xorout o x : cmd := *(uint32_t*)((out+literal(4*o))%bedrock_expr) = *(uint32_t*)((out+literal(4*o))) .^ x.
  Definition chacha20_block := ("chacha20_block", ((out::key::nonce::countervalue::nil), @nil varname, bedrock_func_body:(
    x0 = Ox"61707865";;          x1 = Ox"3320646e";;          x2 = Ox"79622d32";;            x3 = Ox"6b206574";;
    x4 = *(uint32_t*) key;;      x5 = *(uint32_t*) (key+4);;  x6 = *(uint32_t*) (key+8);;    x7 = *(uint32_t*) (key+12);;
    x8 = *(uint32_t*) (key+16);; x9 = *(uint32_t*) (key+20);; x10 = *(uint32_t*) (key+24);;  x11 = *(uint32_t*) (key+28);;
    x12 = countervalue;;         x13 = *(uint32_t*) nonce;;   x14 = *(uint32_t*) (nonce+4);; x15 = *(uint32_t*) (nonce+8);;
    i = 0;; while (i < 10) {{ i += 1;;
      QUARTERROUND x0 x4 x8  x12;;
      QUARTERROUND x1 x5 x9  x13;;
      QUARTERROUND x2 x6 x10 x14;;
      QUARTERROUND x3 x7 x11 x15;;
      QUARTERROUND x0 x5 x10 x15;;
      QUARTERROUND x1 x6 x11 x12;;
      QUARTERROUND x2 x7 x8  x13;;
      QUARTERROUND x3 x4 x9  x14
    }};;
    x0 += Ox"61707865";;          x1 += Ox"3320646e";;          x2 += Ox"79622d32";;            x3 += Ox"6b206574";;
    x4 += *(uint32_t*) key;;      x5 += *(uint32_t*) (key+4);;  x6 += *(uint32_t*) (key+8);;    x7 += *(uint32_t*) (key+12);;
    x8 += *(uint32_t*) (key+16);; x9 += *(uint32_t*) (key+20);; x10 += *(uint32_t*) (key+24);;  x11 += *(uint32_t*) (key+28);;
    x12 += countervalue;;         x13 += *(uint32_t*) nonce;;   x14 += *(uint32_t*) (nonce+4);; x15 += *(uint32_t*) (nonce+8);;
    xorout  0  x0;;   xorout 1 x1;; xorout 2   x2;;  xorout 3 x3;;
    xorout  4  x4;;   xorout 5 x5;; xorout 6   x6;;  xorout 7 x7;;
    xorout  8  x8;;   xorout 9 x9;; xorout 10 x10;; xorout 11 x11;;
    xorout 12 x12;; xorout 13 x13;; xorout 14 x14;; xorout 15 x15
  ))).
End chacha20.

(*
Example chacha20_block_c_string := Eval vm_compute in
  BasicC64Syntax.c_func ("chacha20_block", (chacha20_block )).
Print chacha20_block_c_string.
*)

From Coq Require Import ZArith.ZArith.
From coqutil Require Import Word.Interface Word.Properties Map.Interface.
From coqutil.Word Require Import Naive.
From coqutil.Tactics Require Import letexists eabstract.
From bedrock2 Require Import FE310CSemantics Semantics WeakestPrecondition ProgramLogic Array Scalars TailRecursion.
From bedrock2.Map Require Import Separation SeparationLogic.
From coqutil.Z Require Import Lia.

Local Infix "*" := sep.
Local Infix "*" := sep : type_scope.

Local Instance word32: Interface.word 32 := coqutil.Word.Naive.word 32 eq_refl.
Local Instance word32_ok: word.ok word32 := coqutil.Word.Naive.ok _ _.
Local Instance byte_ok: word.ok byte := coqutil.Word.Naive.ok _ _.
Local Instance mapok: map.ok mem := SortedListWord.ok (Naive.word 32 eq_refl) _.
Local Instance wordok: word.ok word := coqutil.Word.Naive.ok _ _.

Instance spec_of_chacha20 : spec_of "chacha20_block" := fun functions =>
  forall outAddr out keyAddr key nonceAddr nonce cval R m t,
    (array scalar32 (word.of_Z 4) outAddr out *
     array scalar32 (word.of_Z 4) keyAddr key *
     array scalar32 (word.of_Z 4) nonceAddr nonce *
     R) m ->
    16 = Z.of_nat (List.length out) ->
    8 = Z.of_nat (List.length key) ->
    3 = Z.of_nat (List.length nonce) ->
    WeakestPrecondition.call functions "chacha20_block" t m [outAddr; keyAddr; nonceAddr; cval]
                             (fun t' m' rets => exists out',
                                  t' = t /\ (array scalar32 (word.of_Z 4) outAddr out' *
                                            array scalar32 (word.of_Z 4) keyAddr key *
                                            array scalar32 (word.of_Z 4) nonceAddr nonce *
                                            R) m' /\ rets = []).

Hint Rewrite
     word.unsigned_of_Z word.signed_of_Z word.of_Z_unsigned word.unsigned_add word.unsigned_sub word.unsigned_opp word.unsigned_or word.unsigned_and word.unsigned_xor word.unsigned_not word.unsigned_ndn word.unsigned_mul word.signed_mulhss word.signed_mulhsu word.unsigned_mulhuu word.unsigned_divu word.signed_divs word.unsigned_modu word.signed_mods word.unsigned_slu word.unsigned_sru word.signed_srs word.unsigned_eqb word.unsigned_ltu word.signed_lts
     using trivial
  : word_laws.

Monomorphic Definition word__monomorphic_ring_theory := Properties.word.ring_theory (word := word).
Add Ring word_ring : word__monomorphic_ring_theory.

Lemma chacha20_ok : program_logic_goal_for_function! chacha20_block.
Proof.
  straightline.
  repeat (destruct out; [cbn in H0; congruence |]).
  repeat (destruct key; [cbn in H1; congruence |]).
  repeat (destruct nonce; [cbn in H2; congruence |]).
  cbn [array word.add word.of_Z] in H.
  Local Ltac word_add_trans_one addr :=
    match goal with
    | [ H : context[@word.add _ ?w (word.add addr ?x) ?y] |- _ ] =>
      replace (@word.add _ w (word.add addr x) y) with (@word.add _ w addr (word.add x y)) in H by ring
    end.
  Local Ltac word_add_trans addr :=
    repeat word_add_trans_one addr.
  word_add_trans outAddr.
  word_add_trans keyAddr.
  word_add_trans nonceAddr.
  repeat match goal with
         | [ H : context[@word.add _ ?w (word.of_Z ?x) (word.of_Z ?y)] |- _ ] =>
           let z := eval cbv in (x + y) in
               change (@word.add _ w (word.of_Z x) (word.of_Z y)) with (@word.of_Z _ w z) in H
         end.
  repeat straightline.
  subst c95.
  match type of H with
  | ?f m => set (Hsep := f)
  end.
  refine (tailrec (HList.polymorphic_list.nil) ("i"::"out"::"key"::"nonce"::"countervalue"::"x0"::"x1"::"x2"::"x3"::"x4"::"x5"::"x6"::"x7"::"x8"::"x9"::"x10"::"x11"::"x12"::"x13"::"x14"::"x15"::nil)%list%string (fun l t m i out key nonce cval _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => PrimitivePair.pair.mk (Hsep m /\ word.unsigned i = 10 - Z.of_nat l /\ (l <= 10)%nat) (fun T M I OUT KEY NONCE CVAL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => T = t /\ OUT = out /\ KEY = key /\ NONCE = nonce /\ CVAL = cval /\ Hsep M)) lt _ _ _ _ _);
    cbn [reconstruct map.putmany_of_list HList.tuple.to_list
         HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *.

  { repeat straightline. }
  { exact lt_wf. }
  { split; [| split].
    { subst Hsep.
      ecancel_assumption. }
    { subst i.
      rewrite word.unsigned_of_Z.
      cbv [word.wrap].
      rewrite Zmod_0_l.
      match goal with
      | [ |- _ = _ - Z.of_nat ?n ] =>
        unify n (10%nat)
      end.
      reflexivity.
    }
    { blia. }
  }
  { straightline.
    straightline.
    do 5 straightline.
    straightline.
    straightline.
    do 100 straightline.
    2: solve [intuition].
    straightline.
    straightline.
    straightline.
    straightline.
    do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.

    (* prove [enforce] *)
    match goal with |- Markers.unique (Markers.left (exists x131 x132 x133 x134 x135 x136 x137 x138 x139 x140 x141 x142 x143 x144 x145 x146 x147 x148 x149 x150 x151, _)) => idtac end.

    repeat letexists. split.
    { 
      cbv [enforce gather].
      repeat match goal with
      | |- context G [@map.get ?K ?V ?M ?m ?k] =>
        let v := match goal with H := context [map.put _ k ?v] |- _ => v end in
        let goal := context G [Some v] in
        change goal
      end.
    cbv beta iota.
    split; refine eq_refl.
    }

    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time straightline.
    Time straightline.
    Time straightline.

    letexists. split.
    2:split.
    1: split.
    2: split.

    all : repeat straightline.
    all : try typeclasses eauto with core.

    {
      lazymatch goal with
      | [ H : word.unsigned br <> 0 |- _ ] =>
        subst br;
          rewrite word.unsigned_ltu in H;
          lazymatch type of H with
          | word.unsigned (if ?x <? ?y then _ else _) <> _ =>
            destruct (Z.ltb_spec0 x y) as [Hv |];
              rewrite word.unsigned_of_Z in H;
              cbv in H;
              [| congruence]
          end
      end.
      subst x131.
      subst v'.
      match goal with
      | [ |- word.unsigned ?w = _ ] =>
        change w with (word.add x (word.of_Z 1))
      end.
      rewrite word.unsigned_add, word.unsigned_of_Z.
      match goal with
      | [ H : word.unsigned _ = 10 - _ |- _ ] =>
        rewrite H in *
      end.
      rewrite word.unsigned_of_Z in Hv.
      change (word.wrap 10) with 10 in Hv.
      instantiate (1 := Nat.pred v).
      rewrite Nat2Z.inj_pred; [| blia].
      change (word.wrap 1) with 1.
      cbv [word.wrap].
      rewrite Z.mod_small; [blia |].
      split; [blia |].
      match goal with
      | [ H : (_ <= _)%nat |- _ ] =>
        let H' := fresh "H" in
        pose proof (inj_le _ _ H) as H'; cbn in H'
      end.
      match goal with
      | [ |- _ < 2^?w ] =>
          let w' := eval cbv in w in
          change w with w'
      end.
      blia.
    }
    { subst v'. blia. }
    { subst v'.
      lazymatch goal with
      | [ H : word.unsigned br <> 0 |- _ ] =>
        subst br;
          rewrite word.unsigned_ltu in H;
          lazymatch type of H with
          | word.unsigned (if ?x <? ?y then _ else _) <> _ =>
            destruct (Z.ltb_spec0 x y) as [Hv |];
              rewrite word.unsigned_of_Z in H;
              cbv in H;
              [| congruence]
          end
      end.
      match goal with
      | [ H : word.unsigned _ = 10 - _ |- _ ] =>
        rewrite H in *
      end.
      rewrite word.unsigned_of_Z in Hv.
      change (word.wrap 10) with 10 in Hv.
      apply lt_pred_n_n.
      apply Nat2Z.inj_lt.
      blia.
    }
  }

  subst Hsep.
  repeat straightline.
  replace (scalar32 x47 r) with (scalar32 (word.add x47 (word.of_Z 0)) r) in H8.
  2: {
    f_equal.
    1: {
      intros.
      rewrite H9.
      reflexivity.
    }
    ring.
  }
  repeat straightline.
  intuition.
  destruct out; cbn in H0; [| blia].
  cbn [array] in H19.
  let x := open_constr:(@cons word32 _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ nil)))))))))))))))) in
  unify out' x.
  subst out'.
  cbn [array].
  repeat match goal with
  | [ |- context[@word.add _ ?w (word.add x47 ?x) ?y] ] =>
    replace (@word.add _ w (word.add x47 x) y) with (@word.add _ w x47 (word.add x y)) by ring
  end.
  repeat match goal with
  | [ |- context[@word.add _ ?w (word.add x16 ?x) ?y] ] =>
    replace (@word.add _ w (word.add x16 x) y) with (@word.add _ w x16 (word.add x y)) by ring
  end.
  repeat match goal with
  | [ |- context[@word.add _ ?w (word.add x17 ?x) ?y] ] =>
    replace (@word.add _ w (word.add x17 x) y) with (@word.add _ w x17 (word.add x y)) by ring
  end.
  repeat match goal with
         | [ |- context[@word.add _ ?w (word.of_Z ?x) (word.of_Z ?y)] ] =>
           let z := eval cbv in (x + y) in
               change (@word.add _ w (word.of_Z x) (word.of_Z y)) with (@word.of_Z _ w z)
         end.
  rewrite !word.of_Z_unsigned in H19.
  repeat match type of H19 with
         | context[scalar32 ?a _] =>
           subst a
         end.
  replace (word.add x47 (word.of_Z 0)) with x47 in H19 by ring.
  ecancel_assumption.
Defined.
