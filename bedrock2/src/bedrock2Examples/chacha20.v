Require bedrock2.BasicC64Semantics bedrock2.NotationsCustomEntry.
Import BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Require Import coqutil.Macros.ident_to_string.

Section chacha20.
  Import bedrock2.Syntax Syntax.Coercions NotationsCustomEntry.

  Local Notation "x <<<= n" := (cmd.set (ident_to_string! x) (expr.op bopname.slu (ident_to_string! x) n)) (in custom bedrock_cmd at level 0, x ident, n bigint).
  Local Notation "x ^= e" := (cmd.set (ident_to_string! x) (expr.op bopname.xor (ident_to_string! x) e)) (in custom bedrock_cmd at level 0, x ident, e custom bedrock_expr).
  Local Notation "x += e" := (cmd.set (ident_to_string! x) (expr.op bopname.add (ident_to_string! x) e)) (in custom bedrock_cmd at level 0, x ident, e custom bedrock_expr).

  Definition chacha20_quarter : func :=
    ("chacha20_quarter", (["a";"b";"c";"d"], ["a";"b";"c";"d"], bedrock_func_body:(
      a += b; d ^= a; d <<<= 16;
      c += d; b ^= c; b <<<= 12;
      a += b; d ^= a; d <<<= 8;
      c += d; b ^= c; b <<<= 7
    ))).

  Definition QUARTERROUND (a b c d : String.string) : cmd
    := ltac:(let body := (eval cbv [chacha20_quarter] in (let '(_, (_, _, body)) := chacha20_quarter in body)) in
             lazymatch (eval pattern "a", "b", "c", "d" in body) with
             | ?x "a" "b" "c" "d"
               => let y := (eval cbv beta in (x a b c d)) in
                  exact y
             end).

  Local Notation "'xorout' o x" := (
      let addr := bedrock_expr:(out+coq:(expr.literal(4*o))) in
      bedrock_cmd:(store4($addr, load4($addr)^$(expr.var (ident_to_string! x)))))
      (in custom bedrock_cmd at level 0, o bigint, x ident).

  Definition chacha20_block_separate : func :=
    (* NOTE: I (andreser) don't understand why xorout needs these *)
    let x0  := "x0" in let x1  := "x1" in let x2  := "x2" in let x3  := "x3" in
    let x4  := "x4" in let x5  := "x5" in let x6  := "x6" in let x7  := "x7" in
    let x8  := "x8" in let x9  := "x9" in let x10 := "x10" in let x11 := "x11" in
    let x12 := "x12" in let x13 := "x13" in let x14 := "x14" in let x15 := "x15" in
    ("chacha20_block", (["out"; "key"; "nonce"; "countervalue"], [], bedrock_func_body:(
      x0 = $0x61707865;   x1 = $0x3320646e;   x2 = $0x79622d32;    x3 = $0x6b206574;
      x4 = load4(key);           x5 = load4(key+$4);   x6 = load4(key+$8);    x7 = load4(key+$12);
      x8 = load4(key+$16);  x9 = load4(key+$20); x10 = load4(key+$24);  x11 = load4(key+$28);
      x12 = countervalue;       x13 = load4(nonce);        x14 = load4(nonce+$4); x15 = load4(nonce+$8);
      i = $0; while (i < $10) { i += $1;
        (x0, x4,  x8, x12) = chacha20_quarter( x0, x4, x8,  x12);
        (x1, x5,  x9, x13) = chacha20_quarter( x1, x5, x9,  x13);
        (x2, x6, x10, x14) = chacha20_quarter( x2, x6, x10, x14);
        (x3, x7, x11, x15) = chacha20_quarter( x3, x7, x11, x15);
        (x0, x5, x10, x15) = chacha20_quarter( x0, x5, x10, x15);
        (x1, x6, x11, x12) = chacha20_quarter( x1, x6, x11, x12);
        (x2, x7,  x8, x13) = chacha20_quarter( x2, x7, x8,  x13);
        (x3, x4,  x9, x14) = chacha20_quarter( x3, x4, x9,  x14)
      };
      x0 += $0x61707865;  x1 += $0x3320646e;   x2 += $0x79622d32;    x3 += $0x6b206574;
      x4 += load4(key);          x5 += load4(key+$4);   x6 += load4(key+$8);    x7 += load4(key+$12);
      x8 += load4(key+$16); x9 += load4(key+$20); x10 += load4(key+$24);  x11 += load4(key+$28);
      x12 += countervalue;      x13 += load4(nonce);        x14 += load4(nonce+$4); x15 += load4(nonce+$8);
      xorout  0  x0;   xorout 1 x1; xorout 2   x2;  xorout 3  x3;
      xorout  4  x4;   xorout 5 x5; xorout 6   x6;  xorout 7  x7;
      xorout  8  x8;   xorout 9 x9; xorout 10 x10; xorout 11 x11;
      xorout 12 x12; xorout 13 x13; xorout 14 x14; xorout 15 x15
  ))).

  Local Ltac repquarterround body :=
    lazymatch body with
    | context body[cmd.call [?x1; ?x2; ?x3; ?x4] "chacha20_quarter" [expr.var ?x1; expr.var ?x2; expr.var ?x3; expr.var ?x4] ]
      => let body := context body[QUARTERROUND x1 x2 x3 x4] in
         repquarterround body
    | context body[cmd.call ?ls "chacha20_quarter" ?ls' ]
      => let v := constr:(cmd.call ls "chacha20_quarter" ls') in
         fail 0 "could not replace ""chacha20_quarter"" in" v
    | context["chacha20_quarter"]
      => fail 0 "could not replace ""chacha20_quarter"" in" body
    | _ => body
    end.
  Definition chacha20_block : func :=
    ltac:(let body := (eval cbv delta [chacha20_block_separate] in chacha20_block_separate) in
          let body := repquarterround body in
          exact body).
End chacha20.

(*
Require bedrock2.ToCString.
Example chacha20_block_c_string := Eval vm_compute in
  ToCString.c_module [chacha20_quarter; chacha20_block_separate].
Print chacha20_block_c_string.
*)

From Coq Require Import String.
From Coq Require Import ZArith.ZArith.
From coqutil Require Import Word.Interface Word.Properties Map.Interface.
From coqutil.Word Require Import Naive.
From coqutil.Tactics Require Import letexists eabstract.
From bedrock2 Require Import FE310CSemantics Semantics WeakestPrecondition ProgramLogic Array Scalars Loops.
From bedrock2.Map Require Import Separation SeparationLogic.
From coqutil.Z Require Import Lia.

Local Infix "*" := sep.
Local Infix "*" := sep : type_scope.

Local Existing Instance coqutil.Word.Naive.word.

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
