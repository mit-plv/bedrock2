Require Import Coq.Strings.String Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import coqutil.Z.PushPullMod.
From bedrock2 Require Import NotationsInConstr ProgramLogic Map.Separation Array Scalars TailRecursion.

Require bedrock2.Examples.Demos.
Definition bsearch := @Demos.bsearch _ Demos.BinarySearch.StringNames.Inst.

From coqutil Require Import Datatypes.List Word.Interface Map.Interface. (* coercions word and rep *)
From bedrock2 Require Import Semantics BasicC64Semantics.

From coqutil Require Import Z.div_mod_to_equations.
From coqutil.Tactics Require Import syntactic_unify.
From coqutil.Tactics Require Import rdelta.

Require Import bedrock2.AbsintWordToZ.
Strategy -1000 [word parameters]. (* TODO where should this go? *)

Local Infix "^+" := word.add  (at level 50, left associativity).
Local Infix "^-" := word.sub  (at level 50, left associativity).
Local Infix "^<<" := word.slu  (at level 37, left associativity).
Local Infix "^>>" := word.sru  (at level 37, left associativity).
Local Notation "/_" := word.of_Z.      (* smaller angle: squeeze a Z into a word *)
Local Notation "\_" := word.unsigned.  (* supposed to be a denotation bracket;
                                          or bigger angle: let a word fly into the large Z space *)
Local Open Scope Z_scope.

From coqutil Require Import Z.div_mod_to_equations.
From bedrock2 Require Import Semantics BasicC64Semantics.

Import HList List.
Instance spec_of_bsearch : spec_of "bsearch"%string := fun functions =>
  forall left right target xs R t m,
    sep (array scalar (word.of_Z 8) left xs) R m ->
    \_ (right ^- left) = 8*Z.of_nat (Datatypes.length xs) ->
    WeakestPrecondition.call functions
      "bsearch"%string t m (left::right::target::nil)%list
      (fun t' m' rets => t=t' /\ sep (array scalar (word.of_Z 8) left xs) R m' /\ exists i, rets = (i::nil)%list /\
      ((*sorted*)False -> True)
      ).

From coqutil.Tactics Require Import eabstract letexists rdelta.
From coqutil.Macros Require Import symmetry.
Import PrimitivePair.

Lemma mix_eq_into_mod{lhs rhs m: Z}(E: lhs mod m = rhs)(a: Z):
    a mod m = (a - lhs + rhs) mod m.
Proof.
  intros. rewrite <- E. Z.mod_equality.
Qed.

Lemma mix_eq_into_unsigned{lhs: word}{rhs: Z}(E: word.unsigned lhs = rhs)(w: word):
  word.unsigned w = word.unsigned (word.add w (word.sub (word.of_Z rhs) lhs)).
Proof.
  intros.
  rewrite <- E.
  rewrite word.of_Z_unsigned.
  f_equal.
  ring.
Qed.

Lemma computable_bounds{lo v hi: Z}(H: andb (Z.leb lo v) (Z.ltb v hi) = true): lo <= v < hi.
Proof.
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply Z.leb_le in H1.
  apply Z.ltb_lt in H2.
  auto.
Qed.

Lemma computable_le{lo v: Z}(H: Z.leb lo v = true): lo <= v.
Proof. apply Z.leb_le. assumption. Qed.

Lemma computable_lt{lo v: Z}(H: Z.ltb lo v = true): lo < v.
Proof. apply Z.ltb_lt. assumption. Qed.

Local Unset Simplex. (* COQBUG(9615) *)
Lemma bsearch_ok : program_logic_goal_for_function! bsearch.
Proof.
  repeat straightline.

  refine (
    tailrec (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ HList.polymorphic_list.nil)) ("left"::"right"::"target"::nil)%list%string
        (fun l xs R t m left right target => PrimitivePair.pair.mk
                                               (sep (array scalar (word.of_Z 8) left xs) R m /\
                                                \_ (right ^- left) = 8*Z.of_nat (Datatypes.length xs) /\
                                                List.length xs = l)
        (fun        T M LEFT RIGHT TARGET => T = t /\ sep (array scalar (word.of_Z 8) left xs) R M))
        lt _ _ _ _ _ _ _);
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
  { eauto. }
  { repeat straightline.
    2: solve [auto]. (* exiting loop *)
    (* loop body *)
    rename H2 into length_rep. subst br. subst v0.

    Import Markers.hide. idtac.

    seprewrite @array_address_inbounds;
       [ ..|(* if expression *) exact eq_refl|letexists; split; [repeat straightline|]]. (* determines element *)
    { rewrite ?Properties.word.word_sub_add_l_same_l. rewrite ?Properties.word.word_sub_add_l_same_r.
      repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in progress (* COQBUG(9652) *) rewrite H end.
      (* rewrite length_rep in *. (* WHY is this necessary for blia? *) *)
      Z.div_mod_to_equations. blia. }
    { rewrite ?Properties.word.word_sub_add_l_same_l, ?Properties.word.word_sub_add_l_same_r.
      repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in progress (* COQBUG(9652) *) rewrite H end.
      Z.div_mod_to_equations. blia. }
    (* split if cases *) split; repeat straightline. (* code is processed, loop-go-again goals left behind *)
    { repeat letexists. split; [repeat straightline|].
      repeat letexists; repeat split; repeat straightline.
      { SeparationLogic.ecancel_assumption. }
      { subst v1. subst x7.
        clear H1 x8 H5 v0.

Ltac count_summands e :=
  lazymatch e with
  | Z.add ?a ?b => let m := count_summands a in
                   let n := count_summands b in
                   let r := eval cbv in (m + n) in r
  | Z.sub ?a ?b => let m := count_summands a in
                   let n := count_summands b in
                   let r := eval cbv in (m + n) in r
  | _ => Z.one
  end.

(*
let a := constr:((1 - 3) + (3 + 2 + 8)) in
let n := count_summands a in idtac n.
*)

Ltac rhs_fewer_summands E :=
   match type of E with
   | ?a mod ?x = ?b mod ?x =>
     let m := count_summands a in
     let n := count_summands b in
     let b := eval cbv in (Z.ltb n m) in
     lazymatch b with
     | true => idtac
     | false => fail "lhs has" m "summands, rhs has" n
     end
   end.


        rewrite length_skipn.
        clear -length_rep H4.

        Hint Rewrite
       word.unsigned_of_Z word.signed_of_Z word.of_Z_unsigned word.unsigned_add word.unsigned_sub word.unsigned_opp word.unsigned_or word.unsigned_and word.unsigned_xor word.unsigned_not word.unsigned_ndn word.unsigned_mul word.signed_mulhss word.signed_mulhsu word.unsigned_mulhuu word.unsigned_divu word.signed_divs word.unsigned_modu word.signed_mods word.unsigned_slu word.unsigned_sru word.signed_srs word.unsigned_eqb word.unsigned_ltu word.signed_lts
       using solve[reflexivity || trivial]
  : word_laws.

        autorewrite with word_laws in *. cbv [word.wrap] in *.
        rewrite Z.shiftr_div_pow2 by (apply computable_le; reflexivity).
        rewrite Z.shiftl_mul_pow2 by (apply computable_le; reflexivity).

Import coqutil.Z.PushPullMod.Z.
Ltac mod_free t ::=
  lazymatch t with
  | Z.modulo ?a ?b => fail "contains" a "mod" b
  | Z.add ?a ?b => mod_free a; mod_free b
  | Z.sub ?a ?b => mod_free a; mod_free b
  | Z.mul ?a ?b => mod_free a; mod_free b
  | _ => idtac
  end.



        Z.push_pull_mod.

        repeat match goal with
                 (* if COQBUG https://github.com/coq/coq/issues/7672 was fixed, no context
                    match would be needed here *)
               | |- context[?a mod ?m] => rewrite (Z.mod_small a m) by
                     (apply computable_bounds; reflexivity)
               end.

        repeat match goal with
               | |- context[?x mod _] => progress ring_simplify x
               end.

        repeat match goal with
        | E: ?lhs mod ?m = ?rhs |- context[?e mod ?m] =>
          let F := named_pose_proof (mix_eq_into_mod E e) in
          match type of F with
          | _ = ?R mod m => ring_simplify R in F
          end;
          rhs_fewer_summands F;
          rewrite F;
          clear F;
          (* removing the modulo, so let's remember its bounds: *)
          let B := named_pose_proof (Z.mod_pos_bound lhs m eq_refl) in
          rewrite E in B
        end.

        Z.push_pull_mod.

        (* here... first do it manually *)


        (* not a good reason for rewriting
        match goal with
        | H: ?a mod ?m = ?b |- context[?a mod ?m] =>
          Z.mod_free b;
            rewrite H
        end.
        *)

        (* better reason: *)
        rewrite (mix_eq_into_mod length_rep). (* wrong place *)
        repeat match goal with
               | |- context[?x mod _] => progress ring_simplify x
               end.
        (* TODO confirm that it was good by doing count_summands before/after *)

        Z.push_pull_mod.

        repeat match goal with
               | |- context[?x mod _] => progress ring_simplify x
               end.


Search Z.shiftl Z.mul.

        rewrite word.unsigned_slu by reflexivity.
        rewrite word.unsigned_sru by reflexivity.

2: reflexivity.
2: cbv.

(*-------------------------*)

(* does one simplification step *)
Ltac wsimp e parentIsWord simplifier :=
  first
  [ (* try to simplify child expression *)
    lazymatch e with
    | @word.add _ _ ?a ?b => first [ wsimp a true simplifier | wsimp b true simplifier ]
    | @word.mul _ _ ?a ?b => first [ wsimp a true simplifier | wsimp b true simplifier ]
    | @word.sub _ _ ?a ?b => first [ wsimp a true simplifier | wsimp b true simplifier ]
    | @word.opp _ _ ?a    =>         wsimp a true simplifier
    | ?f ?a               => first [ wsimp f false simplifier | wsimp a false simplifier ]
    end
  | (* If we're here, no child expression could be simplified. *)
    lazymatch parentIsWord with false => idtac end;
    lazymatch e with
    | @word.add _ _ _ _ => idtac
    | @word.mul _ _ _ _ => idtac
    | @word.sub _ _ _ _ => idtac
    | @word.opp _ _ _   => idtac
    end;
    progress (simplifier e)
  ].

Ltac wsimp_goal :=
  repeat match goal with
         | |- ?G =>  wsimp G false ltac:(fun e => ring_simplify e)
         end.

Ltac wsimp_hyps :=
  repeat match goal with
         | H: ?P |- _ => wsimp P false ltac:(fun e => ring_simplify e in H)
         end.

Ltac wsimp_star := wsimp_goal; wsimp_hyps.

Ltac lia2 := PreOmega.zify; rewrite ?Z2Nat.id in *; Z.div_mod_to_equations; blia.

        rewrite length_skipn.
        clear -length_rep H4.

        Hint Rewrite
       word.unsigned_of_Z word.signed_of_Z word.of_Z_unsigned word.unsigned_add word.unsigned_sub word.unsigned_opp word.unsigned_or word.unsigned_and word.unsigned_xor word.unsigned_not word.unsigned_ndn word.unsigned_mul word.signed_mulhss word.signed_mulhsu word.unsigned_mulhuu word.unsigned_divu word.signed_divs word.unsigned_modu word.signed_mods word.unsigned_slu word.unsigned_sru word.signed_srs word.unsigned_eqb word.unsigned_ltu word.signed_lts
       using solve[trivial]
  : word_laws.



        Ltac count_summands e :=
          lazymatch e with
          | word.add ?a ?b => let m := count_summands a in
                              let n := count_summands b in
                              let r := eval cbv in (m + n) in r
          | word.sub ?a ?b => let m := count_summands a in
                              let n := count_summands b in
                              let r := eval cbv in (m + n) in r
          | _ => Z.one
          end.

(*

          let a := constr:(word.add (word.sub (word.of_Z 1) (word.of_Z 44)) (word.add (word.of_Z 1) (word.of_Z 44))) in
          let n := count_summands a
          in idtac n.
*)

Ltac rhs_fewer_summands E :=
   match type of E with
   | word.unsigned ?a = word.unsigned ?b =>
     let m := count_summands a in
     let n := count_summands b in
     let b := eval cbv in (Z.ltb n m) in
     lazymatch b with
     | true => idtac
     | false => fail "lhs has" m "summands, rhs has" n
     end
   end.




        match goal with
        | E: word.unsigned ?lhs = ?rhs |- context[word.unsigned ?e] =>
          let F := named_pose_proof (mix_eq_into_unsigned E e) in
          match type of F with
          | _ = word.unsigned ?R => ring_simplify R in F
          end;
          rhs_fewer_summands F;
          rewrite F;
          clear F;
          let B := named_pose_proof (Properties.word.unsigned_range lhs) in
          rewrite E in B
        end.



(* problem: ring_simplify does an unwanted simplification,
if we put this into a loop two cases will undo each other

but actually, mix_eq_into_unsigned squeezes (8 * Z.of_nat (Datatypes.length x)) into a /_,
so let's better get rid of that?
 *)


        match goal with
        | |- context[word.add (word.opp ?a) ?b] =>
          replace (word.add (word.opp a) b) with (word.sub b a) by ring
        end.

        (* Don't do that on its own, because otherwise unsigned.zify will thing all bounds
           have already been inferred
          change @eq with @absint_eq in length_rep.*)

        repeat match goal with
               | |- context[word.unsigned ?e] =>
                 let H := unsigned.zify_expr e in progress (* COQBUG(9652) *) rewrite H
               end.
        (* the zify & rewrite loop did not do as much as it should *)
        match goal with
        | |- word.unsigned ?e = _ => let H := unsigned.zify_expr e in idtac H
        end. (* just absint_eq_refl, why does it not do more? *)
        match goal with
        | |- \_ (?a ^- ?b ^- ?c) = _ => replace (a ^- b ^- c) with (a ^- (b ^+ c)) by ring
        end.
        match goal with
        | |- word.unsigned ?e = _ => let H := unsigned.zify_expr e in idtac H
        end. (* still absint_eq_refl *)
        match goal with
        | |- word.unsigned (?a ^- ?b) = _ => let H := unsigned.zify_expr b in idtac H
        end. (* this part works! *)
        match goal with
        | |- word.unsigned (?a ^- ?b) = _ => let H := unsigned.zify_expr a in idtac H
        end. (* this part doesn't work, just absint_eq_refl *)

        (* doesn't help
        pose proof H3 as H3'.
        rewrite length_rep in H3'.
        match goal with
        | |- word.unsigned (?a ^- ?b) = _ => let H := unsigned.zify_expr a in idtac H
        end.
         *)

        (*
        Q: why did ring_simplify introduce word.mul of 8? because "simpler"
        Q: how to deal with that?
        *)

        let R := rbounded (8 * Z.of_nat (Datatypes.length x)) in idtac R.

Require Import Coq.Strings.String Coq.ZArith.ZArith.
From coqutil Require Import Word.Interface Word.Properties.
From coqutil Require Import Tactics.rdelta Z.div_mod_to_equations.
Require Import coqutil.Z.Lia.
Local Open Scope Z_scope.

Local Infix "=~>" := absint_eq (at level 70, no associativity).

Import bedrock2.AbsintWordToZ.unsigned.

  Ltac named_pose_asfresh_or_id x n :=
    let y := match constr:(Set) with _ => named_pose_asfresh x n | _ => x end in
    y.


  let r := rbounded (8 * (Z.of_nat (Datatypes.length x))) in idtac r. (* good *)


  let r := rbounded (8 * \_ (/_ (Z.of_nat (Datatypes.length x)))) in idtac r. (* todo: should be as good *)

  Ltac zify_expr e :=
    let re := rdelta e in
    let __ := match goal with _ => idtac "RE" re end in
    lazymatch type of e with
    | @word.rep ?width ?word_parameters =>
      match re with
      | _ => match goal with H: word.unsigned e =~> _ |- _ => H end
      | word.of_Z ?a =>
        let Ba := rbounded a in
        named_pose_proof (absint_of_Z a (boundscheck (X0:=0) (X1:=2^width) Ba (eq_refl true)) : @absint_eq Z (@word.unsigned _ word_parameters e) a)
      | word.and ?a ?b =>
        let Ha := zify_expr a in let Ra := lazymatch type of Ha with _ =~> ?x => x end in
        let Hb := zify_expr b in let Rb := lazymatch type of Hb with _ =~> ?x => x end in
        named_pose_proof (absint_mask_r a b Ra Ha Rb Hb eq_refl : @absint_eq Z (@word.unsigned _ word_parameters e) (Z.modulo Ra (Rb+1)))
      | word.and ?a ?b =>
        let Ha := zify_expr a in let Ra := lazymatch type of Ha with _ =~> ?x => x end in
        let Hb := zify_expr b in let Rb := lazymatch type of Hb with _ =~> ?x => x end in
        named_pose_proof (absint_mask_l a b Ra Ha Rb Hb eq_refl : @absint_eq Z (@word.unsigned _ word_parameters e) (Z.modulo Rb (Ra+1)))
      | ?op ?a ?b =>
        let Ha := zify_expr a in let Ra := lazymatch type of Ha with _ =~> ?x => x end in
        let Hb := zify_expr b in let Rb := lazymatch type of Hb with _ =~> ?x => x end in
        match op with
        | word.and =>
          named_pose_proof constr:(absint_and a b Ra Ha Rb Hb : @absint_eq Z (@word.unsigned _ word_parameters e) (Z.land Ra Rb))
        | word.or =>
          named_pose_proof constr:(absint_or a b Ra Ha Rb Hb : @absint_eq Z (@word.unsigned _ word_parameters e) (Z.lor Ra Rb))
        | word.xor =>
          named_pose_proof constr:(absint_xor a b Ra Ha Rb Hb : @absint_eq Z (@word.unsigned _ word_parameters e) (Z.lxor Ra Rb))
        | word.ndn =>
          named_pose_proof constr:(absint_ndn a b Ra Ha Rb Hb : @absint_eq Z (@word.unsigned _ word_parameters e) (Z.ldiff Ra Rb))

        | word.add =>
          let Re := named_pose_asfresh_or_id constr:(Ra+Rb) e in
          let Be := rbounded Re in
          let Hbounds := match type of Be with ?x0 <= ?x < ?x1 =>
                           constr:(@boundscheck x0 x x1 Be 0 (2^width) (@eq_refl bool true)) end in
          named_pose_proof constr:(absint_add a b Ra Ha Rb Hb Hbounds : @absint_eq Z (@word.unsigned _ word_parameters e) Re)
        | word.sub =>
          let Re := named_pose_asfresh_or_id constr:(Ra-Rb) e in
          let Be := rbounded Re in
          let Hbounds := match type of Be with ?x0 <= ?x < ?x1 =>
                           constr:(@boundscheck x0 x x1 Be 0 (2^width) (@eq_refl bool true)) end in
          named_pose_proof constr:(absint_sub a b Ra Ha Rb Hb Hbounds : @absint_eq Z (@word.unsigned _ word_parameters e) Re)
        | word.mul =>
          let __ := match goal with _ => idtac "heeere" end in
          let Re := named_pose_asfresh_or_id constr:(Ra*Rb) e in
          let __ := match goal with _ => idtac "Re-mul:" Re end in
          let Be := rbounded Re in
          let __ := match goal with _ => idtac "Be-mul:" Be end in
          let __ := match type of Be with ?T => idtac "of type" T end in
          let Hbounds := match type of Be with ?x0 <= ?x < ?x1 =>
                           constr:(@boundscheck x0 x x1 Be 0 (2^width) (@eq_refl bool true)) end in
          let __ := match goal with _ => idtac "Hbounds:" Hbounds end in
          named_pose_proof constr:(absint_mul a b Ra Ha Rb Hb Hbounds : @absint_eq Z (@word.unsigned _ word_parameters e) Re)

        | word.sru =>
          let Re := named_pose_asfresh_or_id constr:((Ra / 2^Rb)) e in
          let Bb := rbounded Rb in
          let pf := constr:(absint_sru a b Ra Ha Rb Hb (@boundscheck_lt _ Rb _ Bb width eq_refl): @absint_eq Z (@word.unsigned _ word_parameters e) Re) in
          named_pose_proof pf
        | word.slu =>
          let Re := named_pose_asfresh_or_id constr:((Ra * 2^Rb)) e in
          let Bb := rbounded Rb in
          let Be := rbounded Re in
          named_pose_proof (absint_slu a b Ra Ha Rb Hb (boundscheck (X0:=0) (X1:=2^width) Be (eq_refl true)) (@boundscheck_lt _ Rb _ Bb width eq_refl): @absint_eq Z (@word.unsigned _ word_parameters e) Re)
        | _ => (* unknown binop or bad bounds, don't backtrack to keep Ha and Hb *)
          constr:(@absint_eq_refl Z (@word.unsigned _ word_parameters e))
         (* TODO: divu, modu (how do we prove denominator nonzero?) *)
        end
      | _ =>
        constr:(@absint_eq_refl Z (@word.unsigned _ word_parameters e))
      end
    | Z =>
      match e with
      | _ => match goal with H: e =~> _ |- _ => H end
      | word.unsigned ?a => zify_expr a
      | _ => constr:(@absint_eq_refl Z e)
      end
    end.

  assert (8 * \_ (/_ (Z.of_nat (Datatypes.length x)))
          <= 8 * (Z.of_nat (Datatypes.length x))) as D. {
    rewrite word.unsigned_of_Z.
    apply Z.mul_le_mono_nonneg_l.
    Search (?a * _ <= ?a * _).
    all: admit.
  }


  let A := zify_expr (word.mul (/_ 8) (/_ (Z.of_nat (Datatypes.length x)))) in idtac "-->" A.
  (* debug why not better *)




        rewrite word.unsigned_sub. rewrite word.unsigned_add.
        rewrite word.unsigned_opp.

        repeat match goal with
               | |- context[word.unsigned ?e] =>
                 let H := unsigned.zify_expr e in progress (* COQBUG(9652) *) rewrite H
               end.



        repeat match goal with
               | |- context[word.unsigned ?x] => progress ring_simplify x
               end.


        match goal with
        | |- word.unsigned ?e = _ =>
          let H := unsigned.zify_expr e in pose proof H as AAA
        end.


        wsimp_goal.

        repeat match goal with
               | |- context[?x mod _] => progress ring_simplify x
               end.


  (*      autorewrite with word_laws in *.*)


        match goal with
        | |- word.unsigned ?e = _ =>
          let H := unsigned.zify_expr e in pose proof H as AAA
        end.
        rewrite AAA.

        repeat match goal with
               | |- context[word.unsigned ?e] =>
                 let H := unsigned.zify_expr e in progress (* COQBUG(9652) *) rewrite H
               end.

(* unsigned.zify_expr tries to have one word.unsigned as the only outermost word.unsigned,
   now add mix+simpl to this? no, unsigned.zify_expr does not do any simplification

 *)

        cbv [word.wrap] in *.

        Z.push_pull_mod.

        repeat match goal with
               | |- context[?x mod _] => progress ring_simplify x
               end.


        rewrite (mix_eq_into_mod length_rep).
        repeat match goal with
               | |- context[?x mod _] => progress ring_simplify x
               end.



        (* how to detect that "\_ (x2 ^- x1)" is 'interesting' and should be
           factored out/used for rewriting?

           Say RHS of "length_rep" is better than LHS because fewer word.unsigned/wrap/mods,
           try to rewrite with it as often as possible, do rewriting not syntactically but
           by subtracting LHS of length_rep.

           Given
           E: LHS = RHS
           Turn
           (blah) mod 2^width
           into
           (blah - LHS + RHS) mod 2^width
           if (blah - LHS + RHS) becomes simpler than (blah)
*)

        rewrite ?length_rep.

        (*
        autorewrite with word_laws. cbv [word.wrap].

        (* Z.push_pull_mod. <-- doesn't work as expected because
           pull_mod is blocked by mod inside division *)

        Z.unary_to_binary_minus. Z.push_mod. rewrite ?Zmod_mod.

        Notation "[ a ]_ m" := (a mod m) (at level 20, format "[ a ]_ m").
        idtac.

        Z.pull_mod.

        Print Ltac Z.push_pull_mod.
        *)

        repeat match goal with
               | |- context[?x mod _] => progress ring_simplify x
               end.


        repeat match goal with
               | |- context[word.unsigned ?e] =>
                 let H := unsigned.zify_expr e in progress (* COQBUG(9652) *) rewrite H
               end.

        rewrite Z.mod_small; cycle 1. {

            by lia2.
        lia2.



        replace (x2 ^- x1 ^- (x2 ^- x1) ^>> /_ 4 ^<< /_ 3 ^- /_ 8) with
            (x2 ^- x1 ^- (/_ 8 ^+ (x2 ^- x1) ^>> /_ 4 ^<< /_ 3)); [|wsimp_star; ring].
        rewrite word.unsigned_sub.

        (* push/pull mod??
        TODO delete it in compiler, update submodule
        TODO: can we use "ring_simplify [HH GG] (a - b + c)" to throw in additional equations? *)

        repeat match goal with
               | |- context[word.unsigned ?e] =>
                 let H := unsigned.zify_expr e in progress (* COQBUG(9652) *) rewrite H
               end.

        cbv [word.wrap].
        rewrite Z.mod_small by lia2.
        lia2.
      }

      { subst v'. subst v. subst x7.
        set (\_ (x1 ^+ (x2 ^- x1) ^>> /_ 4 ^<< /_ 3 ^- x1) / \_ (/_ 8)) as X.
        assert (X < Z.of_nat (Datatypes.length x)). {
          eapply Z.div_lt_upper_bound; [exact eq_refl|].
          rewrite ?Properties.word.word_sub_add_l_same_l, ?Properties.word.word_sub_add_l_same_r.
          repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H end.
          rewrite length_rep in *. (* WHY does lia need this? *)
          revert H4. clear. intros. Z.div_mod_to_equations. blia. }
        rewrite length_skipn; bomega. }
      SeparationLogic.seprewrite_in (symmetry! @array_address_inbounds) H6.
      { rewrite ?Properties.word.word_sub_add_l_same_l, ?Properties.word.word_sub_add_l_same_r.
        destruct x; cbn [Datatypes.length] in *.
        { rewrite Z.mul_0_r in length_rep. bomega. }
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H end.
        rewrite length_rep.  clear. Z.div_mod_to_equations. blia. }
      { rewrite ?Properties.word.word_sub_add_l_same_l, ?Properties.word.word_sub_add_l_same_r.
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H end.
        rewrite length_rep.  clear. Z.div_mod_to_equations. blia. }
      { exact eq_refl. }
      { SeparationLogic.ecancel_assumption. } }
    (* second branch of the if, very similar goals... *)
    { repeat letexists. split. 1: solve [repeat straightline].
      repeat letexists; repeat split; repeat straightline.
      { SeparationLogic.ecancel_assumption. }
      { subst v1. subst x7.
        rewrite ?Properties.word.word_sub_add_l_same_l, ?Properties.word.word_sub_add_l_same_r.
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in try rewrite H end.
        rewrite ?length_rep.
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in try rewrite H end.
        rewrite List.firstn_length_le; cycle 1.
        { assert (Datatypes.length x <> 0)%nat by bomega.
          revert H13. clear. intros. Z.div_mod_to_equations; zify; rewrite ?Z2Nat.id by blia; blia. }
        rewrite Z2Nat.id by (clear; Z.div_mod_to_equations; blia).
        clear. Z.div_mod_to_equations. blia. }
      { subst v. subst v'. subst x7.
        rewrite ?Properties.word.word_sub_add_l_same_l, ?Properties.word.word_sub_add_l_same_r.
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in try rewrite H end.
        rewrite ?length_rep.
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in try rewrite H end.
        assert (Datatypes.length x <> 0)%nat by bomega.
        rewrite List.firstn_length_le; cycle 1.
        { revert H12. clear. intros. Z.div_mod_to_equations; zify; rewrite ?Z2Nat.id by blia; blia. }
        revert H12. clear. zify. rewrite ?Z2Nat.id; (Z.div_mod_to_equations; blia). }
      subst x8. SeparationLogic.seprewrite_in (symmetry! @array_address_inbounds) H6.
      { rewrite ?Properties.word.word_sub_add_l_same_l, ?Properties.word.word_sub_add_l_same_r.
        destruct x; cbn [Datatypes.length] in *.
        { rewrite Z.mul_0_r in length_rep. bomega. }
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H end.
        rewrite length_rep.  clear. Z.div_mod_to_equations. blia. }
      { rewrite ?Properties.word.word_sub_add_l_same_l, ?Properties.word.word_sub_add_l_same_r.
        repeat match goal with |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H end.
        rewrite length_rep.  clear. Z.div_mod_to_equations. blia. }
      { exact eq_refl. }
      { SeparationLogic.ecancel_assumption. } } }
  repeat straightline.
  repeat apply conj; auto; []. (* postcondition *)
  letexists. split.
  { exact eq_refl. }
  { auto. }

  Unshelve.
  all: exact (word.of_Z 0).

  all:fail "remaining subgoals".
Qed.
(* Print Assumptions bsearch_ok. *)
(* SortedListString.string_strict_order *)
(* reconstruct_enforce *)
(* SortedListMap *)

Local Set Simplex.
