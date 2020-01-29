Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Array.
Require Import bedrock2.BasicCSyntax.
Require Import bedrock2.BasicC64Semantics.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.Scalars.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Z.PushPullMod.
Require Import Rupicola.Examples.CapitalizeThird.CapitalizeThird.
Require bedrock2.WeakestPrecondition.
Require bedrock2.Semantics.
From coqutil.Tactics Require Import destr.
Local Open Scope Z_scope. Local Open Scope string_scope.
Import ListNotations.
Import CapitalizeThird.Bedrock2.

Hint Rewrite word.unsigned_add word.unsigned_mul word.unsigned_of_Z
     word.unsigned_of_Z_1 using lia : push_unsigned.
Hint Rewrite @firstn_length @skipn_length @map_length @app_length
  : push_length.
Hint Rewrite @skipn_app @skipn_O @List.skipn_skipn : push_skipn.
Hint Rewrite @firstn_app @firstn_O @firstn_firstn : push_firstn.

Local Existing Instance bedrock2.BasicCSyntax.StringNames_params.
Local Coercion literal (z : Z) : Syntax.expr := expr.literal z.
Local Coercion var (x : string) : Syntax.expr := expr.var x.
Local Coercion name_of_func (f : bedrock_func) := fst f.

(* Helper lemmas that could be moved elsewhere *)
Section Generalizable.
  Lemma only_differ_trans {key value map} ks m1 m2 m3 :
    @map.only_differ key value map m1 ks m2 ->
    map.only_differ m2 ks m3 ->
    map.only_differ m1 ks m3.
  Proof.
    cbv [map.only_differ]; intros H1 H2 x;
      specialize (H1 x); specialize (H2 x).
    destruct H1; destruct H2; try tauto.
    right; congruence.
  Qed.

  Lemma only_differ_get locals vars locals' v post :
    map.only_differ locals vars locals' ->
    ~ vars v ->
    WeakestPrecondition.get locals v post ->
    WeakestPrecondition.get locals' v post.
  Proof.
    intro Honly_differ; intros.
    specialize (Honly_differ v);
      destruct Honly_differ as [? | Honly_differ].
    { cbv [PropSet.elem_of] in *; tauto. }
    { cbv [WeakestPrecondition.get] in *.
      match goal with H : exists _, _ |- exists _, _ =>
                      let x := fresh in
                      destruct H as [x H]; exists x end.
      congruence. }
  Qed.

  (* TODO: move *)
  Lemma hd_app_l {A} (d : A) (xs ys : list A) :
    (0 < length xs)%nat ->
    hd d (xs ++ ys) = hd d xs.
  Proof.
    destruct xs; cbn [length]; [ lia | intros ].
    rewrite <-app_comm_cons. reflexivity.
  Qed.

  (* TODO: move *)
  Lemma hd_firstn {A} (d : A) n (xs : list A) :
    (0 < n)%nat ->
    hd d (firstn n xs) = hd d xs.
  Proof.
    destruct xs; destruct n; cbn [firstn hd]; intros;
      (lia || reflexivity).
  Qed.

  (* TODO: move *)
  Lemma hd_skipn_map
        {A B} (f: A -> B) (a : A) (b : B) (xs : list A) :
    forall n,
      (0 < length (skipn n xs))%nat ->
      hd b (skipn n (map f xs)) = f (hd a (skipn n xs)).
  Proof.
    induction xs; destruct n; cbn [skipn map length hd]; intros;
      try lia; try reflexivity.
    apply IHxs; auto.
  Qed.

  Lemma word_to_nat_to_word w :
    w = word.of_Z (Z.of_nat (Z.to_nat (word.unsigned w))).
  Proof.
    rewrite Z2Nat.id by apply word.unsigned_range.
    rewrite word.of_Z_unsigned; reflexivity.
  Qed.

End Generalizable.

Section Proofs.
  Context (functions' : list bedrock_func)
          (toupper_body : Semantics.byte -> Semantics.byte).

  Local Definition byte_to_word : Semantics.byte -> Semantics.word :=
    fun b => word.of_Z (word.unsigned b).

  Context
    (wordsize_eq : wordsize = 8) (* using C64 semantics; 8 bytes *)
    (charsize_eq : charsize = 1) (* char = 1 byte *)
    (toupper_correct :
       forall (c : Semantics.byte) tr mem,
         WeakestPrecondition.call
           functions' toupper tr mem [byte_to_word c]
           (fun tr' mem' rets =>
              tr = tr' /\ mem = mem'
              /\ rets = [byte_to_word (toupper_body c)])).

  Local Existing Instance BasicC64Semantics.parameters.
  Local Existing Instance BasicC64Semantics.parameters_ok.
  Local Notation len := Gallina.len (only parsing).
  Local Notation chars := Gallina.chars (only parsing).

  Definition String
             (addr : Semantics.word) (s : Gallina.String) :
    map.rep (map:=Semantics.mem) -> Prop :=
    sep
      (emp (Z.of_nat (len s) < 2^Semantics.width))
      (sep
         (scalar addr (word.of_Z (Z.of_nat (len s))))
         (array ptsto
                (word.of_Z charsize)
                (word.add addr (word.of_Z wordsize))
                (chars s))).

  Definition loop_invariant
             (s : Gallina.String) tr locals s_ptr R
             (m : nat) (tr' : Semantics.trace)
             (mem' : Semantics.mem) (locals' : Semantics.locals)
    : Prop :=
    tr = tr'
    /\ map.only_differ
         locals (PropSet.of_list ["x"; "c_ptr"; "i"]) locals'
    /\ WeakestPrecondition.get
         locals' "c_ptr"
         (fun _c_ptr =>
            let c_ptr := word.unsigned _c_ptr in
            WeakestPrecondition.get
              locals' "i"
              (fun _i =>
                 let i := Z.to_nat (word.unsigned _i) in
                 let partial : Gallina.String :=
                     {|len := len s;
                       chars :=
                         (List.firstn i (map toupper_body (chars s))
                                      ++ List.skipn i (chars s)) |} in
                 m = (len s - i)%nat
                 /\ (i <= len s)%nat
                 /\ c_ptr =
                    word.unsigned
                      (word.add
                         (word.add s_ptr (word.of_Z wordsize))
                         (word.mul (word.of_Z charsize) _i))
                 /\ sep (String s_ptr partial) R mem')).

  (* extracts the separation-logic condition for a single element of the
       string's char array *)
  Lemma char_array_lookup_sep addr s R mem n naddr :
    sep (String addr s) R mem ->
    len s = length (chars s) ->
    (n < len s)%nat ->
    naddr = word.add (word.add addr (word.of_Z wordsize))
                     (word.mul (word.of_Z charsize)
                               (word.of_Z (Z.of_nat n))) ->
    sep (ptsto naddr (List.hd (word.of_Z 0) (List.skipn n (chars s))))
        (sep
           (sep
              (array ptsto (word.of_Z charsize)
                     (word.add addr (word.of_Z wordsize))
                     (List.firstn n (Gallina.chars s)))
              (array ptsto (word.of_Z charsize)
                     (word.add
                        (word.add (word.add addr (word.of_Z wordsize))
                                  (word.mul (word.of_Z charsize)
                                            (word.of_Z (Z.of_nat n))))
                        (word.of_Z charsize))
                     (List.skipn (S n) (chars s))))
           (sep R
                (scalar addr (word.of_Z (Z.of_nat (len s))))))
        mem.
  Proof.
    intros; subst naddr.
    match goal with
      H : sep (String _ _) _ _ |- _ =>
      cbv [String] in H;
        apply sep_assoc, sep_emp_l in H; destruct H as [_ H];
          simple refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H)
    end.
    etransitivity.
    { rewrite sep_comm, <-sep_assoc.
      apply iff1_sep_cancel.
      eapply array_index_nat_inbounds
        with (n0:=n) (default:=word.of_Z 0);
        eauto using Semantics.word_ok, Semantics.mem_ok.
      lia. }
    rewrite word.ring_morph_mul, !word.of_Z_unsigned.
    (* annoying separation-logic algebra *)
    rewrite sep_comm with (p:=sep R _).
    rewrite sep_comm with (q:=sep (ptsto _ _) _).
    rewrite !sep_assoc with (p:=ptsto _ _).
    rewrite sep_comm with
        (p:=array _ _ _ (List.skipn _ _))
        (q:=array _ _ _ (List.firstn _ _)).
    reflexivity.
  Qed.

  Local Ltac prove_not_in_list :=
    match goal with
    | |- ~ PropSet.of_list _ _ =>
      cbn [PropSet.of_list In];
      let H' := fresh in
      intro H';
      solve [repeat (destruct H' as [H' | H'];
                     try congruence)]
    end.

  (* TODO: try to use ProgramLogic *)
  Lemma capitalize_String_correct
        (addr : Semantics.word) (s : Gallina.String) :
    forall tr mem R,
      sep (String addr s) R mem ->
      len s = length (chars s) ->
      let functions := (capitalize_String :: functions') in
      let caps :=
          Gallina.capitalize_String (toupper:=toupper_body) s in
      WeakestPrecondition.call
        functions capitalize_String tr mem [addr]
        (fun tr' mem' rets =>
           let success := word.unsigned (hd (word.of_Z 0) rets) in
           tr = tr' /\
           length rets = 1%nat /\
           ( (* either we failed and string is untouched, or... *)
             (success = 0 /\ sep (String addr s) R mem') \/
             (* we succeeded and string is correctly uppercase *)
             (success = 1 /\ sep (String addr caps) R mem'))).
  Proof.
    cbv zeta. intros.

    (* finding the function to call *)
    cbn [WeakestPrecondition.call
           WeakestPrecondition.call_body
           capitalize_String name_of_func fst].
    match goal with |- if Semantics.funname_eqb ?x ?x then _ else _ =>
                    destr (Semantics.funname_eqb x x) end;
      [ | congruence ].

    (* load arguments as initial local variables *)
    cbn [WeakestPrecondition.func].
    eexists; split; [ reflexivity | ].

    (* beginning of function body *)
    cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].

    (* first line : len = load( s_ptr ) *)
    eexists; split.
    { eexists; split; [ reflexivity | ].
      cbv [WeakestPrecondition.load Memory.load].
      match goal with
      | H : sep (String _ _) _ _ |- _ =>
        let E := fresh in
        apply sep_assoc, sep_emp_l in H; destruct H as [E H];
          apply sep_assoc, load_Z_of_sep in H; rewrite H
      end.
      eexists; split; reflexivity. }

    (* second line: i = 0 *)
    eexists; split; [ constructor | ].

    (* third line: c_ptr = s_ptr + wordsize *)
    eexists; split.
    { eexists; split; [ reflexivity | ].
      constructor. }

    (* beginning of while loop; need to provide measure/invariant *)
    cbn [WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
    match goal with |- dlet.dlet ?locals _ =>
                    cbv [dlet.dlet];
                      exists nat, lt, (loop_invariant s tr locals addr R)
    end.
    split; [ exact lt_wf | ].
    cbv [loop_invariant]; split.
    { (* invariant holds at start *)
      eexists; split; [ reflexivity | ]. (* tr = tr' *)
      split; [ cbn; right; reflexivity | ]. (* only_differ *)
      do 2 (eexists; split; [ reflexivity | ]). (* fetch i and c_ptr *)
      split; [ reflexivity | ]. (* measure = len s - i *)
      split; [ cbn; lia | ]. (* i <= len s *)

      (* c_ptr = s_ptr + wordsize + i * charsize *)
      split.
      { rewrite wordsize_eq. cbn.
        rewrite Z.add_0_r, Z.mod_mod by lia.
        reflexivity. }

      (* memory state *)
      cbn [firstn skipn map List.app].
      destruct s; cbn [Gallina.len Gallina.chars].
      assumption. }
    intros.

    (* extract the length-bounds clause of [String] and simplify; helps [lia] *)
    match goal with
      H : sep (String _ _) _ _ |- _ =>
      cbv [String] in H;
        apply sep_assoc, sep_emp_l in H; destruct H as [H ?]
    end.

    repeat match goal with
           | H : _ /\ _ |- _ => destruct H
           | H : exists _, _ |- _ => destruct H
           | H : WeakestPrecondition.get _ _ _ |- _ =>
             destruct H
           end.
    subst; eexists. split.

    (* get the value of the loop condition *)
    {
      (* fetch the value of "i" from the current locals *)
      eexists. split; [ eassumption | ].

      (* use only_differ to prove that "len" is unchanged *)
      eapply only_differ_get;
        [ eassumption | prove_not_in_list | ].

      (* fetch the value of "len" from the start-of-loop locals *)
      cbv [WeakestPrecondition.get].
      cbn - [BasicC64Semantics.parameters].
      eexists; split; [ reflexivity | ].

      (* could do reflexivity here, but it helps later if we simplify the
           expression for len *)
      rewrite Z.land_ones, Z.mod_small; [ reflexivity |  | lia ].
      match goal with |- ?x <= ?y < ?z =>
                      change (x <= y < 2 ^ Semantics.width)
      end.
      apply word.unsigned_range. }

    (* prove continue/break case depending on value of loop condition *)
    match goal with |- context [if ?x then _ else _] => destr x end;
      split; try (let X := fresh in intro X; cbv in X; congruence); [ | ].
    { (* continue case: prove that loop body preserves invariant *)
      intros.

      (* first, simplify the hypothesis that says i < len *)
      repeat match goal with H : _ |- _ =>
                             rewrite word.of_Z_unsigned in H end.
      let H :=
          match goal with
            H : word.ltu _ (word.of_Z (Z.of_nat (len _))) = true |- _ =>
            H end in
      rewrite word.unsigned_ltu in H;
        apply Z.ltb_lt in H;
        rewrite word.unsigned_of_Z in H;
        cbv [word.wrap] in H;
        rewrite Z.mod_small in H by lia;
        apply Z2Nat.inj_lt in H;
        [ | solve [apply word.unsigned_range] | lia ];
        rewrite Nat2Z.id in H.

      (* first line of loop body: unpack! x = toupper( load1( c_ptr ) ) *)
      (* first step: deal with load1( c_ptr ) *)
      eexists; split.
      {
        (* get value of c_ptr *)
        cbn. cbv [WeakestPrecondition.get].
        eexists; split; [ eassumption | ].
        repeat match goal with
                 H : word.unsigned _ = word.unsigned _ |- _ =>
                 apply word.unsigned_inj in H
               end.

        (* load char from c_ptr *)
        cbv [WeakestPrecondition.load].
        eexists; split; [ | reflexivity ].
        eapply load_one_of_sep.

        eapply char_array_lookup_sep; eauto;
          [| rewrite Z2Nat.id, word.of_Z_unsigned by apply word.unsigned_range;
             subst; reflexivity ].
        cbn [Gallina.chars Gallina.len].
        autorewrite with push_length.
        lia. }

      (* now, call toupper on loaded character *)
      eapply Proper_call; [ repeat intro | solve [apply toupper_correct] ].
      cbv beta in *.
      repeat match goal with
             | H : _ /\ _ |- _ => destruct H
             end.
      subst. (* toupper guarantees trace/memory are unchanged *)
      (* assign returned character to "x" *)
      eexists; split; [reflexivity | ].

      (* second line of loop body: store1(c_ptr, x) *)

      (* first, get value of "c_ptr"; we've fetched it before, so this just
           involves proving that adding a new variable to the locals didn't
           change the value *)
      eexists; split.
      { eexists; split; [ | reflexivity ].
        rewrite map.get_put_diff by congruence.
        eassumption. }

      repeat match goal with
               H : word.unsigned _ = word.unsigned _ |- _ =>
               apply word.unsigned_inj in H
             end.

      (* get value from "x" *)
      eexists; split.
      { eexists; split; [ | reflexivity ].
        rewrite map.get_put_same by congruence.
        reflexivity. }

      (* now, store *)
      cbv [WeakestPrecondition.store].
      eapply store_one_of_sep.
      { eapply char_array_lookup_sep; eauto;
          [ | rewrite Z2Nat.id, word.of_Z_unsigned by apply word.unsigned_range;
              subst; reflexivity ].
        cbn [Gallina.chars Gallina.len].
        autorewrite with push_length.
        lia. }

      (* third line of loop : c_ptr = c_ptr + charsize *)
      intros.
      eexists; split.
      { eexists; split; [ | reflexivity ].
        rewrite !map.get_put_diff by congruence.
        eassumption. }

      (* fourth line of loop: i = i + 1 *)
      eexists; split.
      { eexists; split; [ | reflexivity ].
        rewrite !map.get_put_diff by congruence.
        eassumption. }

      (* end of loop body; prove invariant holds on new state *)
      match goal with
      | H : map.get _ "i" = Some ?w |- _ =>
        exists (len s - Z.to_nat (word.unsigned w) - 1)%nat
      end.
      cbn [Gallina.len Gallina.chars] in *.
      split; [ | lia ].
      repeat match goal with |- _ /\ _ => split end.
      { reflexivity. (* trace unchanged *) }
      { (* no variables changed except i, x, c_ptr *)
        eapply only_differ_trans; [ eassumption | ].
        match goal with
          |- map.only_differ ?l (PropSet.of_list [?a; ?b; ?c])
                             (map.put
                                (map.put
                                   (map.put l ?a ?av) ?b ?bv) ?c ?cv) =>
          apply map.only_differ_putmany with (vs:=[av;bv;cv])
        end.
        reflexivity. }
      { (* postconditions based on c_ptr and i *)

        (* get value of variable "c_ptr" *)
        eexists; split.
        { rewrite ?map.get_put_diff, ?map.get_put_same by congruence.
          reflexivity. }

        (* get value of variable "i" *)
        eexists; split.
        { rewrite ?map.get_put_diff, ?map.get_put_same by congruence.
          reflexivity. }

        (* simplify the value of i (which is previous i + 1) *)
        cbn [Semantics.interp_binop].
        match goal with H : (Z.to_nat ?x < Gallina.len _)%nat |- _ =>
                        pose proof (proj1 (Nat2Z.inj_lt _ _) H);
                          rewrite !Z2Nat.id in * by apply word.unsigned_range
        end.
        match goal with
          |- context [word.unsigned (word.add ?x ?y)] =>
          pose proof word.unsigned_range x;
            pose proof word.unsigned_range y;
            autorewrite with push_unsigned in *;
            cbv [word.wrap];
            rewrite Z.mod_small, Z2Nat.inj_add by lia
        end.
        change (Z.to_nat 1) with 1%nat.

        (* m = len s - i *)
        split; [ lia | ].

        (* i <= len s *)
        split; [ lia | ].

        (* c_ptr = s_ptr + wordsize + (charsize * i) *)
        split.
        { subst; autorewrite with push_unsigned.
          cbv [word.wrap]. Z.mod_equality. }

        (* correct partial string is Stringresented *)
        cbv [String]; cbn [Gallina.len Gallina.chars].
        apply sep_assoc, sep_emp_l. split; [ assumption | ].
        rewrite Nat.add_1_r.
        apply sep_comm, sep_assoc, sep_comm.
        simple refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H6).

        (* reverse order of element and firstn to match
             array_index_nat_inbounds *)
        rewrite <-!sep_assoc with (p:=ptsto _ _).
        rewrite sep_comm with (p:=ptsto _ _).
        rewrite sep_assoc with (p:=array _ _ _ (List.firstn _ _)).
        (* cancel non-array clause *)
        rewrite !sep_comm with (q:=sep R _).
        apply iff1_sep_cancel.

        match goal with
          |- Lift1Prop.iff1 (sep (array _ _ _ (List.firstn ?i _)) _)
                            (array _ _ _ ?ls) =>
          rewrite array_index_nat_inbounds
          with (n:=i) (default:=word.of_Z 0) (xs:=ls)
            by (autorewrite with push_length; lia)
        end.
        rewrite !Z2Nat.id by apply word.unsigned_range.
        rewrite !word.of_Z_unsigned.

        match goal with
          |- context
               [(word.of_Z (word.unsigned ?x * word.unsigned ?y))] =>
          replace (word.of_Z (word.unsigned x * word.unsigned y))
          with (word.mul x y)
            by (rewrite word.ring_morph_mul, !word.of_Z_unsigned;
                reflexivity)
        end.

        (* prove that the looked-up addresses are the same *)
        match goal with
          |- Lift1Prop.iff1 ?l ?r =>
          let xl :=
              match l with context [ptsto ?xl] => xl end in
          let xr :=
              match r with context [ptsto ?xr] => xr end in
          replace xr with xl
        end.

        (* simplify the conversions on the selected element *)
        match goal with
          |- context [word.of_Z (word.unsigned (byte_to_word ?b))] =>
          replace (word.of_Z (word.unsigned (byte_to_word b))) with b
            by (clear; pose proof (word.unsigned_range b); cbv [byte_to_word]; rewrite word.unsigned_of_Z; cbv [word.wrap]; rewrite Z.mod_small, word.of_Z_unsigned by (cbn in *; lia); reflexivity)
        end.

        (* separate out each of the 3 clauses *)
        apply Proper_sep_iff1; [ | apply Proper_sep_iff1 ].
        all:autorewrite with push_skipn push_firstn push_length.
        1:rewrite !firstn_skipn_comm.
        2:rewrite !skipn_firstn_comm.

        (* TODO: somewhat fragile list-manipulation hell *)
        all:
          repeat match goal with
                 | _ => progress autorewrite with push_skipn
                                                  push_firstn
                                                  push_length
                 | _ => rewrite app_nil_l
                 | _ => rewrite hd_app_l
                     by (autorewrite with push_length; lia)
                 | _ => rewrite (hd_skipn_map _ (word.of_Z 0))
                     by (autorewrite with push_length; lia)
                 | |- context [List.skipn ?n (List.firstn ?n ?l)] =>
                   rewrite (@skipn_all2 _ n (List.firstn n l))
                     by (clear; autorewrite with push_length; lia)
                 | _ => rewrite skipn_all2
                     by (clear; autorewrite with push_length; lia)
                 | _ => rewrite hd_firstn by lia
                 | _ => rewrite Nat.sub_diag
                 | _ => rewrite Nat.add_0_l
                 | _ => rewrite Nat.min_l by lia
                 | |- Lift1Prop.iff1
                        (array _ _ _ (List.skipn ?nl ?ls))
                        (array _ _ _ (List.skipn ?nr ?ls)) =>
                   replace nl with nr by lia; reflexivity
                 | _ => reflexivity
                 end. } }
    { (* break case : prove that postcondition holds given loop is done and
           invariant holds *)
      intros.

      (* first, simplify the hypothesis that says i >= len *)
      repeat match goal with H : _ |- _ =>
                             rewrite word.of_Z_unsigned in H end.
      let H :=
          match goal with
            H : word.ltu _ (word.of_Z (Z.of_nat (len _))) = false |- _ =>
            H end in
      rewrite word.unsigned_ltu in H;
        apply Z.ltb_ge in H;
        rewrite word.unsigned_of_Z in H;
        cbv [word.wrap] in H;
        rewrite Z.mod_small in H by lia;
        apply Z2Nat.inj_le in H;
        [ | lia | solve [apply word.unsigned_range] ];
        rewrite Nat2Z.id in H.

      (* use i >= len to remove firstn/skipn from loop invariant *)
      match goal with
      | H : sep (String _ _) _ _ |- _ =>
        rewrite firstn_all2, skipn_all2, app_nil_r in H
          by (autorewrite with push_length; lia)
      end.

      (* ret = 1 *)
      eexists; split; [ solve [constructor] | ].
      eexists; split; [ rewrite map.get_put_same; reflexivity | ].
      cbn [WeakestPrecondition.list_map WeakestPrecondition.list_map_body].

      (* take care of easy postconditions *)
      cbn [length hd].
      rewrite word.unsigned_of_Z_1.
      repeat split; try reflexivity; [ ].
      right. split; [ reflexivity | ].

      (* the last "partial" string is the correct final result *)
      assumption. }
  Qed.
End Proofs.
