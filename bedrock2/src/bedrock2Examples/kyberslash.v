
(*https://github.com/pq-crystals/kyber/commit/dda29cc63af721981ee2c831cf00822e69be3220*)
(*
typedef struct{
  int16_t coeffs[KYBER_N];
} poly;

void poly_tomsg(uint8_t msg[KYBER_INDCPA_MSGBYTES], const poly *a)
{
  unsigned int i,j;
  uint32_t t;

  for(i=0;i<KYBER_N/8;i++) {
    msg[i] = 0;
    for(j=0;j<8;j++) {
      t  = a->coeffs[8*i+j];
      // t += ((int16_t)t >> 15) & KYBER_Q;
      // t  = (((t << 1) + KYBER_Q/2)/KYBER_Q) & 1;
      t <<= 1;
      t += 1665;
      t *= 80635;
      t >>= 28;
      t &= 1;
      msg[i] |= t << j;
    }
  }
}
 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
From bedrock2 Require Import NotationsCustomEntry LeakageProgramLogic Map.Separation Map.SeparationLogic Array Scalars LeakageLoops.
From coqutil Require Import Datatypes.List Word.Bitwidth Map.Interface.
From bedrock2 Require Import Semantics LeakageSemantics Syntax.
Import coqutil.Word.Properties coqutil.Map.Properties.
Require Import bedrock2.AbsintWordToZ.
Require Import bedrock2.ZnWords.
From coqutil.Macros Require Import symmetry.
Require Import bedrock2.LeakageWeakestPrecondition bedrock2.LeakageWeakestPreconditionProperties bedrock2.LeakageProgramLogic.
From coqutil.Tactics Require Import Tactics letexists.

Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Infix "/" := (expr.op bopname.divu) (in custom bedrock_expr at level 5, left associativity).

Section WithWord.
  Context {width: Z} {BW: Bitwidth width}.
  Local Notation word := (bits width).
  Context {mem: map.map word Byte.byte}.
  Context {locals: map.map string word}.
  Context {env : map.map string (list string * list string * Syntax.cmd)}.
  Context {mem_ok: map.ok mem} {locals_ok: map.ok locals} {env_ok : map.ok env}.
  Context {ext_spec: ExtSpec} {ext_spec_ok : ext_spec.ok ext_spec}.
  Context {pick_sp: PickSp}.
  Context (width_big: 4 <= width). (*to avoid division by zero*)
  Context (KYBER_N KYBER_Q KYBER_INDCPA_MSGBYTES : Z).
  (* global constants in bedrock2? *)
  
  Definition poly_tomsg :=
    func! (msg, a_coeffs) {
        i = $0;
        while (i < coq:(expr.literal KYBER_N) / $8) {
            store1(msg + i, $0);
            j = $0;
            while (j < $8) {
                t = load2(a_coeffs + $2 (* <- because 2-byte array *) * ($8 * i + j));
                t = t << $1;
                t = t + $1665;
                t = t * $80635;
                t = t >> $28;
                t = t & $1;
                store1(msg + i, load1(msg + i) | (t << j));
                j = j + $1;
                coq:(cmd.unset "t")
              };
            i = i + $1;
            coq:(cmd.unset "j")
          }
      }.

  Fixpoint get_inner_leakage start f fi fj (i j : word) (vj : nat) : leakage :=
    match vj with
    | S vj' => get_inner_leakage start f fi fj (fi i j) (fj i j) vj' ++ f i j
    | O => start
    end%list.

  Fixpoint get_outer_leakage start f fi (i : word) (vi : nat) : leakage :=
    match vi with
    | S vi' => get_outer_leakage start f fi (fi i) vi' ++ f i
    | O => start
    end%list.
    
  
  (*Definition bad_poly_tomsg :=
    func! (msg, a_coeffs) {
        i = $0;
        while (i < KYBER_N / $8) {
            store1(msg + i, $0);
            j = $0;
            while (j < $8) {
                t = load2(a_coeffs + $2 (* <- because 2-byte array *) * ($8 * i + j));
                (* t += ((int16_t)t >> 15) & KYBER_Q;
                   ^ want to implement that.  t is a uint16_t.
                   apparently uint -> int casts are implementation-defined when not in range.
                   how confusing.
                   so we should assume that t is in int16_t range.
                   But then ((int16_t)t >> 15) = 0, and the whole thing is a no-op.
                   So what?
                   I suppose we just assume the cast just does nothing (aside from changing the type),
                   regardless of the value of t.  That's the only thing that makes that line of code 
                   reasonable.
                 *)
                j = j + $1
              };
            i = i + $1
          }
      }.*)

  Instance poly_tomsg_ct : spec_of "poly_tomsg" :=
    fnspec! exists f : word -> word -> Z -> leakage, "poly_tomsg" msg a_coeffs / (msg_vals : list Byte.byte) (a_coeffs_vals : list word) (R : mem -> Prop),
    { requires k t m :=
        ((array scalar8 (bits.of_Z width 1) msg msg_vals) ⋆ (array scalar16 2 a_coeffs a_coeffs_vals) ⋆ R)%sep m /\
          KYBER_N = Z.of_nat (List.length a_coeffs_vals) /\
          KYBER_INDCPA_MSGBYTES = Z.of_nat (List.length msg_vals) /\
          Zmod.unsigned (Zmod.udiv (bits.of_Z width KYBER_N) (bits.of_Z width 8)) <= KYBER_INDCPA_MSGBYTES ;
      ensures K T M :=
        T = t /\ K = f msg a_coeffs KYBER_N ++ k }.
    
    Lemma poly_tomsg_ok : program_logic_goal_for_function! poly_tomsg.
    Proof.
      repeat straightline.
      refine ((LeakageLoops.tailrec
                 (* types of ghost variables*) (let c := HList.polymorphic_list.cons in c _ (c _ HList.polymorphic_list.nil))
                 (* program variables *) ("i" :: "a_coeffs" :: "msg" :: nil))%string
                (fun vi msg_vals a_coeffs_vals k t m i a_coeffs msg =>
                   PrimitivePair.pair.mk
                     (KYBER_N = Z.of_nat (List.length a_coeffs_vals) /\
                        KYBER_INDCPA_MSGBYTES = Z.of_nat (List.length msg_vals) /\
                        ((array scalar8 (bits.of_Z width 1) msg msg_vals) * (array scalar16 2 a_coeffs a_coeffs_vals) * R)%sep m 
                      /\ vi = Zmod.unsigned (Zmod.udiv (bits.of_Z width KYBER_N) (bits.of_Z width 8)) - Zmod.unsigned i) (* precondition *)
                     (fun K T M I A_COEFFS MSG => (*postcondition*)
                        T = t /\ A_COEFFS = a_coeffs /\ MSG = msg /\
                          exists MSG_VALS A_COEFFS_VALS,
                            KYBER_N = Z.of_nat (List.length A_COEFFS_VALS) /\
                              KYBER_INDCPA_MSGBYTES = Z.of_nat (List.length MSG_VALS) /\
                              ((array scalar8 (bits.of_Z width 1) msg MSG_VALS) * (array scalar16 2 a_coeffs A_COEFFS_VALS) * R)%sep M /\
                              K = (get_outer_leakage _ _ _ i (Z.to_nat vi) ++ k)%list
                )) 
                (fun n m => 0 <= n < m) (* well_founded relation *)
                _ _ _ _ _ _ _);
        cbn [HList.hlist.foralls HList.tuple.foralls
               HList.hlist.existss HList.tuple.existss
               HList.hlist.apply  HList.tuple.apply
               HList.hlist
               List.repeat Datatypes.length
               HList.polymorphic_list.repeat HList.polymorphic_list.length
               PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
      { cbv [enforce]; cbn.
        subst l l0.
        repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn). split.
        { exact eq_refl. }
        { eapply map.map_ext; intros k0.
          repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec, ?map.get_empty; cbn -[String.eqb]).
          repeat (destruct String.eqb; trivial). } }
      { exact (Z.lt_wf _). }
      { repeat (straightline || intuition eauto). }
      { repeat straightline. cbn in localsmap.
        cbv [dexpr expr expr_body localsmap get literal dlet.dlet].
        (*would be nice if straightline did the following stuff... but the non-leakage
         straightline doesn't do it either, so i'll just leave it alone*)
        eexists. eexists. split.
        { rewrite ?Properties.map.get_put_dec. cbn. eauto. }
        split.
        { repeat straightline.
          eapply dexpr_expr. repeat straightline. letexists; split.
          { rewrite ?Properties.map.get_put_dec; exact eq_refl. }
          repeat straightline. letexists; split.
          { rewrite ?Properties.map.get_put_dec; exact eq_refl. }
          eapply dexpr_expr. repeat straightline.
          (*finally we do something interesting*)
          destruct (Z.ltb (Zmod.unsigned x1) _) eqn:E.
          2: { rewrite Zmod.unsigned_0 in H4. exfalso. auto. }
          apply Z.ltb_lt in E.
          assert (nsmall: (0 <= Z.to_nat (Zmod.unsigned x1) < Datatypes.length x)%nat) by ZnWords.
          assert (Ex1: x1 = bits.of_Z width (Zmod.unsigned (bits.of_Z width 1) * Z.of_nat (Z.to_nat (Zmod.unsigned x1)))).
          { rewrite Z2Nat.id.
            2: { assert (Hnonneg := bits.unsigned_range x1 width_nonneg). blia. }
            apply Zmod.unsigned_inj.
            rewrite bits.unsigned_of_Z, bits.unsigned_1 by (pose proof width_pos; blia).
            assert (Hx1 := bits.unsigned_range x1 width_nonneg).
            rewrite Z.mod_small; blia. }
          eapply Scalars.store_one_of_sep.
          { seprewrite_in (@array_index_nat_inbounds _ _ _ _ _ ptsto (bits.of_Z width 1) Byte.x00 x x3 (Z.to_nat (Zmod.unsigned x1))) H3.
            { ZnWords. }            
            rewrite <- Ex1 in H3.
            ecancel_assumption. }
          repeat straightline. (* neat, why did that work now? *)
          refine ((LeakageLoops.tailrec
                     (* types of ghost variables*) (let c := HList.polymorphic_list.cons in c _ (c _ HList.polymorphic_list.nil))
                     (* program variables *) ("j" :: "i" :: "a_coeffs" :: "msg" :: nil))%string
                    (fun vj msg_vals a_coeffs_vals k t m j i a_coeffs msg =>
                       PrimitivePair.pair.mk
                         (KYBER_N = Z.of_nat (List.length a_coeffs_vals) /\
                            KYBER_INDCPA_MSGBYTES = Z.of_nat (List.length msg_vals) /\
                            i = x1(*value of i before we enter loop*) /\
                            ((array scalar8 (bits.of_Z width 1) msg msg_vals) * (array scalar16 2 a_coeffs a_coeffs_vals) * R)%sep m 
                          /\ vj = (8 mod 2 ^ width) - Zmod.unsigned j) (* precondition *)
                         (fun K T M J I A_COEFFS MSG => (*postcondition*) 
                            T = t /\ A_COEFFS = a_coeffs /\ MSG = msg /\
                              exists MSG_VALS A_COEFFS_VALS,
                                KYBER_N = Z.of_nat (List.length A_COEFFS_VALS) /\
                                  KYBER_INDCPA_MSGBYTES = Z.of_nat (List.length MSG_VALS) /\
                                  I = x1 /\
                                  ((array scalar8 (bits.of_Z width 1) msg MSG_VALS) * (array scalar16 2 a_coeffs A_COEFFS_VALS) * R)%sep M /\
                                  K = (get_inner_leakage _ _ _ _ i j (Z.to_nat vj) ++ k)%list
                    )) 
                    (fun n m => 0 <= n < m) (* well_founded relation *)
                    _ _ _ _ _ _ _);
            cbn [HList.hlist.foralls HList.tuple.foralls
                   HList.hlist.existss HList.tuple.existss
                   HList.hlist.apply  HList.tuple.apply
                   HList.hlist
                   List.repeat Datatypes.length
                   HList.polymorphic_list.repeat HList.polymorphic_list.length
                   PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
          { cbv [LeakageLoops.enforce]; cbn.
            subst l.
            repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn). split.
            { exact eq_refl. }
            { eapply map.map_ext; intros k0'.
              repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec, ?map.get_empty; cbn -[String.eqb]).
              repeat (destruct String.eqb; trivial). } }
          { exact (Z.lt_wf _). }
          { seprewrite_in (symmetry! @array_cons) H5.
            seprewrite_in @sep_comm H5.
            remember (Z.to_nat (Zmod.unsigned x1)) as n eqn:En.            
            rewrite Ex1 in H5.
            replace (Z.of_nat n) with (Z.of_nat (List.length (List.firstn n x))) in H5.
            2: { rewrite List.firstn_length. blia. }
            seprewrite_in (symmetry! @array_append) H5. subst.
            split; [|split; [|split; [|split] ] ].
            4: ecancel_assumption.
            { assumption. }
            { repeat rewrite List.app_length. cbn [List.length].
              rewrite List.firstn_length. rewrite List.skipn_length. blia. }
            { reflexivity. }
            { reflexivity. } }
          { repeat straightline. cbn in localsmap.
            cbv [dexpr expr expr_body localsmap get literal dlet.dlet].
            (*would be nice if straightline did the following stuff... but the non-leakage
         straightline doesn't do it either, so i'll just leave it alone*)
            eexists. eexists. split.
            { rewrite ?Properties.map.get_put_dec. cbn. eauto. }
            split.
            { repeat straightline.
              eapply dexpr_expr. repeat straightline. letexists; split.
              { rewrite ?Properties.map.get_put_dec; exact eq_refl. }
              repeat straightline. letexists; split.
              { rewrite ?Properties.map.get_put_dec; exact eq_refl. }
              repeat straightline. letexists; split.
              { rewrite ?Properties.map.get_put_dec; exact eq_refl. }
              destruct (Z.ltb (Zmod.unsigned _) _) eqn:Ex6.
              2: { rewrite Zmod.unsigned_0 in H10. exfalso. auto. }
              apply Z.ltb_lt in Ex6.
              eexists. split.
              { eapply load_two_of_sep. repeat straightline.
                remember (Zmod.add (Zmod.mul v2 x1) x6) as n eqn:En.
                seprewrite_in (@array_index_nat_inbounds _ _ _ _ _ scalar16 2 (bits.of_Z width 0) x5 x8 (Z.to_nat (Zmod.unsigned n))) H11.
                2: { repeat straightline. use_sep_assumption. cancel.
                     cancel_seps_at_indices 1%nat 0%nat.
                     { f_equal. f_equal. subst v1 n.
                       rewrite Z2Nat.id.
                       2: { assert (Hnonneg:= bits.unsigned_range (Zmod.add (Zmod.mul v2 x1) x6) width_nonneg).
                            blia. }
                       ZnWords. }
                     ecancel_done. }
                subst. subst v1. subst v0. subst v2.
                assert (Hnonneg := bits.unsigned_range (Zmod.add (Zmod.mul 8 x1) x6) width_nonneg).
                enough ((Zmod.unsigned (Zmod.add (Zmod.mul 8 x1) x6)) < KYBER_N).
                { subst KYBER_N. blia. }
                assert (0 < Zmod.unsigned (m := 2 ^ width) (bits.of_Z width 8)).
                { rewrite bits.unsigned_of_Z.
                  rewrite Z.mod_small; try split; try blia.
                  assert (X := Z.pow_le_mono_r 2 4 width). specialize (X ltac:(blia) ltac:(blia)).
                  blia. }
                assert (0 < 2 ^ width).
                { apply Z.pow_pos_nonneg; blia. }
                rewrite Zmod.unsigned_add, Zmod.unsigned_mul, Zmod.unsigned_udiv in * by blia.
                rewrite bits.unsigned_of_Z in E.
                
                rewrite Z.add_mod_idemp_l by blia. rewrite bits.unsigned_of_Z in *.
                assert (Zmod.unsigned x1 < KYBER_N mod 2 ^ width / (8 mod 2 ^ width)).
                { eapply Z.lt_le_trans. 1: eassumption.
                  apply Z.mod_le; try blia.
                  apply Z_div_nonneg_nonneg; try blia.
                  apply Z_mod_nonneg_nonneg; blia. }
                enough (((8 mod 2 ^ width) * Zmod.unsigned x1 + Zmod.unsigned x6) < KYBER_N).
                { eapply Z.le_lt_trans. 2: eassumption. apply Z.mod_le; try blia.
                  assert (Hx6 := bits.unsigned_range x6 width_nonneg). assert (Hx1 := bits.unsigned_range x1 width_nonneg).
                  blia. }
                assert (Zmod.unsigned x1 < KYBER_N / (8 mod 2 ^ width)).
                { eapply Z.lt_le_trans. 1: eassumption.
                  apply Z.div_le_mono; try blia. apply Z.mod_le; blia. }
                enough ((8 mod 2 ^ width) * (Zmod.unsigned x1 + 1) <= KYBER_N).
                { blia. }
                assert (Zmod.unsigned x1 + 1 <= KYBER_N / (8 mod 2 ^ width)) by blia.
                apply Zmult_le_compat_l with (p := (8 mod 2 ^ width)) in H16; try blia.
                eapply Z.le_trans. 1: eassumption.
                apply Z.mul_div_le. blia. }
              repeat straightline. eapply dexpr_expr. repeat straightline. letexists; split.
              { cbv [l]. rewrite ?Properties.map.get_put_dec; exact eq_refl. }
              repeat straightline. eapply dexpr_expr. repeat straightline. letexists; split.
              { cbv [l0]. rewrite ?Properties.map.get_put_dec; exact eq_refl. }
              repeat straightline. eapply dexpr_expr. repeat straightline. letexists; split.
              { cbv [l1]. rewrite ?Properties.map.get_put_dec; exact eq_refl. }
              repeat straightline. eapply dexpr_expr. repeat straightline. letexists; split.
              { cbv [l2]. rewrite ?Properties.map.get_put_dec; exact eq_refl. }
              repeat straightline. eapply dexpr_expr. repeat straightline. letexists; split.
              { cbv [l3]. rewrite ?Properties.map.get_put_dec; exact eq_refl. }
              repeat straightline. eapply dexpr_expr. repeat straightline. letexists; split.
              { cbv [l4 l3 l2 l1 l0 l]. rewrite ?Properties.map.get_put_dec; exact eq_refl. }
              repeat straightline. letexists; split.
              { cbv [l4 l3 l2 l1 l0 l]. rewrite ?Properties.map.get_put_dec; exact eq_refl. }
              repeat straightline. eapply dexpr_expr. repeat straightline. letexists; split.
              { cbv [l4 l3 l2 l1 l0 l]. rewrite ?Properties.map.get_put_dec; exact eq_refl. }
              repeat straightline. letexists; split.
              { cbv [l4 l3 l2 l1 l0 l]. rewrite ?Properties.map.get_put_dec; exact eq_refl. }
              repeat straightline. letexists; split.
              { eapply Scalars.load_one_of_sep.
                seprewrite_in_by (@array_index_nat_inbounds _ _ _ _ _ ptsto (bits.of_Z width 1) Byte.x00 x4 x9 (Z.to_nat (Zmod.unsigned x1))) H11 ZnWords.
                rewrite <- Ex1 in H11.
                ecancel_assumption. }
              repeat straightline. letexists; split.
              { cbv [l4 l3 l2 l1 l0 l]. rewrite ?Properties.map.get_put_dec; exact eq_refl. }
              repeat straightline. letexists; split.
              { cbv [l4 l3 l2 l1 l0 l]. rewrite ?Properties.map.get_put_dec; exact eq_refl. }
              eapply Scalars.store_one_of_sep.
              { seprewrite_in_by (@array_index_nat_inbounds _ _ _ _ _ ptsto (bits.of_Z width 1) Byte.x00 x4 x9 (Z.to_nat (Zmod.unsigned x1))) H11 ZnWords.
                rewrite <- Ex1 in H11. ecancel_assumption. }
              repeat straightline. eapply dexpr_expr. repeat straightline. letexists; split.
              { cbv [l4 l3 l2 l1 l0 l]. rewrite ?Properties.map.get_put_dec; exact eq_refl. }
              repeat straightline. eexists _, _, _, _. split.
              { cbv [enforce l6 l5 l4 l3 l2 l1 l0 l].
                repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn). split.
                { exact eq_refl. }
                { eapply map.map_ext; intros kk.
                  repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec, ?map.get_empty; cbn -[String.eqb]).
                  repeat (destruct String.eqb; trivial). } }
              repeat straightline.

              seprewrite_in (symmetry! @array_cons) H12.
              remember (Byte.byte.of_Z (Zmod.unsigned (Zmod.or _ _))) as something.
              seprewrite_in @sep_comm H12.
              remember (Z.to_nat (Zmod.unsigned x1)) as n eqn:En.              
              rewrite Ex1 in H12.
              replace (Z.of_nat n) with (Z.of_nat (List.length (List.firstn n x4))) in H12.
              2: { rewrite List.firstn_length. blia. }
              seprewrite_in (symmetry! @array_append) H12. subst.
              assert (8 < 2 ^ width).
              { assert (X := Z.pow_le_mono_r 2 4 width). specialize (X ltac:(blia) ltac:(blia)).
                blia. }
              rewrite bits.unsigned_of_Z in Ex6.
              rewrite Z.mod_small in * by blia.

              eexists. eexists. eexists. split.
              { ssplit. 4: ecancel_assumption.
                all: intuition eauto.
                repeat rewrite List.app_length. cbn [List.length].
                rewrite List.firstn_length. rewrite List.skipn_length. blia. }
              split.
              { clear H12. subst v15. subst v.
                rewrite Zmod.unsigned_add. rewrite bits.unsigned_of_Z.
                rewrite (Z.mod_small 8) by blia. rewrite (Z.mod_small 1) by blia.
                pose proof (bits.unsigned_range x6 width_nonneg). rewrite Z.mod_small by blia.
                blia. }
              (*postcondition*)
              intros. intuition.
              destruct H18 as [MSG_VALS [A_COEFFS_VALS [H18 [H19 [H20 [H21 H22] ] ] ] ] ].
              eexists. eexists. ssplit.
              4: ecancel_assumption.
              1,2,3: solve [auto].
              subst v. replace (Z.to_nat (8 mod 2 ^ width - Zmod.unsigned x6)) with
                (S (Z.to_nat (8 - Zmod.unsigned (Zmod.add x6 (bits.of_Z width 1))))).
              { cbn [get_inner_leakage].
                rewrite H22.
                assert (app_one_cons : forall A (a : A) l, (a :: l = (cons a nil) ++ l)%list).
                { reflexivity. }
                clear H22.
                repeat rewrite <- List.app_assoc. f_equal.
                { f_equal.
                  { instantiate (1 := fun _ _ => _). simpl. reflexivity. }
                  { instantiate (1 := fun _ _ => _). simpl. reflexivity. } }
                instantiate (1 := fun _ _ => _). simpl. align_trace. }
              clear H22. rewrite Zmod.unsigned_add. clear H12.
              rewrite bits.unsigned_1 by (pose proof width_pos; blia).
              rewrite (Z.mod_small 8) by blia. rewrite Z.mod_small.
              { blia. }
              pose proof (bits.unsigned_range x6 width_nonneg). blia. }
            intros. intuition. eexists. eexists. split; [|split; [|split; [|split] ] ].
            4: ecancel_assumption.
            all: auto.
            f_equal.
            replace (Z.to_nat v) with O.
            { simpl. instantiate (1 := (_ :: nil)%list). reflexivity. }
            subst v. destruct (Z.ltb (Zmod.unsigned _) _) eqn:Ex6; try congruence.
            apply Z.ltb_nlt in Ex6.
            rewrite bits.unsigned_of_Z in Ex6.
            assert (8 < 2 ^ width).
            { assert (X := Z.pow_le_mono_r 2 4 width). specialize (X ltac:(blia) ltac:(blia)).
              blia. }
            rewrite (Z.mod_small 8) in * by blia. blia. }
          { cbn in l. repeat straightline.
            eapply dexpr_expr. repeat straightline. letexists; split.
            { cbn. rewrite ?Properties.map.get_put_dec; exact eq_refl. }
            repeat straightline. eexists. eexists. eexists. split.
            { cbv [LeakageLoops.enforce]; cbn.
              subst l l0.
              repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn). split.
              { exact eq_refl. }
              { eapply map.map_ext; intros K0.
                repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec, ?map.get_empty; cbn -[String.eqb]).
                repeat (destruct String.eqb; trivial). } }
            (*postcondition*)
            repeat straightline.
            eexists. eexists. eexists. split.
            { ssplit. 3: ecancel_assumption. all: eauto. }
            split.
            (*the following block, 'block X', is copied and pasted down below*)
            { subst v v1.
              assert (8 < 2 ^ width).
              { assert (X := Z.pow_le_mono_r 2 4 width). specialize (X ltac:(blia) ltac:(blia)).
                blia. }
              assert (0 < Zmod.unsigned (m := 2 ^ width) (bits.of_Z width 8)).
              { rewrite bits.unsigned_of_Z.
                rewrite Z.mod_small by blia. blia. }
              remember (Zmod.udiv _ _) as cow.
              rewrite Zmod.unsigned_add. rewrite bits.unsigned_1 by (pose proof width_pos; blia).
              rewrite (Z.mod_small (Zmod.unsigned x1 + 1)).
              { blia. }
              pose proof (bits.unsigned_range x1 width_nonneg). split; try blia.
              pose proof (bits.unsigned_range cow width_nonneg). blia. }
            repeat straightline. eexists. eexists. ssplit.
            3: ecancel_assumption.
            1,2: assumption.
            simpl. subst k1.
            replace (Z.to_nat v) with (S (Z.to_nat
                                            (Zmod.unsigned (m := 2 ^ width) (Zmod.udiv (bits.of_Z width KYBER_N) (bits.of_Z width 8)) -
                                               Zmod.unsigned (Zmod.add x1 (bits.of_Z width 1))))).
            { cbn [get_outer_leakage].
              rewrite H17. clear H17.
              assert (app_one_cons : forall A (a : A) l, (a :: l = (cons a nil) ++ l)%list).
              { reflexivity. }
              simpl. 
              repeat (rewrite List.app_assoc || rewrite (app_one_cons _ _ (_ ++ k0)%list) || rewrite (app_one_cons _ _ k0)).
              f_equal. repeat rewrite <- List.app_assoc. f_equal.
              2: { instantiate (1 := fun _ => _). cbv beta. simpl. reflexivity. }
              f_equal.
              { instantiate (1 := fun _ => _). simpl. reflexivity. } }
            (*block X again*)
            { subst v v1.
              assert (8 < 2 ^ width).
              { assert (X := Z.pow_le_mono_r 2 4 width). specialize (X ltac:(blia) ltac:(blia)).
                blia. }
              assert (0 < Zmod.unsigned (m := 2 ^ width) (bits.of_Z width 8)).
              { rewrite bits.unsigned_of_Z.
                rewrite Z.mod_small by blia. blia. }
              remember (Zmod.udiv _ _) as cow.
              rewrite Zmod.unsigned_add. rewrite bits.unsigned_1 by (pose proof width_pos; blia).
              rewrite (Z.mod_small (Zmod.unsigned x1 + 1)).
              { blia. }
              pose proof (bits.unsigned_range x1 width_nonneg). split; try blia.
              pose proof (bits.unsigned_range cow width_nonneg). blia. } } }
        intros. intuition. eexists. eexists. ssplit.
        3: ecancel_assumption.
        1,2: assumption.
        simpl. replace (Z.to_nat v) with 0%nat.
        { cbn [get_outer_leakage]. instantiate (1 := (_ :: _ :: _ :: nil)%list). reflexivity. }
        destruct (Z.ltb (Zmod.unsigned x1) _) eqn:E.
        { rewrite bits.unsigned_1 in H4 by (pose proof width_pos; blia). congruence. }
        apply Z.ltb_nlt in E.
        blia. }
      repeat straightline.
      subst k0.
      assert (app_one_cons : forall A (a : A) l, (a :: l = (cons a nil) ++ l)%list).
      { reflexivity. }
      repeat (rewrite List.app_assoc || rewrite (app_one_cons _ _ (_ ++ k)%list)).
      instantiate (1 := fun _ _ _ => _). reflexivity.
    Qed.
End WithWord.
