Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Bitwidth32.
Require Import bedrock2.Array.
Require Import bedrock2.SepCalls bedrock2.SepAutoArray bedrock2.SepAuto.
Require Import bedrock2.TransferSepsOrder.
Require Import coqutil.Map.Interface.
Require Import egg.Loader.
Require Import bedrock2.egg_lemmas.
Require Import coqutil.Datatypes.OperatorOverloading bedrock2.OperatorOverloading.
Local Open Scope oo_scope.
Local Open Scope conversion_parse_scope. Local Open Scope conversion_print_scope.
Require Import bedrock2.ListIndexNotations. Local Open Scope list_index_scope.
Require Import bedrock2.SepBulletPoints. Local Open Scope sep_bullets_scope.
Close Scope list_scope. Close Scope Z_scope. (* TODO *)



Section WithParameters.
  Context {word: word.word 32} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Add Ring wring : (Properties.word.ring_theory (word := word))
        ((*This preprocessing is too expensive to be always run, especially if
           we do many ring_simplify in a sequence, in which case it's sufficient
           to run it once before the ring_simplify sequence.
           preprocess [autorewrite with rew_word_morphism],*)
         morphism (Properties.word.ring_morph (word := word)),
         constants [Properties.word_cst]).


Definition wadd_0_l := word.add_0_l.
Definition wadd_0_r := word.add_0_r.
Definition wadd_join := word.add_join.
Definition wadd_rot := word.add_rot.
Definition wadd_to_left_assoc := word.add_to_left_assoc.
Definition wadd_to_right_assoc := word.add_to_right_assoc.
Definition wadd_opp := word.add_opp.
Definition wadd_opp_l_distant := word.add_opp_l_distant.
Definition wadd_opp_r_distant := word.add_opp_r_distant.
Definition wsub_def := word.sub_def.
Definition wunsigned_of_Z_nowrap := word.unsigned_of_Z_nowrap.
Definition wunsigned_nonneg := word.unsigned_nonneg.
Definition wunsigned_upper := word.unsigned_upper.
Definition wunsigned_sru_to_div_pow2 := word.unsigned_sru_to_div_pow2.
Definition wunsigned_slu_to_mul_pow2 := word.unsigned_slu_to_mul_pow2.
Definition wunsigned_sub := word.unsigned_sub.
Definition wunsigned_add := word.unsigned_add.
Definition H_eq_eq_sym := @eq_eq_sym.
Definition H_eq_same_True := eq_same_True.
Definition and_True_l := and_True_l.
Definition and_True_r := and_True_r.
Definition and_proj_l := and_proj_l.
Definition and_proj_r := and_proj_r.
Definition l_app_to_left_assoc := List.app_assoc.
Definition l_app_to_right_assoc:
  forall (A : Type) (l m n : list A), (l ++ m) ++ n = l ++ m ++ n.
Proof. intros. symmetry. apply List.app_assoc. Qed.
Definition l_length_nil := @List.length_nil.
Definition l_length_cons := @List.length_cons.
Definition l_firstn_O := List.firstn_O.
Definition l_app_nil_l := List.app_nil_l.
Definition l_app_nil_r := List.app_nil_r.
Definition l_firstn_app := List.firstn_app.
Definition l_skipn_app := @List.skipn_app.
Definition l_firstn_firstn := List.firstn_firstn.
Definition l_skipn_skipn := @List.skipn_skipn.
Definition l_firstn_length := List.firstn_length.
Definition l_skipn_length := List.skipn_length.


  Hint Rewrite Z.div_1_r Nat2Z.id : fwd_rewrites.

  Definition simplification1 := forall (ws : list word) (R : mem -> Prop) (addr : word),
      16 <= length ws ->
      iff1 <{ * addr -->
                (ws[: (((addr + (2%Z * 4%Z) to word - addr) to Z) / 4%Z) to nat] ++
                 ws[((addr + (2%Z * 4%Z) to word - addr) to Z / 4%Z) to nat :]
                   [: (10%Z to word) to nat]
                   [5 := ws[((addr + (2%Z * 4%Z) to word - addr) to Z / 4%Z) to nat :]
                           [: (10%Z to word) to nat][5] * 2%Z to word] ++
                 ws[((addr + (2%Z * 4%Z) to word - addr) to Z / 4%Z) to nat +
                    (10%Z to word) to nat :])
              * R }>
           <{ * addr --> ws[7 := ws[7] * 2%Z to word]
              * R }>.

Ltac pose_fwd_list_hints :=
  pose proof List.app_assoc as l_app_to_left_assoc;
  pose proof List.app_assoc as l_app_to_right_assoc; symmetry in l_app_to_right_assoc;
  pose proof @List.length_nil as l_length_nil;
  pose proof @List.length_cons as l_length_cons;
  pose proof List.firstn_O as l_firstn_O;
  pose proof List.app_nil_l as l_app_nil_l;
  pose proof List.app_nil_r as l_app_nil_r;
  pose proof List.firstn_app as l_firstn_app;
  pose proof @List.skipn_app as l_skipn_app;
  pose proof List.firstn_firstn as l_firstn_firstn;
  pose proof @List.skipn_skipn as l_skipn_skipn;
  pose proof List.firstn_length as l_firstn_length;
  (* additional lemmas: *)
  pose proof List.skipn_length as l_skipn_length;
  (* Not supported because higher-order. Concretely, two unsupported features:
     - Function f/predicate P appear with different arities (unapplied/applied)
     - Function f/predicate P appear as a variable at the head of an application.
     Workaround: Define aliases with f/P hardcoded.
  pose proof @List.invert_Forall_cons as l_invert_Forall_cons;
  pose proof @List.invert_NoDup_cons as l_invert_NoDup_cons
  pose proof @List.unfoldn_0 as l_unfoldn_0;
  pose proof @List.unfoldn_S as l_unfoldn_S;
*)
  idtac.

  Axiom TODO: False.

  Lemma simplification1_proof3: simplification1.
  Proof.
    unfold simplification1. intros.

    unfold List.upd, List.upds.
(*    pose_word_lemmas 32%Z word. pose_Prop_lemmas. pose_fwd_list_hints.*)

(*
Time
time "all" (let t := uconstr:(((@rew_zoom_bw _
    (@word.add 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4)))
       (@word.opp 32 word addr)) _ (wsub_def _ _)
    (fun hole =>
     @iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem)
       (@sep (@word.rep 32 word) Init.Byte.byte mem
          (@array 32 word Init.Byte.byte mem (@word.rep 32 word)
             (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr
             (@Datatypes.app (@word.rep 32 word)
                (@List.firstn (@word.rep 32 word)
                   (Z.to_nat (Z.div (@word.unsigned 32 word hole) 4)) ws)
                (@Datatypes.app (@word.rep 32 word)
                   (@Datatypes.app (@word.rep 32 word)
                      (@List.firstn (@word.rep 32 word) (S (S (S (S (S O)))))
                         (@List.firstn (@word.rep 32 word)
                            (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))
                            (@List.skipn (@word.rep 32 word)
                               (Z.to_nat
                                  (Z.div
                                     (@word.unsigned 32 word
                                        (@word.sub 32 word
                                           (@word.add 32 word addr
                                              (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4))
                               ws)))
                      (@Datatypes.app (@word.rep 32 word)
                         (@List.firstn (@word.rep 32 word)
                            (Init.Nat.sub
                               (@length (@word.rep 32 word)
                                  (@List.firstn (@word.rep 32 word)
                                     (Z.to_nat
                                        (@word.unsigned 32 word (@word.of_Z 32 word 10)))
                                     (@List.skipn (@word.rep 32 word)
                                        (Z.to_nat
                                           (Z.div
                                              (@word.unsigned 32 word
                                                 (@word.sub 32 word
                                                    (@word.add 32 word addr
                                                       (@word.of_Z 32 word (Z.mul 2 4)))
                                                    addr)) 4)) ws)))
                               (S (S (S (S (S O))))))
                            (@cons (@word.rep 32 word)
                               (@word.mul 32 word
                                  (@List.nth (@word.rep 32 word)
                                     (S (S (S (S (S O)))))
                                     (@List.firstn (@word.rep 32 word)
                                        (Z.to_nat
                                           (@word.unsigned 32 word (@word.of_Z 32 word 10)))
                                        (@List.skipn (@word.rep 32 word)
                                           (Z.to_nat
                                              (Z.div
                                                 (@word.unsigned 32 word
                                                    (@word.sub 32 word
                                                       (@word.add 32 word addr
                                                          (@word.of_Z 32 word (Z.mul 2 4)))
                                                       addr)) 4)) ws))
                                     (@default (@word.rep 32 word)
                                        (@word_inhabited 32 word)))
                                  (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word))))
                         (@List.skipn (@word.rep 32 word)
                            (Init.Nat.add
                               (@length (@word.rep 32 word)
                                  (@cons (@word.rep 32 word)
                                     (@word.mul 32 word
                                        (@List.nth (@word.rep 32 word)
                                           (S (S (S (S (S O)))))
                                           (@List.firstn (@word.rep 32 word)
                                              (Z.to_nat
                                                 (@word.unsigned 32 word
                                                    (@word.of_Z 32 word 10)))
                                              (@List.skipn (@word.rep 32 word)
                                                 (Z.to_nat
                                                    (Z.div
                                                       (@word.unsigned 32 word
                                                          (@word.sub 32 word
                                                             (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                           (@default (@word.rep 32 word)
                                              (@word_inhabited 32 word)))
                                        (@word.of_Z 32 word 2))
                                     (@nil (@word.rep 32 word))))
                               (S (S (S (S (S O))))))
                            (@List.firstn (@word.rep 32 word)
                               (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))
                               (@List.skipn (@word.rep 32 word)
                                  (Z.to_nat
                                     (Z.div
                                        (@word.unsigned 32 word
                                           (@word.sub 32 word
                                              (@word.add 32 word addr
                                                 (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4))
                                  ws)))))
                   (@List.skipn (@word.rep 32 word)
                      (Init.Nat.add
                         (Z.to_nat
                            (Z.div
                               (@word.unsigned 32 word
                                  (@word.sub 32 word
                                     (@word.add 32 word addr
                                        (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4))
                         (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws))))
          R)
       (@sep (@word.rep 32 word) Init.Byte.byte mem
          (@array 32 word Init.Byte.byte mem (@word.rep 32 word)
             (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr
             (@Datatypes.app (@word.rep 32 word)
                (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws)
                (@Datatypes.app (@word.rep 32 word)
                   (@List.firstn (@word.rep 32 word)
                      (Init.Nat.sub (@length (@word.rep 32 word) ws)
                         (S (S (S (S (S (S (S O))))))))
                      (@cons (@word.rep 32 word)
                         (@word.mul 32 word
                            (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws
                               (@default (@word.rep 32 word) (@word_inhabited 32 word)))
                            (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word))))
                   (@List.skipn (@word.rep 32 word)
                      (Init.Nat.add
                         (@length (@word.rep 32 word)
                            (@cons (@word.rep 32 word)
                               (@word.mul 32 word
                                  (@List.nth (@word.rep 32 word)
                                     (S (S (S (S (S (S (S O))))))) ws
                                     (@default (@word.rep 32 word)
                                        (@word_inhabited 32 word)))
                                  (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word))))
                         (S (S (S (S (S (S (S O)))))))) ws)))) R)))
   ((@rew_zoom_bw _
       (@word.add 32 word addr
          (@word.add 32 word (@word.of_Z 32 word (Z.mul 2 4)) (@word.opp 32 word addr))) _
       (wadd_to_right_assoc _ _ _)
       (fun hole =>
        @iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem)
          (@sep (@word.rep 32 word) Init.Byte.byte mem
             (@array 32 word Init.Byte.byte mem (@word.rep 32 word)
                (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr
                (@Datatypes.app (@word.rep 32 word)
                   (@List.firstn (@word.rep 32 word)
                      (Z.to_nat (Z.div (@word.unsigned 32 word hole) 4)) ws)
                   (@Datatypes.app (@word.rep 32 word)
                      (@Datatypes.app (@word.rep 32 word)
                         (@List.firstn (@word.rep 32 word) (S (S (S (S (S O)))))
                            (@List.firstn (@word.rep 32 word)
                               (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))
                               (@List.skipn (@word.rep 32 word)
                                  (Z.to_nat
                                     (Z.div
                                        (@word.unsigned 32 word
                                           (@word.sub 32 word
                                              (@word.add 32 word addr
                                                 (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4))
                                  ws)))
                         (@Datatypes.app (@word.rep 32 word)
                            (@List.firstn (@word.rep 32 word)
                               (Init.Nat.sub
                                  (@length (@word.rep 32 word)
                                     (@List.firstn (@word.rep 32 word)
                                        (Z.to_nat
                                           (@word.unsigned 32 word (@word.of_Z 32 word 10)))
                                        (@List.skipn (@word.rep 32 word)
                                           (Z.to_nat
                                              (Z.div
                                                 (@word.unsigned 32 word
                                                    (@word.sub 32 word
                                                       (@word.add 32 word addr
                                                          (@word.of_Z 32 word (Z.mul 2 4)))
                                                       addr)) 4)) ws)))
                                  (S (S (S (S (S O))))))
                               (@cons (@word.rep 32 word)
                                  (@word.mul 32 word
                                     (@List.nth (@word.rep 32 word)
                                        (S (S (S (S (S O)))))
                                        (@List.firstn (@word.rep 32 word)
                                           (Z.to_nat
                                              (@word.unsigned 32 word
                                                 (@word.of_Z 32 word 10)))
                                           (@List.skipn (@word.rep 32 word)
                                              (Z.to_nat
                                                 (Z.div
                                                    (@word.unsigned 32 word
                                                       (@word.sub 32 word
                                                          (@word.add 32 word addr
                                                             (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                        (@default (@word.rep 32 word)
                                           (@word_inhabited 32 word)))
                                     (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word))))
                            (@List.skipn (@word.rep 32 word)
                               (Init.Nat.add
                                  (@length (@word.rep 32 word)
                                     (@cons (@word.rep 32 word)
                                        (@word.mul 32 word
                                           (@List.nth (@word.rep 32 word)
                                              (S (S (S (S (S O)))))
                                              (@List.firstn (@word.rep 32 word)
                                                 (Z.to_nat
                                                    (@word.unsigned 32 word
                                                       (@word.of_Z 32 word 10)))
                                                 (@List.skipn (@word.rep 32 word)
                                                    (Z.to_nat
                                                       (Z.div
                                                          (@word.unsigned 32 word
                                                             (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                              (@default (@word.rep 32 word)
                                                 (@word_inhabited 32 word)))
                                           (@word.of_Z 32 word 2))
                                        (@nil (@word.rep 32 word))))
                                  (S (S (S (S (S O))))))
                               (@List.firstn (@word.rep 32 word)
                                  (Z.to_nat
                                     (@word.unsigned 32 word (@word.of_Z 32 word 10)))
                                  (@List.skipn (@word.rep 32 word)
                                     (Z.to_nat
                                        (Z.div
                                           (@word.unsigned 32 word
                                              (@word.sub 32 word
                                                 (@word.add 32 word addr
                                                    (@word.of_Z 32 word (Z.mul 2 4))) addr))
                                           4)) ws)))))
                      (@List.skipn (@word.rep 32 word)
                         (Init.Nat.add
                            (Z.to_nat
                               (Z.div
                                  (@word.unsigned 32 word
                                     (@word.sub 32 word
                                        (@word.add 32 word addr
                                           (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4))
                            (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws))))
             R)
          (@sep (@word.rep 32 word) Init.Byte.byte mem
             (@array 32 word Init.Byte.byte mem (@word.rep 32 word)
                (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr
                (@Datatypes.app (@word.rep 32 word)
                   (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws)
                   (@Datatypes.app (@word.rep 32 word)
                      (@List.firstn (@word.rep 32 word)
                         (Init.Nat.sub (@length (@word.rep 32 word) ws)
                            (S (S (S (S (S (S (S O))))))))
                         (@cons (@word.rep 32 word)
                            (@word.mul 32 word
                               (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O)))))))
                                  ws
                                  (@default (@word.rep 32 word) (@word_inhabited 32 word)))
                               (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word))))
                      (@List.skipn (@word.rep 32 word)
                         (Init.Nat.add
                            (@length (@word.rep 32 word)
                               (@cons (@word.rep 32 word)
                                  (@word.mul 32 word
                                     (@List.nth (@word.rep 32 word)
                                        (S (S (S (S (S (S (S O))))))) ws
                                        (@default (@word.rep 32 word)
                                           (@word_inhabited 32 word)))
                                     (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word))))
                            (S (S (S (S (S (S (S O)))))))) ws)))) R)))
      ((@rew_zoom_bw _ (@word.of_Z 32 word (Z.mul 2 4)) _ (wadd_opp_r_distant _ _)
          (fun hole =>
           @iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem)
             (@sep (@word.rep 32 word) Init.Byte.byte mem
                (@array 32 word Init.Byte.byte mem (@word.rep 32 word)
                   (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr
                   (@Datatypes.app (@word.rep 32 word)
                      (@List.firstn (@word.rep 32 word)
                         (Z.to_nat (Z.div (@word.unsigned 32 word hole) 4)) ws)
                      (@Datatypes.app (@word.rep 32 word)
                         (@Datatypes.app (@word.rep 32 word)
                            (@List.firstn (@word.rep 32 word) (S (S (S (S (S O)))))
                               (@List.firstn (@word.rep 32 word)
                                  (Z.to_nat
                                     (@word.unsigned 32 word (@word.of_Z 32 word 10)))
                                  (@List.skipn (@word.rep 32 word)
                                     (Z.to_nat
                                        (Z.div
                                           (@word.unsigned 32 word
                                              (@word.sub 32 word
                                                 (@word.add 32 word addr
                                                    (@word.of_Z 32 word (Z.mul 2 4))) addr))
                                           4)) ws)))
                            (@Datatypes.app (@word.rep 32 word)
                               (@List.firstn (@word.rep 32 word)
                                  (Init.Nat.sub
                                     (@length (@word.rep 32 word)
                                        (@List.firstn (@word.rep 32 word)
                                           (Z.to_nat
                                              (@word.unsigned 32 word
                                                 (@word.of_Z 32 word 10)))
                                           (@List.skipn (@word.rep 32 word)
                                              (Z.to_nat
                                                 (Z.div
                                                    (@word.unsigned 32 word
                                                       (@word.sub 32 word
                                                          (@word.add 32 word addr
                                                             (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws)))
                                     (S (S (S (S (S O))))))
                                  (@cons (@word.rep 32 word)
                                     (@word.mul 32 word
                                        (@List.nth (@word.rep 32 word)
                                           (S (S (S (S (S O)))))
                                           (@List.firstn (@word.rep 32 word)
                                              (Z.to_nat
                                                 (@word.unsigned 32 word
                                                    (@word.of_Z 32 word 10)))
                                              (@List.skipn (@word.rep 32 word)
                                                 (Z.to_nat
                                                    (Z.div
                                                       (@word.unsigned 32 word
                                                          (@word.sub 32 word
                                                             (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                           (@default (@word.rep 32 word)
                                              (@word_inhabited 32 word)))
                                        (@word.of_Z 32 word 2))
                                     (@nil (@word.rep 32 word))))
                               (@List.skipn (@word.rep 32 word)
                                  (Init.Nat.add
                                     (@length (@word.rep 32 word)
                                        (@cons (@word.rep 32 word)
                                           (@word.mul 32 word
                                              (@List.nth (@word.rep 32 word)
                                                 (S (S (S (S (S O)))))
                                                 (@List.firstn
                                                    (@word.rep 32 word)
                                                    (Z.to_nat
                                                       (@word.unsigned 32 word
                                                          (@word.of_Z 32 word 10)))
                                                    (@List.skipn
                                                       (@word.rep 32 word)
                                                       (Z.to_nat
                                                          (Z.div
                                                             (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                                 (@default (@word.rep 32 word)
                                                    (@word_inhabited 32 word)))
                                              (@word.of_Z 32 word 2))
                                           (@nil (@word.rep 32 word))))
                                     (S (S (S (S (S O))))))
                                  (@List.firstn (@word.rep 32 word)
                                     (Z.to_nat
                                        (@word.unsigned 32 word (@word.of_Z 32 word 10)))
                                     (@List.skipn (@word.rep 32 word)
                                        (Z.to_nat
                                           (Z.div
                                              (@word.unsigned 32 word
                                                 (@word.sub 32 word
                                                    (@word.add 32 word addr
                                                       (@word.of_Z 32 word (Z.mul 2 4)))
                                                    addr)) 4)) ws)))))
                         (@List.skipn (@word.rep 32 word)
                            (Init.Nat.add
                               (Z.to_nat
                                  (Z.div
                                     (@word.unsigned 32 word
                                        (@word.sub 32 word
                                           (@word.add 32 word addr
                                              (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4))
                               (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))))
                            ws)))) R)
             (@sep (@word.rep 32 word) Init.Byte.byte mem
                (@array 32 word Init.Byte.byte mem (@word.rep 32 word)
                   (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr
                   (@Datatypes.app (@word.rep 32 word)
                      (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws)
                      (@Datatypes.app (@word.rep 32 word)
                         (@List.firstn (@word.rep 32 word)
                            (Init.Nat.sub (@length (@word.rep 32 word) ws)
                               (S (S (S (S (S (S (S O))))))))
                            (@cons (@word.rep 32 word)
                               (@word.mul 32 word
                                  (@List.nth (@word.rep 32 word)
                                     (S (S (S (S (S (S (S O))))))) ws
                                     (@default (@word.rep 32 word)
                                        (@word_inhabited 32 word)))
                                  (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word))))
                         (@List.skipn (@word.rep 32 word)
                            (Init.Nat.add
                               (@length (@word.rep 32 word)
                                  (@cons (@word.rep 32 word)
                                     (@word.mul 32 word
                                        (@List.nth (@word.rep 32 word)
                                           (S (S (S (S (S (S (S O))))))) ws
                                           (@default (@word.rep 32 word)
                                              (@word_inhabited 32 word)))
                                        (@word.of_Z 32 word 2))
                                     (@nil (@word.rep 32 word))))
                               (S (S (S (S (S (S (S O)))))))) ws)))) R)))
         ((@rew_zoom_bw _
             (@Datatypes.app (@word.rep 32 word)
                (@List.firstn (@word.rep 32 word) (S (S (S (S (S O)))))
                   (@List.firstn (@word.rep 32 word)
                      (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))
                      (@List.skipn (@word.rep 32 word)
                         (Z.to_nat
                            (Z.div
                               (@word.unsigned 32 word
                                  (@word.sub 32 word
                                     (@word.add 32 word addr
                                        (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)))
                (@Datatypes.app (@word.rep 32 word)
                   (@Datatypes.app (@word.rep 32 word)
                      (@List.firstn (@word.rep 32 word)
                         (Init.Nat.sub
                            (@length (@word.rep 32 word)
                               (@List.firstn (@word.rep 32 word)
                                  (Z.to_nat
                                     (@word.unsigned 32 word (@word.of_Z 32 word 10)))
                                  (@List.skipn (@word.rep 32 word)
                                     (Z.to_nat
                                        (Z.div
                                           (@word.unsigned 32 word
                                              (@word.sub 32 word
                                                 (@word.add 32 word addr
                                                    (@word.of_Z 32 word (Z.mul 2 4))) addr))
                                           4)) ws))) (S (S (S (S (S O))))))
                         (@cons (@word.rep 32 word)
                            (@word.mul 32 word
                               (@List.nth (@word.rep 32 word) (S (S (S (S (S O)))))
                                  (@List.firstn (@word.rep 32 word)
                                     (Z.to_nat
                                        (@word.unsigned 32 word (@word.of_Z 32 word 10)))
                                     (@List.skipn (@word.rep 32 word)
                                        (Z.to_nat
                                           (Z.div
                                              (@word.unsigned 32 word
                                                 (@word.sub 32 word
                                                    (@word.add 32 word addr
                                                       (@word.of_Z 32 word (Z.mul 2 4)))
                                                    addr)) 4)) ws))
                                  (@default (@word.rep 32 word) (@word_inhabited 32 word)))
                               (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word))))
                      (@List.skipn (@word.rep 32 word)
                         (Init.Nat.add
                            (@length (@word.rep 32 word)
                               (@cons (@word.rep 32 word)
                                  (@word.mul 32 word
                                     (@List.nth (@word.rep 32 word)
                                        (S (S (S (S (S O)))))
                                        (@List.firstn (@word.rep 32 word)
                                           (Z.to_nat
                                              (@word.unsigned 32 word
                                                 (@word.of_Z 32 word 10)))
                                           (@List.skipn (@word.rep 32 word)
                                              (Z.to_nat
                                                 (Z.div
                                                    (@word.unsigned 32 word
                                                       (@word.sub 32 word
                                                          (@word.add 32 word addr
                                                             (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                        (@default (@word.rep 32 word)
                                           (@word_inhabited 32 word)))
                                     (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word))))
                            (S (S (S (S (S O))))))
                         (@List.firstn (@word.rep 32 word)
                            (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))
                            (@List.skipn (@word.rep 32 word)
                               (Z.to_nat
                                  (Z.div
                                     (@word.unsigned 32 word
                                        (@word.sub 32 word
                                           (@word.add 32 word addr
                                              (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4))
                               ws))))
                   (@List.skipn (@word.rep 32 word)
                      (Init.Nat.add
                         (Z.to_nat
                            (Z.div
                               (@word.unsigned 32 word
                                  (@word.sub 32 word
                                     (@word.add 32 word addr
                                        (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4))
                         (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws)))
             _ (l_app_to_right_assoc _ _ _ _)
             (fun hole =>
              @iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem)
                (@sep (@word.rep 32 word) Init.Byte.byte mem
                   (@array 32 word Init.Byte.byte mem (@word.rep 32 word)
                      (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr
                      (@Datatypes.app (@word.rep 32 word)
                         (@List.firstn (@word.rep 32 word)
                            (Z.to_nat
                               (Z.div
                                  (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4)))
                                  4)) ws) hole)) R)
                (@sep (@word.rep 32 word) Init.Byte.byte mem
                   (@array 32 word Init.Byte.byte mem (@word.rep 32 word)
                      (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr
                      (@Datatypes.app (@word.rep 32 word)
                         (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws)
                         (@Datatypes.app (@word.rep 32 word)
                            (@List.firstn (@word.rep 32 word)
                               (Init.Nat.sub (@length (@word.rep 32 word) ws)
                                  (S (S (S (S (S (S (S O))))))))
                               (@cons (@word.rep 32 word)
                                  (@word.mul 32 word
                                     (@List.nth (@word.rep 32 word)
                                        (S (S (S (S (S (S (S O))))))) ws
                                        (@default (@word.rep 32 word)
                                           (@word_inhabited 32 word)))
                                     (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word))))
                            (@List.skipn (@word.rep 32 word)
                               (Init.Nat.add
                                  (@length (@word.rep 32 word)
                                     (@cons (@word.rep 32 word)
                                        (@word.mul 32 word
                                           (@List.nth (@word.rep 32 word)
                                              (S (S (S (S (S (S (S O))))))) ws
                                              (@default (@word.rep 32 word)
                                                 (@word_inhabited 32 word)))
                                           (@word.of_Z 32 word 2))
                                        (@nil (@word.rep 32 word))))
                                  (S (S (S (S (S (S (S O)))))))) ws)))) R)))
            ((@rew_zoom_bw _
                (@List.firstn (@word.rep 32 word)
                   (Init.Nat.min (S (S (S (S (S O)))))
                      (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))))
                   (@List.skipn (@word.rep 32 word)
                      (Z.to_nat
                         (Z.div
                            (@word.unsigned 32 word
                               (@word.sub 32 word
                                  (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4)))
                                  addr)) 4)) ws)) _ (l_firstn_firstn _ _ _ _)
                (fun hole =>
                 @iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem)
                   (@sep (@word.rep 32 word) Init.Byte.byte mem
                      (@array 32 word Init.Byte.byte mem (@word.rep 32 word)
                         (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr
                         (@Datatypes.app (@word.rep 32 word)
                            (@List.firstn (@word.rep 32 word)
                               (Z.to_nat
                                  (Z.div
                                     (@word.unsigned 32 word
                                        (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)
                            (@Datatypes.app (@word.rep 32 word) hole
                               (@Datatypes.app (@word.rep 32 word)
                                  (@Datatypes.app (@word.rep 32 word)
                                     (@List.firstn (@word.rep 32 word)
                                        (Init.Nat.sub
                                           (@length (@word.rep 32 word)
                                              (@List.firstn (@word.rep 32 word)
                                                 (Z.to_nat
                                                    (@word.unsigned 32 word
                                                       (@word.of_Z 32 word 10)))
                                                 (@List.skipn (@word.rep 32 word)
                                                    (Z.to_nat
                                                       (Z.div
                                                          (@word.unsigned 32 word
                                                             (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws)))
                                           (S (S (S (S (S O))))))
                                        (@cons (@word.rep 32 word)
                                           (@word.mul 32 word
                                              (@List.nth (@word.rep 32 word)
                                                 (S (S (S (S (S O)))))
                                                 (@List.firstn
                                                    (@word.rep 32 word)
                                                    (Z.to_nat
                                                       (@word.unsigned 32 word
                                                          (@word.of_Z 32 word 10)))
                                                    (@List.skipn
                                                       (@word.rep 32 word)
                                                       (Z.to_nat
                                                          (Z.div
                                                             (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                                 (@default (@word.rep 32 word)
                                                    (@word_inhabited 32 word)))
                                              (@word.of_Z 32 word 2))
                                           (@nil (@word.rep 32 word))))
                                     (@List.skipn (@word.rep 32 word)
                                        (Init.Nat.add
                                           (@length (@word.rep 32 word)
                                              (@cons (@word.rep 32 word)
                                                 (@word.mul 32 word
                                                    (@List.nth
                                                       (@word.rep 32 word)
                                                       (S (S (S (S (S O)))))
                                                       (@List.firstn
                                                          (@word.rep 32 word)
                                                          (Z.to_nat
                                                             (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                          (@List.skipn
                                                             (@word.rep 32 word)
                                                             (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                                       (@default
                                                          (@word.rep 32 word)
                                                          (@word_inhabited 32 word)))
                                                    (@word.of_Z 32 word 2))
                                                 (@nil (@word.rep 32 word))))
                                           (S (S (S (S (S O))))))
                                        (@List.firstn (@word.rep 32 word)
                                           (Z.to_nat
                                              (@word.unsigned 32 word
                                                 (@word.of_Z 32 word 10)))
                                           (@List.skipn (@word.rep 32 word)
                                              (Z.to_nat
                                                 (Z.div
                                                    (@word.unsigned 32 word
                                                       (@word.sub 32 word
                                                          (@word.add 32 word addr
                                                             (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))))
                                  (@List.skipn (@word.rep 32 word)
                                     (Init.Nat.add
                                        (Z.to_nat
                                           (Z.div
                                              (@word.unsigned 32 word
                                                 (@word.sub 32 word
                                                    (@word.add 32 word addr
                                                       (@word.of_Z 32 word (Z.mul 2 4)))
                                                    addr)) 4))
                                        (Z.to_nat
                                           (@word.unsigned 32 word (@word.of_Z 32 word 10))))
                                     ws))))) R)
                   (@sep (@word.rep 32 word) Init.Byte.byte mem
                      (@array 32 word Init.Byte.byte mem (@word.rep 32 word)
                         (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr
                         (@Datatypes.app (@word.rep 32 word)
                            (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O)))))))
                               ws)
                            (@Datatypes.app (@word.rep 32 word)
                               (@List.firstn (@word.rep 32 word)
                                  (Init.Nat.sub (@length (@word.rep 32 word) ws)
                                     (S (S (S (S (S (S (S O))))))))
                                  (@cons (@word.rep 32 word)
                                     (@word.mul 32 word
                                        (@List.nth (@word.rep 32 word)
                                           (S (S (S (S (S (S (S O))))))) ws
                                           (@default (@word.rep 32 word)
                                              (@word_inhabited 32 word)))
                                        (@word.of_Z 32 word 2))
                                     (@nil (@word.rep 32 word))))
                               (@List.skipn (@word.rep 32 word)
                                  (Init.Nat.add
                                     (@length (@word.rep 32 word)
                                        (@cons (@word.rep 32 word)
                                           (@word.mul 32 word
                                              (@List.nth (@word.rep 32 word)
                                                 (S (S (S (S (S (S (S O))))))) ws
                                                 (@default (@word.rep 32 word)
                                                    (@word_inhabited 32 word)))
                                              (@word.of_Z 32 word 2))
                                           (@nil (@word.rep 32 word))))
                                     (S (S (S (S (S (S (S O)))))))) ws)))) R)))
               ((@rew_zoom_bw _
                   (@word.add 32 word
                      (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4)))
                      (@word.opp 32 word addr)) _ (wsub_def _ _)
                   (fun hole =>
                    @iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem)
                      (@sep (@word.rep 32 word) Init.Byte.byte mem
                         (@array 32 word Init.Byte.byte mem (@word.rep 32 word)
                            (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr
                            (@Datatypes.app (@word.rep 32 word)
                               (@List.firstn (@word.rep 32 word)
                                  (Z.to_nat
                                     (Z.div
                                        (@word.unsigned 32 word
                                           (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)
                               (@Datatypes.app (@word.rep 32 word)
                                  (@List.firstn (@word.rep 32 word)
                                     (Init.Nat.min (S (S (S (S (S O)))))
                                        (Z.to_nat
                                           (@word.unsigned 32 word (@word.of_Z 32 word 10))))
                                     (@List.skipn (@word.rep 32 word)
                                        (Z.to_nat (Z.div (@word.unsigned 32 word hole) 4))
                                        ws))
                                  (@Datatypes.app (@word.rep 32 word)
                                     (@Datatypes.app (@word.rep 32 word)
                                        (@List.firstn (@word.rep 32 word)
                                           (Init.Nat.sub
                                              (@length (@word.rep 32 word)
                                                 (@List.firstn
                                                    (@word.rep 32 word)
                                                    (Z.to_nat
                                                       (@word.unsigned 32 word
                                                          (@word.of_Z 32 word 10)))
                                                    (@List.skipn
                                                       (@word.rep 32 word)
                                                       (Z.to_nat
                                                          (Z.div
                                                             (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws)))
                                              (S (S (S (S (S O))))))
                                           (@cons (@word.rep 32 word)
                                              (@word.mul 32 word
                                                 (@List.nth (@word.rep 32 word)
                                                    (S (S (S (S (S O)))))
                                                    (@List.firstn
                                                       (@word.rep 32 word)
                                                       (Z.to_nat
                                                          (@word.unsigned 32 word
                                                             (@word.of_Z 32 word 10)))
                                                       (@List.skipn
                                                          (@word.rep 32 word)
                                                          (Z.to_nat
                                                             (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                                    (@default (@word.rep 32 word)
                                                       (@word_inhabited 32 word)))
                                                 (@word.of_Z 32 word 2))
                                              (@nil (@word.rep 32 word))))
                                        (@List.skipn (@word.rep 32 word)
                                           (Init.Nat.add
                                              (@length (@word.rep 32 word)
                                                 (@cons (@word.rep 32 word)
                                                    (@word.mul 32 word
                                                       (@List.nth
                                                          (@word.rep 32 word)
                                                          (S (S (S (S (S O)))))
                                                          (@List.firstn
                                                             (@word.rep 32 word)
                                                             (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                             (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                                          (@default
                                                             (@word.rep 32 word)
                                                             (@word_inhabited 32 word)))
                                                       (@word.of_Z 32 word 2))
                                                    (@nil (@word.rep 32 word))))
                                              (S (S (S (S (S O))))))
                                           (@List.firstn (@word.rep 32 word)
                                              (Z.to_nat
                                                 (@word.unsigned 32 word
                                                    (@word.of_Z 32 word 10)))
                                              (@List.skipn (@word.rep 32 word)
                                                 (Z.to_nat
                                                    (Z.div
                                                       (@word.unsigned 32 word
                                                          (@word.sub 32 word
                                                             (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))))
                                     (@List.skipn (@word.rep 32 word)
                                        (Init.Nat.add
                                           (Z.to_nat
                                              (Z.div
                                                 (@word.unsigned 32 word
                                                    (@word.sub 32 word
                                                       (@word.add 32 word addr
                                                          (@word.of_Z 32 word (Z.mul 2 4)))
                                                       addr)) 4))
                                           (Z.to_nat
                                              (@word.unsigned 32 word
                                                 (@word.of_Z 32 word 10)))) ws))))) R)
                      (@sep (@word.rep 32 word) Init.Byte.byte mem
                         (@array 32 word Init.Byte.byte mem (@word.rep 32 word)
                            (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr
                            (@Datatypes.app (@word.rep 32 word)
                               (@List.firstn (@word.rep 32 word)
                                  (S (S (S (S (S (S (S O))))))) ws)
                               (@Datatypes.app (@word.rep 32 word)
                                  (@List.firstn (@word.rep 32 word)
                                     (Init.Nat.sub (@length (@word.rep 32 word) ws)
                                        (S (S (S (S (S (S (S O))))))))
                                     (@cons (@word.rep 32 word)
                                        (@word.mul 32 word
                                           (@List.nth (@word.rep 32 word)
                                              (S (S (S (S (S (S (S O))))))) ws
                                              (@default (@word.rep 32 word)
                                                 (@word_inhabited 32 word)))
                                           (@word.of_Z 32 word 2))
                                        (@nil (@word.rep 32 word))))
                                  (@List.skipn (@word.rep 32 word)
                                     (Init.Nat.add
                                        (@length (@word.rep 32 word)
                                           (@cons (@word.rep 32 word)
                                              (@word.mul 32 word
                                                 (@List.nth (@word.rep 32 word)
                                                    (S (S (S (S (S (S (S O))))))) ws
                                                    (@default (@word.rep 32 word)
                                                       (@word_inhabited 32 word)))
                                                 (@word.of_Z 32 word 2))
                                              (@nil (@word.rep 32 word))))
                                        (S (S (S (S (S (S (S O)))))))) ws)))) R)))
                  ((@rew_zoom_bw _
                      (@word.add 32 word addr
                         (@word.add 32 word (@word.of_Z 32 word (Z.mul 2 4))
                            (@word.opp 32 word addr))) _ (wadd_to_right_assoc _ _ _)
                      (fun hole =>
                       @iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem)
                         (@sep (@word.rep 32 word) Init.Byte.byte mem
                            (@array 32 word Init.Byte.byte mem
                               (@word.rep 32 word) (@Scalars.scalar 32 word mem)
                               (@word.of_Z 32 word 4) addr
                               (@Datatypes.app (@word.rep 32 word)
                                  (@List.firstn (@word.rep 32 word)
                                     (Z.to_nat
                                        (Z.div
                                           (@word.unsigned 32 word
                                              (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)
                                  (@Datatypes.app (@word.rep 32 word)
                                     (@List.firstn (@word.rep 32 word)
                                        (Init.Nat.min (S (S (S (S (S O)))))
                                           (Z.to_nat
                                              (@word.unsigned 32 word
                                                 (@word.of_Z 32 word 10))))
                                        (@List.skipn (@word.rep 32 word)
                                           (Z.to_nat
                                              (Z.div (@word.unsigned 32 word hole) 4)) ws))
                                     (@Datatypes.app (@word.rep 32 word)
                                        (@Datatypes.app (@word.rep 32 word)
                                           (@List.firstn (@word.rep 32 word)
                                              (Init.Nat.sub
                                                 (@length (@word.rep 32 word)
                                                    (@List.firstn
                                                       (@word.rep 32 word)
                                                       (Z.to_nat
                                                          (@word.unsigned 32 word
                                                             (@word.of_Z 32 word 10)))
                                                       (@List.skipn
                                                          (@word.rep 32 word)
                                                          (Z.to_nat
                                                             (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws)))
                                                 (S (S (S (S (S O))))))
                                              (@cons (@word.rep 32 word)
                                                 (@word.mul 32 word
                                                    (@List.nth
                                                       (@word.rep 32 word)
                                                       (S (S (S (S (S O)))))
                                                       (@List.firstn
                                                          (@word.rep 32 word)
                                                          (Z.to_nat
                                                             (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                          (@List.skipn
                                                             (@word.rep 32 word)
                                                             (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                                       (@default
                                                          (@word.rep 32 word)
                                                          (@word_inhabited 32 word)))
                                                    (@word.of_Z 32 word 2))
                                                 (@nil (@word.rep 32 word))))
                                           (@List.skipn (@word.rep 32 word)
                                              (Init.Nat.add
                                                 (@length (@word.rep 32 word)
                                                    (@cons (@word.rep 32 word)
                                                       (@word.mul 32 word
                                                          (@List.nth
                                                             (@word.rep 32 word)
                                                             (S (S (S (S (S O)))))
                                                             (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                                             (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                          (@word.of_Z 32 word 2))
                                                       (@nil (@word.rep 32 word))))
                                                 (S (S (S (S (S O))))))
                                              (@List.firstn (@word.rep 32 word)
                                                 (Z.to_nat
                                                    (@word.unsigned 32 word
                                                       (@word.of_Z 32 word 10)))
                                                 (@List.skipn (@word.rep 32 word)
                                                    (Z.to_nat
                                                       (Z.div
                                                          (@word.unsigned 32 word
                                                             (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))))
                                        (@List.skipn (@word.rep 32 word)
                                           (Init.Nat.add
                                              (Z.to_nat
                                                 (Z.div
                                                    (@word.unsigned 32 word
                                                       (@word.sub 32 word
                                                          (@word.add 32 word addr
                                                             (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4))
                                              (Z.to_nat
                                                 (@word.unsigned 32 word
                                                    (@word.of_Z 32 word 10)))) ws))))) R)
                         (@sep (@word.rep 32 word) Init.Byte.byte mem
                            (@array 32 word Init.Byte.byte mem
                               (@word.rep 32 word) (@Scalars.scalar 32 word mem)
                               (@word.of_Z 32 word 4) addr
                               (@Datatypes.app (@word.rep 32 word)
                                  (@List.firstn (@word.rep 32 word)
                                     (S (S (S (S (S (S (S O))))))) ws)
                                  (@Datatypes.app (@word.rep 32 word)
                                     (@List.firstn (@word.rep 32 word)
                                        (Init.Nat.sub (@length (@word.rep 32 word) ws)
                                           (S (S (S (S (S (S (S O))))))))
                                        (@cons (@word.rep 32 word)
                                           (@word.mul 32 word
                                              (@List.nth (@word.rep 32 word)
                                                 (S (S (S (S (S (S (S O))))))) ws
                                                 (@default (@word.rep 32 word)
                                                    (@word_inhabited 32 word)))
                                              (@word.of_Z 32 word 2))
                                           (@nil (@word.rep 32 word))))
                                     (@List.skipn (@word.rep 32 word)
                                        (Init.Nat.add
                                           (@length (@word.rep 32 word)
                                              (@cons (@word.rep 32 word)
                                                 (@word.mul 32 word
                                                    (@List.nth
                                                       (@word.rep 32 word)
                                                       (S (S (S (S (S (S (S O))))))) ws
                                                       (@default
                                                          (@word.rep 32 word)
                                                          (@word_inhabited 32 word)))
                                                    (@word.of_Z 32 word 2))
                                                 (@nil (@word.rep 32 word))))
                                           (S (S (S (S (S (S (S O)))))))) ws)))) R)))
                     ((@rew_zoom_bw _ (@word.of_Z 32 word (Z.mul 2 4)) _
                         (wadd_opp_r_distant _ _)
                         (fun hole =>
                          @iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem)
                            (@sep (@word.rep 32 word) Init.Byte.byte mem
                               (@array 32 word Init.Byte.byte mem
                                  (@word.rep 32 word) (@Scalars.scalar 32 word mem)
                                  (@word.of_Z 32 word 4) addr
                                  (@Datatypes.app (@word.rep 32 word)
                                     (@List.firstn (@word.rep 32 word)
                                        (Z.to_nat
                                           (Z.div
                                              (@word.unsigned 32 word
                                                 (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)
                                     (@Datatypes.app (@word.rep 32 word)
                                        (@List.firstn (@word.rep 32 word)
                                           (Init.Nat.min (S (S (S (S (S O)))))
                                              (Z.to_nat
                                                 (@word.unsigned 32 word
                                                    (@word.of_Z 32 word 10))))
                                           (@List.skipn (@word.rep 32 word)
                                              (Z.to_nat
                                                 (Z.div (@word.unsigned 32 word hole) 4))
                                              ws))
                                        (@Datatypes.app (@word.rep 32 word)
                                           (@Datatypes.app (@word.rep 32 word)
                                              (@List.firstn (@word.rep 32 word)
                                                 (Init.Nat.sub
                                                    (@length (@word.rep 32 word)
                                                       (@List.firstn
                                                          (@word.rep 32 word)
                                                          (Z.to_nat
                                                             (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                          (@List.skipn
                                                             (@word.rep 32 word)
                                                             (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws)))
                                                    (S (S (S (S (S O))))))
                                                 (@cons (@word.rep 32 word)
                                                    (@word.mul 32 word
                                                       (@List.nth
                                                          (@word.rep 32 word)
                                                          (S (S (S (S (S O)))))
                                                          (@List.firstn
                                                             (@word.rep 32 word)
                                                             (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                             (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                                          (@default
                                                             (@word.rep 32 word)
                                                             (@word_inhabited 32 word)))
                                                       (@word.of_Z 32 word 2))
                                                    (@nil (@word.rep 32 word))))
                                              (@List.skipn (@word.rep 32 word)
                                                 (Init.Nat.add
                                                    (@length (@word.rep 32 word)
                                                       (@cons (@word.rep 32 word)
                                                          (@word.mul 32 word
                                                             (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S O)))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                             (@word.of_Z 32 word 2))
                                                          (@nil (@word.rep 32 word))))
                                                    (S (S (S (S (S O))))))
                                                 (@List.firstn
                                                    (@word.rep 32 word)
                                                    (Z.to_nat
                                                       (@word.unsigned 32 word
                                                          (@word.of_Z 32 word 10)))
                                                    (@List.skipn
                                                       (@word.rep 32 word)
                                                       (Z.to_nat
                                                          (Z.div
                                                             (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))))
                                           (@List.skipn (@word.rep 32 word)
                                              (Init.Nat.add
                                                 (Z.to_nat
                                                    (Z.div
                                                       (@word.unsigned 32 word
                                                          (@word.sub 32 word
                                                             (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4))
                                                 (Z.to_nat
                                                    (@word.unsigned 32 word
                                                       (@word.of_Z 32 word 10)))) ws))))) R)
                            (@sep (@word.rep 32 word) Init.Byte.byte mem
                               (@array 32 word Init.Byte.byte mem
                                  (@word.rep 32 word) (@Scalars.scalar 32 word mem)
                                  (@word.of_Z 32 word 4) addr
                                  (@Datatypes.app (@word.rep 32 word)
                                     (@List.firstn (@word.rep 32 word)
                                        (S (S (S (S (S (S (S O))))))) ws)
                                     (@Datatypes.app (@word.rep 32 word)
                                        (@List.firstn (@word.rep 32 word)
                                           (Init.Nat.sub (@length (@word.rep 32 word) ws)
                                              (S (S (S (S (S (S (S O))))))))
                                           (@cons (@word.rep 32 word)
                                              (@word.mul 32 word
                                                 (@List.nth (@word.rep 32 word)
                                                    (S (S (S (S (S (S (S O))))))) ws
                                                    (@default (@word.rep 32 word)
                                                       (@word_inhabited 32 word)))
                                                 (@word.of_Z 32 word 2))
                                              (@nil (@word.rep 32 word))))
                                        (@List.skipn (@word.rep 32 word)
                                           (Init.Nat.add
                                              (@length (@word.rep 32 word)
                                                 (@cons (@word.rep 32 word)
                                                    (@word.mul 32 word
                                                       (@List.nth
                                                          (@word.rep 32 word)
                                                          (S (S (S (S (S (S (S O))))))) ws
                                                          (@default
                                                             (@word.rep 32 word)
                                                             (@word_inhabited 32 word)))
                                                       (@word.of_Z 32 word 2))
                                                    (@nil (@word.rep 32 word))))
                                              (S (S (S (S (S (S (S O)))))))) ws)))) R)))
                        ((@rew_zoom_bw _
                            (@Datatypes.app (@word.rep 32 word)
                               (@List.firstn (@word.rep 32 word)
                                  (Init.Nat.sub
                                     (@length (@word.rep 32 word)
                                        (@List.firstn (@word.rep 32 word)
                                           (Z.to_nat
                                              (@word.unsigned 32 word
                                                 (@word.of_Z 32 word 10)))
                                           (@List.skipn (@word.rep 32 word)
                                              (Z.to_nat
                                                 (Z.div
                                                    (@word.unsigned 32 word
                                                       (@word.sub 32 word
                                                          (@word.add 32 word addr
                                                             (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws)))
                                     (S (S (S (S (S O))))))
                                  (@cons (@word.rep 32 word)
                                     (@word.mul 32 word
                                        (@List.nth (@word.rep 32 word)
                                           (S (S (S (S (S O)))))
                                           (@List.firstn (@word.rep 32 word)
                                              (Z.to_nat
                                                 (@word.unsigned 32 word
                                                    (@word.of_Z 32 word 10)))
                                              (@List.skipn (@word.rep 32 word)
                                                 (Z.to_nat
                                                    (Z.div
                                                       (@word.unsigned 32 word
                                                          (@word.sub 32 word
                                                             (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                           (@default (@word.rep 32 word)
                                              (@word_inhabited 32 word)))
                                        (@word.of_Z 32 word 2))
                                     (@nil (@word.rep 32 word))))
                               (@Datatypes.app (@word.rep 32 word)
                                  (@List.skipn (@word.rep 32 word)
                                     (Init.Nat.add
                                        (@length (@word.rep 32 word)
                                           (@cons (@word.rep 32 word)
                                              (@word.mul 32 word
                                                 (@List.nth (@word.rep 32 word)
                                                    (S (S (S (S (S O)))))
                                                    (@List.firstn
                                                       (@word.rep 32 word)
                                                       (Z.to_nat
                                                          (@word.unsigned 32 word
                                                             (@word.of_Z 32 word 10)))
                                                       (@List.skipn
                                                          (@word.rep 32 word)
                                                          (Z.to_nat
                                                             (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                                    (@default (@word.rep 32 word)
                                                       (@word_inhabited 32 word)))
                                                 (@word.of_Z 32 word 2))
                                              (@nil (@word.rep 32 word))))
                                        (S (S (S (S (S O))))))
                                     (@List.firstn (@word.rep 32 word)
                                        (Z.to_nat
                                           (@word.unsigned 32 word (@word.of_Z 32 word 10)))
                                        (@List.skipn (@word.rep 32 word)
                                           (Z.to_nat
                                              (Z.div
                                                 (@word.unsigned 32 word
                                                    (@word.sub 32 word
                                                       (@word.add 32 word addr
                                                          (@word.of_Z 32 word (Z.mul 2 4)))
                                                       addr)) 4)) ws)))
                                  (@List.skipn (@word.rep 32 word)
                                     (Init.Nat.add
                                        (Z.to_nat
                                           (Z.div
                                              (@word.unsigned 32 word
                                                 (@word.sub 32 word
                                                    (@word.add 32 word addr
                                                       (@word.of_Z 32 word (Z.mul 2 4)))
                                                    addr)) 4))
                                        (Z.to_nat
                                           (@word.unsigned 32 word (@word.of_Z 32 word 10))))
                                     ws))) _ (l_app_to_right_assoc _ _ _ _)
                            (fun hole =>
                             @iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem)
                               (@sep (@word.rep 32 word) Init.Byte.byte mem
                                  (@array 32 word Init.Byte.byte mem
                                     (@word.rep 32 word) (@Scalars.scalar 32 word mem)
                                     (@word.of_Z 32 word 4) addr
                                     (@Datatypes.app (@word.rep 32 word)
                                        (@List.firstn (@word.rep 32 word)
                                           (Z.to_nat
                                              (Z.div
                                                 (@word.unsigned 32 word
                                                    (@word.of_Z 32 word (Z.mul 2 4))) 4))
                                           ws)
                                        (@Datatypes.app (@word.rep 32 word)
                                           (@List.firstn (@word.rep 32 word)
                                              (Init.Nat.min (S (S (S (S (S O)))))
                                                 (Z.to_nat
                                                    (@word.unsigned 32 word
                                                       (@word.of_Z 32 word 10))))
                                              (@List.skipn (@word.rep 32 word)
                                                 (Z.to_nat
                                                    (Z.div
                                                       (@word.unsigned 32 word
                                                          (@word.of_Z 32 word (Z.mul 2 4)))
                                                       4)) ws)) hole))) R)
                               (@sep (@word.rep 32 word) Init.Byte.byte mem
                                  (@array 32 word Init.Byte.byte mem
                                     (@word.rep 32 word) (@Scalars.scalar 32 word mem)
                                     (@word.of_Z 32 word 4) addr
                                     (@Datatypes.app (@word.rep 32 word)
                                        (@List.firstn (@word.rep 32 word)
                                           (S (S (S (S (S (S (S O))))))) ws)
                                        (@Datatypes.app (@word.rep 32 word)
                                           (@List.firstn (@word.rep 32 word)
                                              (Init.Nat.sub
                                                 (@length (@word.rep 32 word) ws)
                                                 (S (S (S (S (S (S (S O))))))))
                                              (@cons (@word.rep 32 word)
                                                 (@word.mul 32 word
                                                    (@List.nth
                                                       (@word.rep 32 word)
                                                       (S (S (S (S (S (S (S O))))))) ws
                                                       (@default
                                                          (@word.rep 32 word)
                                                          (@word_inhabited 32 word)))
                                                    (@word.of_Z 32 word 2))
                                                 (@nil (@word.rep 32 word))))
                                           (@List.skipn (@word.rep 32 word)
                                              (Init.Nat.add
                                                 (@length (@word.rep 32 word)
                                                    (@cons (@word.rep 32 word)
                                                       (@word.mul 32 word
                                                          (@List.nth
                                                             (@word.rep 32 word)
                                                             (S (S (S (S (S (S (S O)))))))
                                                             ws
                                                             (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                          (@word.of_Z 32 word 2))
                                                       (@nil (@word.rep 32 word))))
                                                 (S (S (S (S (S (S (S O)))))))) ws)))) R)))
                           ((@rew_zoom_bw _
                               (Init.Nat.min
                                  (Z.to_nat
                                     (@word.unsigned 32 word (@word.of_Z 32 word 10)))
                                  (@length (@word.rep 32 word)
                                     (@List.skipn (@word.rep 32 word)
                                        (Z.to_nat
                                           (Z.div
                                              (@word.unsigned 32 word
                                                 (@word.sub 32 word
                                                    (@word.add 32 word addr
                                                       (@word.of_Z 32 word (Z.mul 2 4)))
                                                    addr)) 4)) ws))) _
                               (l_firstn_length _ _ _)
                               (fun hole =>
                                @iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem)
                                  (@sep (@word.rep 32 word) Init.Byte.byte mem
                                     (@array 32 word Init.Byte.byte mem
                                        (@word.rep 32 word) (@Scalars.scalar 32 word mem)
                                        (@word.of_Z 32 word 4) addr
                                        (@Datatypes.app (@word.rep 32 word)
                                           (@List.firstn (@word.rep 32 word)
                                              (Z.to_nat
                                                 (Z.div
                                                    (@word.unsigned 32 word
                                                       (@word.of_Z 32 word (Z.mul 2 4))) 4))
                                              ws)
                                           (@Datatypes.app (@word.rep 32 word)
                                              (@List.firstn (@word.rep 32 word)
                                                 (Init.Nat.min
                                                    (S (S (S (S (S O)))))
                                                    (Z.to_nat
                                                       (@word.unsigned 32 word
                                                          (@word.of_Z 32 word 10))))
                                                 (@List.skipn (@word.rep 32 word)
                                                    (Z.to_nat
                                                       (Z.div
                                                          (@word.unsigned 32 word
                                                             (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                              (@Datatypes.app (@word.rep 32 word)
                                                 (@List.firstn
                                                    (@word.rep 32 word)
                                                    (Init.Nat.sub hole
                                                       (S (S (S (S (S O))))))
                                                    (@cons (@word.rep 32 word)
                                                       (@word.mul 32 word
                                                          (@List.nth
                                                             (@word.rep 32 word)
                                                             (S (S (S (S (S O)))))
                                                             (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                                             (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                          (@word.of_Z 32 word 2))
                                                       (@nil (@word.rep 32 word))))
                                                 (@Datatypes.app
                                                    (@word.rep 32 word)
                                                    (@List.skipn
                                                       (@word.rep 32 word)
                                                       (Init.Nat.add
                                                          (@length
                                                             (@word.rep 32 word)
                                                             (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S O)))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                          (S (S (S (S (S O))))))
                                                       (@List.firstn
                                                          (@word.rep 32 word)
                                                          (Z.to_nat
                                                             (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                          (@List.skipn
                                                             (@word.rep 32 word)
                                                             (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws)))
                                                    (@List.skipn
                                                       (@word.rep 32 word)
                                                       (Init.Nat.add
                                                          (Z.to_nat
                                                             (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4))
                                                          (Z.to_nat
                                                             (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))) ws))))))
                                     R)
                                  (@sep (@word.rep 32 word) Init.Byte.byte mem
                                     (@array 32 word Init.Byte.byte mem
                                        (@word.rep 32 word) (@Scalars.scalar 32 word mem)
                                        (@word.of_Z 32 word 4) addr
                                        (@Datatypes.app (@word.rep 32 word)
                                           (@List.firstn (@word.rep 32 word)
                                              (S (S (S (S (S (S (S O))))))) ws)
                                           (@Datatypes.app (@word.rep 32 word)
                                              (@List.firstn (@word.rep 32 word)
                                                 (Init.Nat.sub
                                                    (@length (@word.rep 32 word) ws)
                                                    (S (S (S (S (S (S (S O))))))))
                                                 (@cons (@word.rep 32 word)
                                                    (@word.mul 32 word
                                                       (@List.nth
                                                          (@word.rep 32 word)
                                                          (S (S (S (S (S (S (S O))))))) ws
                                                          (@default
                                                             (@word.rep 32 word)
                                                             (@word_inhabited 32 word)))
                                                       (@word.of_Z 32 word 2))
                                                    (@nil (@word.rep 32 word))))
                                              (@List.skipn (@word.rep 32 word)
                                                 (Init.Nat.add
                                                    (@length (@word.rep 32 word)
                                                       (@cons (@word.rep 32 word)
                                                          (@word.mul 32 word
                                                             (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                             (@word.of_Z 32 word 2))
                                                          (@nil (@word.rep 32 word))))
                                                    (S (S (S (S (S (S (S O)))))))) ws)))) R)))
                              ((@rew_zoom_bw _
                                  (Init.Nat.sub (@length (@word.rep 32 word) ws)
                                     (Z.to_nat
                                        (Z.div
                                           (@word.unsigned 32 word
                                              (@word.sub 32 word
                                                 (@word.add 32 word addr
                                                    (@word.of_Z 32 word (Z.mul 2 4))) addr))
                                           4))) _ (l_skipn_length _ _ _)
                                  (fun hole =>
                                   @iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem)
                                     (@sep (@word.rep 32 word) Init.Byte.byte mem
                                        (@array 32 word Init.Byte.byte mem
                                           (@word.rep 32 word)
                                           (@Scalars.scalar 32 word mem)
                                           (@word.of_Z 32 word 4) addr
                                           (@Datatypes.app (@word.rep 32 word)
                                              (@List.firstn (@word.rep 32 word)
                                                 (Z.to_nat
                                                    (Z.div
                                                       (@word.unsigned 32 word
                                                          (@word.of_Z 32 word (Z.mul 2 4)))
                                                       4)) ws)
                                              (@Datatypes.app (@word.rep 32 word)
                                                 (@List.firstn
                                                    (@word.rep 32 word)
                                                    (Init.Nat.min
                                                       (S (S (S (S (S O)))))
                                                       (Z.to_nat
                                                          (@word.unsigned 32 word
                                                             (@word.of_Z 32 word 10))))
                                                    (@List.skipn
                                                       (@word.rep 32 word)
                                                       (Z.to_nat
                                                          (Z.div
                                                             (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                 (@Datatypes.app
                                                    (@word.rep 32 word)
                                                    (@List.firstn
                                                       (@word.rep 32 word)
                                                       (Init.Nat.sub
                                                          (Init.Nat.min
                                                             (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                             hole)
                                                          (S (S (S (S (S O))))))
                                                       (@cons (@word.rep 32 word)
                                                          (@word.mul 32 word
                                                             (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S O)))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                             (@word.of_Z 32 word 2))
                                                          (@nil (@word.rep 32 word))))
                                                    (@Datatypes.app
                                                       (@word.rep 32 word)
                                                       (@List.skipn
                                                          (@word.rep 32 word)
                                                          (Init.Nat.add
                                                             (@length
                                                              (@word.rep 32 word)
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S O)))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                             (S (S (S (S (S O))))))
                                                          (@List.firstn
                                                             (@word.rep 32 word)
                                                             (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                             (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws)))
                                                       (@List.skipn
                                                          (@word.rep 32 word)
                                                          (Init.Nat.add
                                                             (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4))
                                                             (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))) ws))))))
                                        R)
                                     (@sep (@word.rep 32 word) Init.Byte.byte mem
                                        (@array 32 word Init.Byte.byte mem
                                           (@word.rep 32 word)
                                           (@Scalars.scalar 32 word mem)
                                           (@word.of_Z 32 word 4) addr
                                           (@Datatypes.app (@word.rep 32 word)
                                              (@List.firstn (@word.rep 32 word)
                                                 (S (S (S (S (S (S (S O))))))) ws)
                                              (@Datatypes.app (@word.rep 32 word)
                                                 (@List.firstn
                                                    (@word.rep 32 word)
                                                    (Init.Nat.sub
                                                       (@length (@word.rep 32 word) ws)
                                                       (S (S (S (S (S (S (S O))))))))
                                                    (@cons (@word.rep 32 word)
                                                       (@word.mul 32 word
                                                          (@List.nth
                                                             (@word.rep 32 word)
                                                             (S (S (S (S (S (S (S O)))))))
                                                             ws
                                                             (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                          (@word.of_Z 32 word 2))
                                                       (@nil (@word.rep 32 word))))
                                                 (@List.skipn (@word.rep 32 word)
                                                    (Init.Nat.add
                                                       (@length
                                                          (@word.rep 32 word)
                                                          (@cons
                                                             (@word.rep 32 word)
                                                             (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                             (@nil (@word.rep 32 word))))
                                                       (S (S (S (S (S (S (S O)))))))) ws))))
                                        R)))
                                 ((@rew_zoom_bw _
                                     (@word.add 32 word
                                        (@word.add 32 word addr
                                           (@word.of_Z 32 word (Z.mul 2 4)))
                                        (@word.opp 32 word addr)) _
                                     (wsub_def _ _)
                                     (fun hole =>
                                      @iff1
                                        (@map.rep (@word.rep 32 word) Init.Byte.byte mem)
                                        (@sep (@word.rep 32 word) Init.Byte.byte mem
                                           (@array 32 word Init.Byte.byte mem
                                              (@word.rep 32 word)
                                              (@Scalars.scalar 32 word mem)
                                              (@word.of_Z 32 word 4) addr
                                              (@Datatypes.app (@word.rep 32 word)
                                                 (@List.firstn
                                                    (@word.rep 32 word)
                                                    (Z.to_nat
                                                       (Z.div
                                                          (@word.unsigned 32 word
                                                             (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws)
                                                 (@Datatypes.app
                                                    (@word.rep 32 word)
                                                    (@List.firstn
                                                       (@word.rep 32 word)
                                                       (Init.Nat.min
                                                          (S (S (S (S (S O)))))
                                                          (Z.to_nat
                                                             (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10))))
                                                       (@List.skipn
                                                          (@word.rep 32 word)
                                                          (Z.to_nat
                                                             (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                    (@Datatypes.app
                                                       (@word.rep 32 word)
                                                       (@List.firstn
                                                          (@word.rep 32 word)
                                                          (Init.Nat.sub
                                                             (Init.Nat.min
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word hole)
                                                              4))))
                                                             (S (S (S (S (S O))))))
                                                          (@cons
                                                             (@word.rep 32 word)
                                                             (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S O)))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                             (@nil (@word.rep 32 word))))
                                                       (@Datatypes.app
                                                          (@word.rep 32 word)
                                                          (@List.skipn
                                                             (@word.rep 32 word)
                                                             (Init.Nat.add
                                                              (@length
                                                              (@word.rep 32 word)
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S O)))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (S (S (S (S (S O))))))
                                                             (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws)))
                                                          (@List.skipn
                                                             (@word.rep 32 word)
                                                             (Init.Nat.add
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))) ws))))))
                                           R)
                                        (@sep (@word.rep 32 word) Init.Byte.byte mem
                                           (@array 32 word Init.Byte.byte mem
                                              (@word.rep 32 word)
                                              (@Scalars.scalar 32 word mem)
                                              (@word.of_Z 32 word 4) addr
                                              (@Datatypes.app (@word.rep 32 word)
                                                 (@List.firstn
                                                    (@word.rep 32 word)
                                                    (S (S (S (S (S (S (S O))))))) ws)
                                                 (@Datatypes.app
                                                    (@word.rep 32 word)
                                                    (@List.firstn
                                                       (@word.rep 32 word)
                                                       (Init.Nat.sub
                                                          (@length (@word.rep 32 word) ws)
                                                          (S (S (S (S (S (S (S O))))))))
                                                       (@cons (@word.rep 32 word)
                                                          (@word.mul 32 word
                                                             (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                             (@word.of_Z 32 word 2))
                                                          (@nil (@word.rep 32 word))))
                                                    (@List.skipn
                                                       (@word.rep 32 word)
                                                       (Init.Nat.add
                                                          (@length
                                                             (@word.rep 32 word)
                                                             (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                          (S (S (S (S (S (S (S O)))))))) ws))))
                                           R)))
                                    ((@rew_zoom_bw _
                                        (@word.add 32 word addr
                                           (@word.add 32 word
                                              (@word.of_Z 32 word (Z.mul 2 4))
                                              (@word.opp 32 word addr))) _
                                        (wadd_to_right_assoc _ _ _)
                                        (fun hole =>
                                         @iff1
                                           (@map.rep (@word.rep 32 word) Init.Byte.byte mem)
                                           (@sep (@word.rep 32 word) Init.Byte.byte mem
                                              (@array 32 word Init.Byte.byte mem
                                                 (@word.rep 32 word)
                                                 (@Scalars.scalar 32 word mem)
                                                 (@word.of_Z 32 word 4) addr
                                                 (@Datatypes.app
                                                    (@word.rep 32 word)
                                                    (@List.firstn
                                                       (@word.rep 32 word)
                                                       (Z.to_nat
                                                          (Z.div
                                                             (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws)
                                                    (@Datatypes.app
                                                       (@word.rep 32 word)
                                                       (@List.firstn
                                                          (@word.rep 32 word)
                                                          (Init.Nat.min
                                                             (S (S (S (S (S O)))))
                                                             (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10))))
                                                          (@List.skipn
                                                             (@word.rep 32 word)
                                                             (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                       (@Datatypes.app
                                                          (@word.rep 32 word)
                                                          (@List.firstn
                                                             (@word.rep 32 word)
                                                             (Init.Nat.sub
                                                              (Init.Nat.min
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word hole)
                                                              4))))
                                                              (S (S (S (S (S O))))))
                                                             (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S O)))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                          (@Datatypes.app
                                                             (@word.rep 32 word)
                                                             (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (@length
                                                              (@word.rep 32 word)
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S O)))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (S (S (S (S (S O))))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws)))
                                                             (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))) ws))))))
                                              R)
                                           (@sep (@word.rep 32 word) Init.Byte.byte mem
                                              (@array 32 word Init.Byte.byte mem
                                                 (@word.rep 32 word)
                                                 (@Scalars.scalar 32 word mem)
                                                 (@word.of_Z 32 word 4) addr
                                                 (@Datatypes.app
                                                    (@word.rep 32 word)
                                                    (@List.firstn
                                                       (@word.rep 32 word)
                                                       (S (S (S (S (S (S (S O))))))) ws)
                                                    (@Datatypes.app
                                                       (@word.rep 32 word)
                                                       (@List.firstn
                                                          (@word.rep 32 word)
                                                          (Init.Nat.sub
                                                             (@length
                                                              (@word.rep 32 word) ws)
                                                             (S (S (S (S (S (S (S O))))))))
                                                          (@cons
                                                             (@word.rep 32 word)
                                                             (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                             (@nil (@word.rep 32 word))))
                                                       (@List.skipn
                                                          (@word.rep 32 word)
                                                          (Init.Nat.add
                                                             (@length
                                                              (@word.rep 32 word)
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                             (S (S (S (S (S (S (S O))))))))
                                                          ws)))) R)))
                                       ((@rew_zoom_bw _ (@word.of_Z 32 word (Z.mul 2 4)) _
                                           (wadd_opp_r_distant _ _)
                                           (fun hole =>
                                            @iff1
                                              (@map.rep (@word.rep 32 word) Init.Byte.byte
                                                 mem)
                                              (@sep (@word.rep 32 word) Init.Byte.byte mem
                                                 (@array 32 word Init.Byte.byte mem
                                                    (@word.rep 32 word)
                                                    (@Scalars.scalar 32 word mem)
                                                    (@word.of_Z 32 word 4) addr
                                                    (@Datatypes.app
                                                       (@word.rep 32 word)
                                                       (@List.firstn
                                                          (@word.rep 32 word)
                                                          (Z.to_nat
                                                             (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws)
                                                       (@Datatypes.app
                                                          (@word.rep 32 word)
                                                          (@List.firstn
                                                             (@word.rep 32 word)
                                                             (Init.Nat.min
                                                              (S (S (S (S (S O)))))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10))))
                                                             (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                          (@Datatypes.app
                                                             (@word.rep 32 word)
                                                             (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (Init.Nat.min
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word hole)
                                                              4))))
                                                              (S (S (S (S (S O))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S O)))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                             (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (@length
                                                              (@word.rep 32 word)
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S O)))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (S (S (S (S (S O))))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))) ws))))))
                                                 R)
                                              (@sep (@word.rep 32 word) Init.Byte.byte mem
                                                 (@array 32 word Init.Byte.byte mem
                                                    (@word.rep 32 word)
                                                    (@Scalars.scalar 32 word mem)
                                                    (@word.of_Z 32 word 4) addr
                                                    (@Datatypes.app
                                                       (@word.rep 32 word)
                                                       (@List.firstn
                                                          (@word.rep 32 word)
                                                          (S (S (S (S (S (S (S O))))))) ws)
                                                       (@Datatypes.app
                                                          (@word.rep 32 word)
                                                          (@List.firstn
                                                             (@word.rep 32 word)
                                                             (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (S (S (S (S (S (S (S O))))))))
                                                             (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                          (@List.skipn
                                                             (@word.rep 32 word)
                                                             (Init.Nat.add
                                                              (@length
                                                              (@word.rep 32 word)
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (S (S (S (S (S (S (S O))))))))
                                                             ws)))) R)))
                                          ((@rew_zoom_bw _
                                              (@word.add 32 word
                                                 (@word.add 32 word addr
                                                    (@word.of_Z 32 word (Z.mul 2 4)))
                                                 (@word.opp 32 word addr)) _
                                              (wsub_def _ _)
                                              (fun hole =>
                                               @iff1
                                                 (@map.rep (@word.rep 32 word)
                                                    Init.Byte.byte mem)
                                                 (@sep (@word.rep 32 word) Init.Byte.byte
                                                    mem
                                                    (@array 32 word Init.Byte.byte mem
                                                       (@word.rep 32 word)
                                                       (@Scalars.scalar 32 word mem)
                                                       (@word.of_Z 32 word 4) addr
                                                       (@Datatypes.app
                                                          (@word.rep 32 word)
                                                          (@List.firstn
                                                             (@word.rep 32 word)
                                                             (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws)
                                                          (@Datatypes.app
                                                             (@word.rep 32 word)
                                                             (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.min
                                                              (S (S (S (S (S O)))))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10))))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                             (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (Init.Nat.min
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4))))
                                                              (S (S (S (S (S O))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S O)))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word hole)
                                                              4)) ws))
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (@length
                                                              (@word.rep 32 word)
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S O)))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (S (S (S (S (S O))))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))) ws))))))
                                                    R)
                                                 (@sep (@word.rep 32 word) Init.Byte.byte
                                                    mem
                                                    (@array 32 word Init.Byte.byte mem
                                                       (@word.rep 32 word)
                                                       (@Scalars.scalar 32 word mem)
                                                       (@word.of_Z 32 word 4) addr
                                                       (@Datatypes.app
                                                          (@word.rep 32 word)
                                                          (@List.firstn
                                                             (@word.rep 32 word)
                                                             (S (S (S (S (S (S (S O)))))))
                                                             ws)
                                                          (@Datatypes.app
                                                             (@word.rep 32 word)
                                                             (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (S (S (S (S (S (S (S O))))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                             (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (@length
                                                              (@word.rep 32 word)
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (S (S (S (S (S (S (S O))))))))
                                                              ws)))) R)))
                                             ((@rew_zoom_bw _
                                                 (@word.add 32 word addr
                                                    (@word.add 32 word
                                                       (@word.of_Z 32 word (Z.mul 2 4))
                                                       (@word.opp 32 word addr))) _
                                                 (wadd_to_right_assoc _ _ _)
                                                 (fun hole =>
                                                  @iff1
                                                    (@map.rep (@word.rep 32 word)
                                                       Init.Byte.byte mem)
                                                    (@sep (@word.rep 32 word)
                                                       Init.Byte.byte mem
                                                       (@array 32 word Init.Byte.byte mem
                                                          (@word.rep 32 word)
                                                          (@Scalars.scalar 32 word mem)
                                                          (@word.of_Z 32 word 4) addr
                                                          (@Datatypes.app
                                                             (@word.rep 32 word)
                                                             (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws)
                                                             (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.min
                                                              (S (S (S (S (S O)))))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10))))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (Init.Nat.min
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4))))
                                                              (S (S (S (S (S O))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S O)))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word hole)
                                                              4)) ws))
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (@length
                                                              (@word.rep 32 word)
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S O)))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (S (S (S (S (S O))))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))) ws))))))
                                                       R)
                                                    (@sep (@word.rep 32 word)
                                                       Init.Byte.byte mem
                                                       (@array 32 word Init.Byte.byte mem
                                                          (@word.rep 32 word)
                                                          (@Scalars.scalar 32 word mem)
                                                          (@word.of_Z 32 word 4) addr
                                                          (@Datatypes.app
                                                             (@word.rep 32 word)
                                                             (@List.firstn
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws)
                                                             (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (S (S (S (S (S (S (S O))))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (@length
                                                              (@word.rep 32 word)
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (S (S (S (S (S (S (S O))))))))
                                                              ws)))) R)))
                                                ((@rew_zoom_bw _
                                                    (@word.of_Z 32 word (Z.mul 2 4)) _
                                                    (wadd_opp_r_distant _ _)
                                                    (fun hole =>
                                                     @iff1
                                                       (@map.rep
                                                          (@word.rep 32 word)
                                                          Init.Byte.byte mem)
                                                       (@sep (@word.rep 32 word)
                                                          Init.Byte.byte mem
                                                          (@array 32 word Init.Byte.byte
                                                             mem
                                                             (@word.rep 32 word)
                                                             (@Scalars.scalar 32 word mem)
                                                             (@word.of_Z 32 word 4) addr
                                                             (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws)
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.min
                                                              (S (S (S (S (S O)))))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10))))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (Init.Nat.min
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4))))
                                                              (S (S (S (S (S O))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S O)))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word hole)
                                                              4)) ws))
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (@length
                                                              (@word.rep 32 word)
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S O)))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws))
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (S (S (S (S (S O))))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))) ws))))))
                                                          R)
                                                       (@sep (@word.rep 32 word)
                                                          Init.Byte.byte mem
                                                          (@array 32 word Init.Byte.byte
                                                             mem
                                                             (@word.rep 32 word)
                                                             (@Scalars.scalar 32 word mem)
                                                             (@word.of_Z 32 word 4) addr
                                                             (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws)
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (S (S (S (S (S (S (S O))))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (@length
                                                              (@word.rep 32 word)
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (S (S (S (S (S (S (S O))))))))
                                                              ws)))) R)))
                                                   ((@rew_zoom_bw _
                                                       (S
                                                          (@length
                                                             (@word.rep 32 word)
                                                             (@nil (@word.rep 32 word)))) _
                                                       (l_length_cons _ _ _)
                                                       (fun hole =>
                                                        @iff1
                                                          (@map.rep
                                                             (@word.rep 32 word)
                                                             Init.Byte.byte mem)
                                                          (@sep
                                                             (@word.rep 32 word)
                                                             Init.Byte.byte mem
                                                             (@array 32 word Init.Byte.byte
                                                              mem
                                                              (@word.rep 32 word)
                                                              (@Scalars.scalar 32 word mem)
                                                              (@word.of_Z 32 word 4) addr
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws)
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.min
                                                              (S (S (S (S (S O)))))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10))))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (Init.Nat.min
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4))))
                                                              (S (S (S (S (S O))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S O)))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add hole
                                                              (S (S (S (S (S O))))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))) ws))))))
                                                             R)
                                                          (@sep
                                                             (@word.rep 32 word)
                                                             Init.Byte.byte mem
                                                             (@array 32 word Init.Byte.byte
                                                              mem
                                                              (@word.rep 32 word)
                                                              (@Scalars.scalar 32 word mem)
                                                              (@word.of_Z 32 word 4) addr
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws)
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (S (S (S (S (S (S (S O))))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (@length
                                                              (@word.rep 32 word)
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (S (S (S (S (S (S (S O))))))))
                                                              ws)))) R)))
                                                      ((@rew_zoom_bw _ O _
                                                          (l_length_nil _)
                                                          (fun hole =>
                                                           @iff1
                                                             (@map.rep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem)
                                                             (@sep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem
                                                              (@array 32 word
                                                              Init.Byte.byte mem
                                                              (@word.rep 32 word)
                                                              (@Scalars.scalar 32 word mem)
                                                              (@word.of_Z 32 word 4) addr
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws)
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.min
                                                              (S (S (S (S (S O)))))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10))))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (Init.Nat.min
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4))))
                                                              (S (S (S (S (S O))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S O)))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (S hole)
                                                              (S (S (S (S (S O))))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4)) ws)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))) ws))))))
                                                              R)
                                                             (@sep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem
                                                              (@array 32 word
                                                              Init.Byte.byte mem
                                                              (@word.rep 32 word)
                                                              (@Scalars.scalar 32 word mem)
                                                              (@word.of_Z 32 word 4) addr
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws)
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (S (S (S (S (S (S (S O))))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (@length
                                                              (@word.rep 32 word)
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (S (S (S (S (S (S (S O))))))))
                                                              ws)))) R)))
                                                         ((@rew_zoom_bw _
                                                             (@word.add 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4)))
                                                              (@word.opp 32 word addr)) _
                                                             (wsub_def _ _)
                                                             (fun hole =>
                                                              @iff1
                                                              (@map.rep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem)
                                                              (@sep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem
                                                              (@array 32 word
                                                              Init.Byte.byte mem
                                                              (@word.rep 32 word)
                                                              (@Scalars.scalar 32 word mem)
                                                              (@word.of_Z 32 word 4) addr
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws)
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.min
                                                              (S (S (S (S (S O)))))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10))))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (Init.Nat.min
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4))))
                                                              (S (S (S (S (S O))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S O)))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (S O)
                                                              (S (S (S (S (S O))))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word hole)
                                                              4)) ws)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))) ws))))))
                                                              R)
                                                              (@sep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem
                                                              (@array 32 word
                                                              Init.Byte.byte mem
                                                              (@word.rep 32 word)
                                                              (@Scalars.scalar 32 word mem)
                                                              (@word.of_Z 32 word 4) addr
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws)
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (S (S (S (S (S (S (S O))))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (@length
                                                              (@word.rep 32 word)
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (S (S (S (S (S (S (S O))))))))
                                                              ws)))) R)))
                                                            ((@rew_zoom_bw _
                                                              (@word.add 32 word addr
                                                              (@word.add 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))
                                                              (@word.opp 32 word addr))) _
                                                              (wadd_to_right_assoc _ _ _)
                                                              (fun hole =>
                                                              @iff1
                                                              (@map.rep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem)
                                                              (@sep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem
                                                              (@array 32 word
                                                              Init.Byte.byte mem
                                                              (@word.rep 32 word)
                                                              (@Scalars.scalar 32 word mem)
                                                              (@word.of_Z 32 word 4) addr
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws)
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.min
                                                              (S (S (S (S (S O)))))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10))))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (Init.Nat.min
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4))))
                                                              (S (S (S (S (S O))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S O)))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (S O)
                                                              (S (S (S (S (S O))))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word hole)
                                                              4)) ws)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))) ws))))))
                                                              R)
                                                              (@sep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem
                                                              (@array 32 word
                                                              Init.Byte.byte mem
                                                              (@word.rep 32 word)
                                                              (@Scalars.scalar 32 word mem)
                                                              (@word.of_Z 32 word 4) addr
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws)
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (S (S (S (S (S (S (S O))))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (@length
                                                              (@word.rep 32 word)
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (S (S (S (S (S (S (S O))))))))
                                                              ws)))) R)))
                                                              ((@rew_zoom_bw _
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4)) _
                                                              (wadd_opp_r_distant _ _)
                                                              (fun hole =>
                                                              @iff1
                                                              (@map.rep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem)
                                                              (@sep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem
                                                              (@array 32 word
                                                              Init.Byte.byte mem
                                                              (@word.rep 32 word)
                                                              (@Scalars.scalar 32 word mem)
                                                              (@word.of_Z 32 word 4) addr
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws)
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.min
                                                              (S (S (S (S (S O)))))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10))))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (Init.Nat.min
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4))))
                                                              (S (S (S (S (S O))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S O)))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (S O)
                                                              (S (S (S (S (S O))))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word hole)
                                                              4)) ws)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.sub 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) addr)) 4))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))) ws))))))
                                                              R)
                                                              (@sep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem
                                                              (@array 32 word
                                                              Init.Byte.byte mem
                                                              (@word.rep 32 word)
                                                              (@Scalars.scalar 32 word mem)
                                                              (@word.of_Z 32 word 4) addr
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws)
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (S (S (S (S (S (S (S O))))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (@length
                                                              (@word.rep 32 word)
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (S (S (S (S (S (S (S O))))))))
                                                              ws)))) R)))
                                                              ((@rew_zoom_bw _
                                                              (@word.add 32 word
                                                              (@word.add 32 word addr
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4)))
                                                              (@word.opp 32 word addr)) _
                                                              (wsub_def _ _)
                                                              (fun hole =>
                                                              @iff1
                                                              (@map.rep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem)
                                                              (@sep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem
                                                              (@array 32 word
                                                              Init.Byte.byte mem
                                                              (@word.rep 32 word)
                                                              (@Scalars.scalar 32 word mem)
                                                              (@word.of_Z 32 word 4) addr
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws)
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.min
                                                              (S (S (S (S (S O)))))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10))))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (Init.Nat.min
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4))))
                                                              (S (S (S (S (S O))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S O)))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (S O)
                                                              (S (S (S (S (S O))))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word hole)
                                                              4))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))) ws))))))
                                                              R)
                                                              (@sep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem
                                                              (@array 32 word
                                                              Init.Byte.byte mem
                                                              (@word.rep 32 word)
                                                              (@Scalars.scalar 32 word mem)
                                                              (@word.of_Z 32 word 4) addr
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws)
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (S (S (S (S (S (S (S O))))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (@length
                                                              (@word.rep 32 word)
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (S (S (S (S (S (S (S O))))))))
                                                              ws)))) R)))
                                                              ((@rew_zoom_bw _
                                                              (@word.add 32 word addr
                                                              (@word.add 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))
                                                              (@word.opp 32 word addr))) _
                                                              (wadd_to_right_assoc _ _ _)
                                                              (fun hole =>
                                                              @iff1
                                                              (@map.rep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem)
                                                              (@sep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem
                                                              (@array 32 word
                                                              Init.Byte.byte mem
                                                              (@word.rep 32 word)
                                                              (@Scalars.scalar 32 word mem)
                                                              (@word.of_Z 32 word 4) addr
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws)
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.min
                                                              (S (S (S (S (S O)))))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10))))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (Init.Nat.min
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4))))
                                                              (S (S (S (S (S O))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S O)))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (S O)
                                                              (S (S (S (S (S O))))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word hole)
                                                              4))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))) ws))))))
                                                              R)
                                                              (@sep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem
                                                              (@array 32 word
                                                              Init.Byte.byte mem
                                                              (@word.rep 32 word)
                                                              (@Scalars.scalar 32 word mem)
                                                              (@word.of_Z 32 word 4) addr
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws)
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (S (S (S (S (S (S (S O))))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (@length
                                                              (@word.rep 32 word)
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (S (S (S (S (S (S (S O))))))))
                                                              ws)))) R)))
                                                              ((@rew_zoom_bw _
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4)) _
                                                              (wadd_opp_r_distant _ _)
                                                              (fun hole =>
                                                              @iff1
                                                              (@map.rep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem)
                                                              (@sep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem
                                                              (@array 32 word
                                                              Init.Byte.byte mem
                                                              (@word.rep 32 word)
                                                              (@Scalars.scalar 32 word mem)
                                                              (@word.of_Z 32 word 4) addr
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws)
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.min
                                                              (S (S (S (S (S O)))))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10))))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (Init.Nat.min
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4))))
                                                              (S (S (S (S (S O))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S O)))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (S O)
                                                              (S (S (S (S (S O))))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word hole)
                                                              4))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))) ws))))))
                                                              R)
                                                              (@sep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem
                                                              (@array 32 word
                                                              Init.Byte.byte mem
                                                              (@word.rep 32 word)
                                                              (@Scalars.scalar 32 word mem)
                                                              (@word.of_Z 32 word 4) addr
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws)
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (S (S (S (S (S (S (S O))))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (@length
                                                              (@word.rep 32 word)
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (S (S (S (S (S (S (S O))))))))
                                                              ws)))) R)))
                                                              ((@rew_zoom_bw _
                                                              (S
                                                              (@length
                                                              (@word.rep 32 word)
                                                              (@nil (@word.rep 32 word))))
                                                              _ (l_length_cons _ _ _)
                                                              (fun hole =>
                                                              @iff1
                                                              (@map.rep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem)
                                                              (@sep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem
                                                              (@array 32 word
                                                              Init.Byte.byte mem
                                                              (@word.rep 32 word)
                                                              (@Scalars.scalar 32 word mem)
                                                              (@word.of_Z 32 word 4) addr
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws)
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.min
                                                              (S (S (S (S (S O)))))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10))))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (Init.Nat.min
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4))))
                                                              (S (S (S (S (S O))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S O)))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (S O)
                                                              (S (S (S (S (S O))))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))) ws))))))
                                                              R)
                                                              (@sep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem
                                                              (@array 32 word
                                                              Init.Byte.byte mem
                                                              (@word.rep 32 word)
                                                              (@Scalars.scalar 32 word mem)
                                                              (@word.of_Z 32 word 4) addr
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws)
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (S (S (S (S (S (S (S O))))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add hole
                                                              (S (S (S (S (S (S (S O))))))))
                                                              ws)))) R)))
                                                              ((@rew_zoom_bw _ O _
                                                              (l_length_nil _)
                                                              (fun hole =>
                                                              @iff1
                                                              (@map.rep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem)
                                                              (@sep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem
                                                              (@array 32 word
                                                              Init.Byte.byte mem
                                                              (@word.rep 32 word)
                                                              (@Scalars.scalar 32 word mem)
                                                              (@word.of_Z 32 word 4) addr
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws)
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.min
                                                              (S (S (S (S (S O)))))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10))))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (Init.Nat.min
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4))))
                                                              (S (S (S (S (S O))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S O)))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws))
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (S O)
                                                              (S (S (S (S (S O))))))
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4)) ws)))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (Z.to_nat
                                                              (Z.div
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word
                                                              (Z.mul 2 4))) 4))
                                                              (Z.to_nat
                                                              (@word.unsigned 32 word
                                                              (@word.of_Z 32 word 10)))) ws))))))
                                                              R)
                                                              (@sep
                                                              (@word.rep 32 word)
                                                              Init.Byte.byte mem
                                                              (@array 32 word
                                                              Init.Byte.byte mem
                                                              (@word.rep 32 word)
                                                              (@Scalars.scalar 32 word mem)
                                                              (@word.of_Z 32 word 4) addr
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws)
                                                              (@Datatypes.app
                                                              (@word.rep 32 word)
                                                              (@List.firstn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.sub
                                                              (@length
                                                              (@word.rep 32 word) ws)
                                                              (S (S (S (S (S (S (S O))))))))
                                                              (@cons
                                                              (@word.rep 32 word)
                                                              (@word.mul 32 word
                                                              (@List.nth
                                                              (@word.rep 32 word)
                                                              (S (S (S (S (S (S (S O)))))))
                                                              ws
                                                              (@default
                                                              (@word.rep 32 word)
                                                              (@word_inhabited 32 word)))
                                                              (@word.of_Z 32 word 2))
                                                              (@nil (@word.rep 32 word))))
                                                              (@List.skipn
                                                              (@word.rep 32 word)
                                                              (Init.Nat.add
                                                              (S hole)
                                                              (S (S (S (S (S (S (S O))))))))
                                                              ws)))) R))) _))))))))))))))))))))))))))))
in
time "typechecking" (let tp := type of t in idtac)).

    case TODO.
    Time Qed.

    (*
    Time refine (printed proof) takes 0.244 secs.

    Set Printing Depth 1000000.
    Set Printing All.
    Set Egg Log Proofs.
    Time egg_step 3.
    *)

    repeat WordSimpl.word_simpl_step_in_goal.

    Time egg_step 3.

Ltac t := (unfold List.upd, List.upds;
       list_length_rewrites_without_sideconds_in_goal;
       ZnWords).

Print Rewrite HintDb fwd_rewrites.

rewrite List.skipn_eq_O by t.
rewrite Nat.min_l by t.
rewrite Nat.min_r by t.



(* Hints from SepAutoArray.v: *)
rewrite List.firstn_all2 by t.
rewrite List.skipn_all2 by t.
rewrite List.firstn_eq_O by t.
rewrite List.skipn_eq_O by t.
rewrite Nat.min_l by t.
rewrite Nat.min_r by t.



Print Rewrite HintDb fwd_rewrites.

try rewrite_db fwd_rewrites.

    Time egg_step 3.
    Time progress groundcbv.groundcbv_in_goal.


  match goal with



| |- context[@word.mul ?wi ?wo ?x ?y] =>idtac x y; progress (ring_simplify (@word.mul wi wo x y))
end.
  | |- context[word.unsigned (word.of_Z _)] =>
    rewrite word.unsigned_of_Z_nowrap by Lia.lia
  | _ => progress groundcbv_in_goal
  end.

    WordSimpl.word_simpl_step_in_goal.

    rewrite word.unsigned_of_Z_nowrap by lia.

    WordSimpl.word_simpl_step_in_goal.

    Time egg_step 3.


{
*)
    WordSimpl.word_simpl_step_in_goal.
    WordSimpl.word_simpl_step_in_goal.
    WordSimpl.word_simpl_step_in_goal.
    WordSimpl.word_simpl_step_in_goal.
    WordSimpl.word_simpl_step_in_goal.
    WordSimpl.word_simpl_step_in_goal.

  Abort.

  Lemma simplification1_proof2: simplification1.
  Proof.
    unfold simplification1. intros.

    unfold List.upd, List.upds.
    pose_word_lemmas 32%Z word. pose_Prop_lemmas. pose_fwd_list_hints.

    (* Time egg_step 3. *)

(* parsing and applying the proof takes 0.347 secs: *)
Time unshelve (
eapply (@rew_zoom_bw _ (@word.add 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) (@word.opp 32 word addr)) _ (wsub_def _ _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word hole) 4)) ws) (@Datatypes.app (@word.rep 32 word) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))) (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws)))) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S (S (S O)))))))) ws)))) R))));
eapply (@rew_zoom_bw _ (@word.add 32 word addr (@word.add 32 word (@word.of_Z 32 word (Z.mul 2 4)) (@word.opp 32 word addr))) _ (wadd_to_right_assoc _ _ _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word hole) 4)) ws) (@Datatypes.app (@word.rep 32 word) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))) (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws)))) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S (S (S O)))))))) ws)))) R))));
eapply (@rew_zoom_bw _ (@word.of_Z 32 word (Z.mul 2 4)) _ (wadd_opp_r_distant _ _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word hole) 4)) ws) (@Datatypes.app (@word.rep 32 word) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))) (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws)))) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S (S (S O)))))))) ws)))) R))));
eapply (@rew_zoom_bw _ (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))) (@Datatypes.app (@word.rep 32 word) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))) (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws))) _ (l_app_to_right_assoc _ _ _ _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws) hole)) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S (S (S O)))))))) ws)))) R))));
eapply (@rew_zoom_bw _ (@List.firstn (@word.rep 32 word) (Init.Nat.min (S (S (S (S (S O))))) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) _ (l_firstn_firstn _ _ _ _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws) (@Datatypes.app (@word.rep 32 word) hole (@Datatypes.app (@word.rep 32 word) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))) (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws))))) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S (S (S O)))))))) ws)))) R))));
eapply (@rew_zoom_bw _ (@word.add 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) (@word.opp 32 word addr)) _ (wsub_def _ _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.min (S (S (S (S (S O))))) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word hole) 4)) ws)) (@Datatypes.app (@word.rep 32 word) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))) (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws))))) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S (S (S O)))))))) ws)))) R))));
eapply (@rew_zoom_bw _ (@word.add 32 word addr (@word.add 32 word (@word.of_Z 32 word (Z.mul 2 4)) (@word.opp 32 word addr))) _ (wadd_to_right_assoc _ _ _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.min (S (S (S (S (S O))))) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word hole) 4)) ws)) (@Datatypes.app (@word.rep 32 word) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))) (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws))))) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S (S (S O)))))))) ws)))) R))));
eapply (@rew_zoom_bw _ (@word.of_Z 32 word (Z.mul 2 4)) _ (wadd_opp_r_distant _ _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.min (S (S (S (S (S O))))) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word hole) 4)) ws)) (@Datatypes.app (@word.rep 32 word) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))) (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws))))) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S (S (S O)))))))) ws)))) R))));
eapply (@rew_zoom_bw _ (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))) (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@Datatypes.app (@word.rep 32 word) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws))) _ (l_app_to_right_assoc _ _ _ _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.min (S (S (S (S (S O))))) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) hole))) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S (S (S O)))))))) ws)))) R))));
eapply (@rew_zoom_bw _ (Init.Nat.min (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@length (@word.rep 32 word) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))) _ (l_firstn_length _ _ _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.min (S (S (S (S (S O))))) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub hole (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@Datatypes.app (@word.rep 32 word) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws)))))) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S (S (S O)))))))) ws)))) R))));
eapply (@rew_zoom_bw _ (Init.Nat.sub (@length (@word.rep 32 word) ws) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4))) _ (l_skipn_length _ _ _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.min (S (S (S (S (S O))))) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (Init.Nat.min (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) hole) (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@Datatypes.app (@word.rep 32 word) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws)))))) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S (S (S O)))))))) ws)))) R))));
eapply (@rew_zoom_bw _ (@word.add 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) (@word.opp 32 word addr)) _ (wsub_def _ _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.min (S (S (S (S (S O))))) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (Init.Nat.min (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (Init.Nat.sub (@length (@word.rep 32 word) ws) (Z.to_nat (Z.div (@word.unsigned 32 word hole) 4)))) (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@Datatypes.app (@word.rep 32 word) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws)))))) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S (S (S O)))))))) ws)))) R))));
eapply (@rew_zoom_bw _ (@word.add 32 word addr (@word.add 32 word (@word.of_Z 32 word (Z.mul 2 4)) (@word.opp 32 word addr))) _ (wadd_to_right_assoc _ _ _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.min (S (S (S (S (S O))))) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (Init.Nat.min (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (Init.Nat.sub (@length (@word.rep 32 word) ws) (Z.to_nat (Z.div (@word.unsigned 32 word hole) 4)))) (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@Datatypes.app (@word.rep 32 word) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws)))))) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S (S (S O)))))))) ws)))) R))));
eapply (@rew_zoom_bw _ (@word.of_Z 32 word (Z.mul 2 4)) _ (wadd_opp_r_distant _ _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.min (S (S (S (S (S O))))) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (Init.Nat.min (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (Init.Nat.sub (@length (@word.rep 32 word) ws) (Z.to_nat (Z.div (@word.unsigned 32 word hole) 4)))) (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@Datatypes.app (@word.rep 32 word) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws)))))) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S (S (S O)))))))) ws)))) R))));
eapply (@rew_zoom_bw _ (@word.add 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) (@word.opp 32 word addr)) _ (wsub_def _ _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.min (S (S (S (S (S O))))) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (Init.Nat.min (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (Init.Nat.sub (@length (@word.rep 32 word) ws) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)))) (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word hole) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@Datatypes.app (@word.rep 32 word) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws)))))) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S (S (S O)))))))) ws)))) R))));
eapply (@rew_zoom_bw _ (@word.add 32 word addr (@word.add 32 word (@word.of_Z 32 word (Z.mul 2 4)) (@word.opp 32 word addr))) _ (wadd_to_right_assoc _ _ _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.min (S (S (S (S (S O))))) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (Init.Nat.min (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (Init.Nat.sub (@length (@word.rep 32 word) ws) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)))) (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word hole) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@Datatypes.app (@word.rep 32 word) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws)))))) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S (S (S O)))))))) ws)))) R))));
eapply (@rew_zoom_bw _ (@word.of_Z 32 word (Z.mul 2 4)) _ (wadd_opp_r_distant _ _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.min (S (S (S (S (S O))))) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (Init.Nat.min (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (Init.Nat.sub (@length (@word.rep 32 word) ws) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)))) (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word hole) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@Datatypes.app (@word.rep 32 word) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws)))))) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S (S (S O)))))))) ws)))) R))));
eapply (@rew_zoom_bw _ (S (@length (@word.rep 32 word) (@nil (@word.rep 32 word)))) _ (l_length_cons _ _ _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.min (S (S (S (S (S O))))) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (Init.Nat.min (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (Init.Nat.sub (@length (@word.rep 32 word) ws) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)))) (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@Datatypes.app (@word.rep 32 word) (@List.skipn (@word.rep 32 word) (Init.Nat.add hole (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws)))))) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S (S (S O)))))))) ws)))) R))));
eapply (@rew_zoom_bw _ O _ (l_length_nil _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.min (S (S (S (S (S O))))) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (Init.Nat.min (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (Init.Nat.sub (@length (@word.rep 32 word) ws) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)))) (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@Datatypes.app (@word.rep 32 word) (@List.skipn (@word.rep 32 word) (Init.Nat.add (S hole) (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) ws))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws)))))) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S (S (S O)))))))) ws)))) R))));
eapply (@rew_zoom_bw _ (@word.add 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) (@word.opp 32 word addr)) _ (wsub_def _ _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.min (S (S (S (S (S O))))) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (Init.Nat.min (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (Init.Nat.sub (@length (@word.rep 32 word) ws) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)))) (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@Datatypes.app (@word.rep 32 word) (@List.skipn (@word.rep 32 word) (Init.Nat.add (S O) (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word hole) 4)) ws))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws)))))) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S (S (S O)))))))) ws)))) R))));
eapply (@rew_zoom_bw _ (@word.add 32 word addr (@word.add 32 word (@word.of_Z 32 word (Z.mul 2 4)) (@word.opp 32 word addr))) _ (wadd_to_right_assoc _ _ _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.min (S (S (S (S (S O))))) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (Init.Nat.min (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (Init.Nat.sub (@length (@word.rep 32 word) ws) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)))) (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@Datatypes.app (@word.rep 32 word) (@List.skipn (@word.rep 32 word) (Init.Nat.add (S O) (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word hole) 4)) ws))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws)))))) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S (S (S O)))))))) ws)))) R))));
eapply (@rew_zoom_bw _ (@word.of_Z 32 word (Z.mul 2 4)) _ (wadd_opp_r_distant _ _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.min (S (S (S (S (S O))))) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (Init.Nat.min (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (Init.Nat.sub (@length (@word.rep 32 word) ws) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)))) (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@Datatypes.app (@word.rep 32 word) (@List.skipn (@word.rep 32 word) (Init.Nat.add (S O) (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word hole) 4)) ws))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word (@word.sub 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) addr)) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws)))))) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S (S (S O)))))))) ws)))) R))));
eapply (@rew_zoom_bw _ (@word.add 32 word (@word.add 32 word addr (@word.of_Z 32 word (Z.mul 2 4))) (@word.opp 32 word addr)) _ (wsub_def _ _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.min (S (S (S (S (S O))))) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (Init.Nat.min (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (Init.Nat.sub (@length (@word.rep 32 word) ws) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)))) (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@Datatypes.app (@word.rep 32 word) (@List.skipn (@word.rep 32 word) (Init.Nat.add (S O) (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word hole) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws)))))) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S (S (S O)))))))) ws)))) R))));
eapply (@rew_zoom_bw _ (@word.add 32 word addr (@word.add 32 word (@word.of_Z 32 word (Z.mul 2 4)) (@word.opp 32 word addr))) _ (wadd_to_right_assoc _ _ _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.min (S (S (S (S (S O))))) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (Init.Nat.min (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (Init.Nat.sub (@length (@word.rep 32 word) ws) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)))) (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@Datatypes.app (@word.rep 32 word) (@List.skipn (@word.rep 32 word) (Init.Nat.add (S O) (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word hole) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws)))))) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S (S (S O)))))))) ws)))) R))));
eapply (@rew_zoom_bw _ (@word.of_Z 32 word (Z.mul 2 4)) _ (wadd_opp_r_distant _ _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.min (S (S (S (S (S O))))) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (Init.Nat.min (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (Init.Nat.sub (@length (@word.rep 32 word) ws) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)))) (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@Datatypes.app (@word.rep 32 word) (@List.skipn (@word.rep 32 word) (Init.Nat.add (S O) (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word hole) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws)))))) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (@length (@word.rep 32 word) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (S (S (S (S (S (S (S O)))))))) ws)))) R))));
eapply (@rew_zoom_bw _ (S (@length (@word.rep 32 word) (@nil (@word.rep 32 word)))) _ (l_length_cons _ _ _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.min (S (S (S (S (S O))))) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (Init.Nat.min (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (Init.Nat.sub (@length (@word.rep 32 word) ws) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)))) (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@Datatypes.app (@word.rep 32 word) (@List.skipn (@word.rep 32 word) (Init.Nat.add (S O) (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws)))))) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add hole (S (S (S (S (S (S (S O)))))))) ws)))) R))));
eapply (@rew_zoom_bw _ O _ (l_length_nil _) (fun hole => (@iff1 (@map.rep (@word.rep 32 word) Init.Byte.byte mem) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.min (S (S (S (S (S O))))) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (Init.Nat.min (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (Init.Nat.sub (@length (@word.rep 32 word) ws) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)))) (S (S (S (S (S O)))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S O))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws)) (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@Datatypes.app (@word.rep 32 word) (@List.skipn (@word.rep 32 word) (Init.Nat.add (S O) (S (S (S (S (S O)))))) (@List.firstn (@word.rep 32 word) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10))) (@List.skipn (@word.rep 32 word) (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) ws))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (Z.to_nat (Z.div (@word.unsigned 32 word (@word.of_Z 32 word (Z.mul 2 4))) 4)) (Z.to_nat (@word.unsigned 32 word (@word.of_Z 32 word 10)))) ws)))))) R) (@sep (@word.rep 32 word) Init.Byte.byte mem (@array 32 word Init.Byte.byte mem (@word.rep 32 word) (@Scalars.scalar 32 word mem) (@word.of_Z 32 word 4) addr (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws) (@Datatypes.app (@word.rep 32 word) (@List.firstn (@word.rep 32 word) (Init.Nat.sub (@length (@word.rep 32 word) ws) (S (S (S (S (S (S (S O)))))))) (@cons (@word.rep 32 word) (@word.mul 32 word (@List.nth (@word.rep 32 word) (S (S (S (S (S (S (S O))))))) ws (@default (@word.rep 32 word) (@word_inhabited 32 word))) (@word.of_Z 32 word 2)) (@nil (@word.rep 32 word)))) (@List.skipn (@word.rep 32 word) (Init.Nat.add (S hole) (S (S (S (S (S (S (S O)))))))) ws)))) R))));
idtac).

  Abort.


  Lemma simplification1_proof1: simplification1.
  Proof.
    unfold simplification1. intros.
    (* takes forever: list_simpl_in_goal. *)
    match goal with
    | |- iff1 _ ?x => remember x as RHS
    end.
    Time list_simpl_in_goal. (* 1.282 secs *)
    subst RHS.
    (* takes forever: list_simpl_in_goal. *)
    match goal with
    | |- iff1 ?x _ => remember x as LHS
    end.
    Time list_simpl_in_goal. (* 0.814 secs *)
    subst LHS.
    reflexivity.
  Qed.

End WithParameters.
