Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Tactics.autoforward.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Map.Interface.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.SepLib.
Require Import bedrock2.sepapp.
Require Import bedrock2.HeapletwiseHyps.

Section WithMem.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}
          {mem: map.map word Byte.byte} {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Lemma emp_True_at_addr_sepapp_l: forall p m addr,
      autoforward (with_mem m (sepapp (emp_at_addr True) p addr))
                  (with_mem m (p addr)).
  Proof.
    unfold autoforward, with_mem. intros.
    unfold emp_at_addr, sepapp in H.
    rewrite sep_emp_l in H. apply proj2 in H. rewrite word.add_0_r in H. exact H.
  Qed.

  Lemma emp_True_at_addr_sepapp_r: forall p sz m addr,
      autoforward (with_mem m (@sepapp _ _ _ _ p (emp_at_addr True) sz addr))
                  (with_mem m (p addr)).
  Proof.
    unfold autoforward, with_mem. intros.
    unfold emp_at_addr, sepapp in H.
    rewrite sep_emp_r in H. apply proj1 in H. exact H.
  Qed.
End WithMem.

#[export] Hint Extern 1 (autoforward (with_mem _ (sepapp (emp_at_addr True) _ _)) _)
=> eapply emp_True_at_addr_sepapp_l : typeclass_instances.

#[export] Hint Extern 1 (autoforward (with_mem _ (sepapp _ (emp_at_addr True) _)) _)
=> eapply emp_True_at_addr_sepapp_r : typeclass_instances.
