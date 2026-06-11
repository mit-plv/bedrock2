Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require coqutil.Datatypes.String coqutil.Map.SortedList coqutil.Map.SortedListString.
Require Import coqutil.Word.Interface coqutil.Map.SortedListWord.
Require Import coqutil.Word.Naive.

(* Local because it automatically adds arbitrary word size instance. *)
#[local] Hint Extern 0 (word.word ?width) => exact (Naive.word width) : typeclass_instances.

#[export] Instance word_ok {width} {BW : Bitwidth.Bitwidth width}: word.ok (Naive.word width).
Proof. destruct Bitwidth.width_cases as [W|W]; symmetry in W; destruct W; [exact word32_ok | exact word64_ok]. Defined.

#[export] Hint Extern 0 (Interface.map.map (@word.rep _ (Naive.word _)) Coq.Init.Byte.byte) =>
  exact (@SortedListWord.map _ _ word_ok _) : typeclass_instances.

#[export] Hint Extern 0 (coqutil.Map.Interface.map.ok (SortedListWord.map (@word.rep _ (Naive.word _)) _)) =>
  exact (SortedListWord.ok _ _) : typeclass_instances.

#[export] Hint Extern 0 (Interface.map.map String.string ?value) =>
  exact (SortedListString.map value) : typeclass_instances.
#[export] Hint Extern 0 (coqutil.Map.Interface.map.ok (SortedListString.map _)) =>
  exact (SortedListString.ok _) : typeclass_instances.

#[export] Hint Extern 0 (Semantics.ExtSpec) => exact (fun _ _ _ _ _ => False) : typeclass_instances.

#[export] Instance weaken_ext_spec width {BW : Bitwidth.Bitwidth width} :
  Morphisms.Proper
    (Morphisms.respectful
       (Morphisms.pointwise_relation (@Interface.map.rep (Naive.word width) (Coq.Init.Byte.byte) _)
          (Morphisms.pointwise_relation (list (Naive.word width)) Basics.impl))
       Basics.impl) (fun post => False).
Proof.
  cbn in *.
  unfold Morphisms.Proper, Morphisms.respectful, Morphisms.pointwise_relation, Basics.impl.
  intros.
  assumption.
Qed.
#[export] Instance ext_spec_ok width {BW : Bitwidth.Bitwidth width}:
    Semantics.ext_spec.ok (fun _ _ _ _ _ => False).
Proof.
  constructor; intros; try contradiction.
  apply weaken_ext_spec.
Qed.

Section TypeclassTests.
  Variable width : Z.
  Context {BW : Bitwidth.Bitwidth width}.

  (* word *)
  Goal word.word width.
    typeclasses eauto.
  Qed.
  Goal word.ok (Naive.word width).
    typeclasses eauto.
  Qed.

  (* mem *)
  Goal (Interface.map.map (Naive.word width) (Coq.Init.Byte.byte)).
    typeclasses eauto.
  Qed.
  Goal coqutil.Map.Interface.map.ok (SortedListWord.map (Naive.word width) (Coq.Init.Byte.byte)).
    typeclasses eauto.
  Qed.

  (* locals *)
  Goal (Interface.map.map String.string (Naive.word width)).
    typeclasses eauto.
  Qed.
  Goal (coqutil.Map.Interface.map.ok (SortedListString.map (Naive.word width))).
    typeclasses eauto.
  Qed.

  (* env *)
  Goal (Interface.map.map String.string (list String.string * list String.string * cmd)).
    typeclasses eauto.
  Qed.
  Goal (coqutil.Map.Interface.map.ok (SortedListString.map (list String.string * list String.string * cmd))).
    typeclasses eauto.
  Qed.

  (* ext_spec *)
  Goal (ext_spec.ok (fun _ _ _ _ _ => False)).
    typeclasses eauto.
  Qed.
End TypeclassTests.
