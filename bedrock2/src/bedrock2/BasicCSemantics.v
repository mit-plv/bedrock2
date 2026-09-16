Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require coqutil.Datatypes.String coqutil.Map.SortedList coqutil.Map.SortedListString.
Require Import coqutil.Word.Bitwidth coqutil.Map.SortedListWord.

#[export] Hint Extern 0 (Interface.map.map (bits ?width) Coq.Init.Byte.byte) =>
  exact (SortedListWord.map width Coq.Init.Byte.byte) : typeclass_instances.

#[export] Hint Extern 0 (coqutil.Map.Interface.map.ok (SortedListWord.map ?width _)) =>
  exact (SortedListWord.ok width _) : typeclass_instances.

#[export] Hint Extern 0 (Interface.map.map String.string ?value) =>
  exact (SortedListString.map value) : typeclass_instances.
#[export] Hint Extern 0 (coqutil.Map.Interface.map.ok (SortedListString.map _)) =>
  exact (SortedListString.ok _) : typeclass_instances.

#[export] Hint Extern 0 (Semantics.ExtSpec) => exact (fun _ _ _ _ _ => False) : typeclass_instances.

#[export] Instance weaken_ext_spec width {BW : Bitwidth.Bitwidth width} :
  Morphisms.Proper
    (Morphisms.respectful
       (Morphisms.pointwise_relation (@Interface.map.rep (bits width) (Coq.Init.Byte.byte) _)
          (Morphisms.pointwise_relation (list (bits width)) Basics.impl))
       Basics.impl) (fun post => False).
Proof.
  cbn in *.
  unfold Morphisms.Proper, Morphisms.respectful, Morphisms.pointwise_relation, Basics.impl.
  intros.
  assumption.
Qed.
(* Stated as a lemma: the Instance command would fill in the weaken field by
   typeclass search and leave its Bitwidth premise as a stray obligation. *)
Lemma ext_spec_ok width {BW : Bitwidth.Bitwidth width}:
    Semantics.ext_spec.ok (fun _ _ _ _ _ => False).
Proof.
  constructor; intros; try contradiction.
  exact (weaken_ext_spec width).
Qed.
#[export] Existing Instance ext_spec_ok.

Section TypeclassTests.
  Variable width : Z.
  Context {BW : Bitwidth.Bitwidth width}.

  (* mem *)
  Goal (Interface.map.map (bits width) (Coq.Init.Byte.byte)).
    typeclasses eauto.
  Qed.
  Goal coqutil.Map.Interface.map.ok (SortedListWord.map width (Coq.Init.Byte.byte)).
    typeclasses eauto.
  Qed.

  (* locals *)
  Goal (Interface.map.map String.string (bits width)).
    typeclasses eauto.
  Qed.
  Goal (coqutil.Map.Interface.map.ok (SortedListString.map (bits width))).
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
