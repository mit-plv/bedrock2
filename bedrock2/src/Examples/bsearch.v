Require Import Coq.Strings.String Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
From bedrock2 Require Import NotationsInConstr ProgramLogic Map.Separation Array Scalars TailRecursion.

Require bedrock2.Examples.Demos.
Definition bsearch := @Demos.bsearch _ Demos.BinarySearch.StringNames.Inst.

From coqutil Require Import Datatypes.List Word.Interface Map.Interface. (* coercions word and rep *)
From bedrock2 Require Import Semantics BasicC64Semantics.

Local Instance mapok: map.ok mem := SortedListWord.ok (Naive.word 64 eq_refl) _.
Local Instance wordok: coqutil.Word.Interface.word.ok word := coqutil.Word.Naive.ok _ _.
Local Instance byteok: coqutil.Word.Interface.word.ok byte := coqutil.Word.Naive.ok _ _.
Definition admit {T} : T. Admitted.

Goal exists (x4 : list word) (x5 : mem -> Prop), forall M : mem,
    sep (array scalar (word.of_Z 0) (word.of_Z 0) x4) x5 M ->
    sep (array scalar (word.of_Z 0) (word.of_Z 0) nil) (fun _ => False) M
.
Proof.
  unshelve (refine (ex_intro _ ?[e1] _); refine (ex_intro _ ?[e2] _); intros M H); cycle -1.
  1: unshelve epose proof ((admit : forall n, n = n -> Lift1Prop.iff1
       (sep (array scalar (word.of_Z 0) (word.of_Z 0) ?[Goal]) (sep ?[P] ?[Q]))
       (array ?[element] ?[a] ?[aa] ?[xs]))_) as Hrw; cycle -1.
  1: unshelve (let Hrw := open_constr:((Hrw _)) in clear H;
       epose proof (proj1 (SeparationLogic.Proper_sep_iff1 _ _ Hrw _ _ (RelationClasses.reflexivity _) _) admit) as XX).
  1: destruct M.
  all: apply admit.
  Show Proof.
(* (ex_intro *)
(*    (fun x4 : list word => *)
(*     exists x5 : mem -> Prop, *)
(*       forall M : mem, *)
(*       sep (array scalar (word.of_Z 0) (word.of_Z 0) x4) x5 M -> *)
(*       sep (array scalar (word.of_Z 0) (word.of_Z 0) nil) *)
(*         (fun _ : mem => False) M) admit *)
(*    (ex_intro *)
(*       (fun x5 : mem -> Prop => *)
(*        forall M : mem, *)
(*        sep (array scalar (word.of_Z 0) (word.of_Z 0) admit) x5 M -> *)
(*        sep (array scalar (word.of_Z 0) (word.of_Z 0) nil) *)
(*          (fun _ : mem => False) M) admit *)
(*       (fun (M : mem) *)
(*          (_ : sep (array scalar (word.of_Z 0) (word.of_Z 0) admit) admit M) *)
(*        => *)
(*        let Hrw : *)
(*          admit = admit -> *)
(*          Lift1Prop.iff1 *)
(*            (sep (array scalar (word.of_Z 0) (word.of_Z 0) admit) *)
(*               (sep admit admit)) (array admit admit admit admit) := *)
(*          admit admit in *)
(*        let XX : sep (array admit admit admit admit) admit admit := *)
(*          proj1 *)
(*            (SeparationLogic.Proper_sep_iff1 *)
(*               (sep (array scalar (word.of_Z 0) (word.of_Z 0) admit) *)
(*                  (sep admit admit)) (array admit admit admit admit) *)
(*               (Hrw *)
(*                  (match *)
(*                     M as r *)
(*                     return *)
(*                       (sep (array scalar (word.of_Z 0) (word.of_Z 0) admit) *)
(*                          admit r -> *)
(*                        (admit = admit -> *)
(*                         Lift1Prop.iff1 *)
(*                           (sep *)
(*                              (array scalar (word.of_Z 0) (word.of_Z 0) admit) *)
(*                              (sep admit admit)) *)
(*                           (array admit admit admit admit)) ->  *)
(*                        admit = admit) *)
(*                   with *)
(*                   | {| SortedList.value := value; SortedList._value_ok := *)
(*                     _value_ok |} => *)
(*                       fun *)
(*                         (_ : sep *)
(*                                (array scalar (word.of_Z 0)  *)
(*                                   (word.of_Z 0) admit) admit *)
(*                                {| *)
(*                                SortedList.value := value; *)
(*                                SortedList._value_ok := _value_ok |}) *)
(*                         (_ : admit = admit -> *)
(*                              Lift1Prop.iff1 *)
(*                                (sep *)
(*                                   (array scalar (word.of_Z 0)  *)
(*                                      (word.of_Z 0) admit)  *)
(*                                   (sep admit admit)) *)
(*                                (array admit admit admit admit)) => admit *)
(*                   end H Hrw)) admit admit (RelationClasses.reflexivity admit) *)
(*               admit) admit in *)
(*        admit))) *)
Qed. (* Error: No such section variable or assumption: H9. *)