(* -*- eval: (load-file "../../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Load LiveVerif.

Definition counted{T: Type}(P: T) := P.

Ltac count_hyps pred :=
  match constr:(Set) with
  | _ => match goal with
         | H: ?t |- _ => lazymatch pred t with
                         | true =>
                             let __ := match constr:(Set) with
                                       | _ => change (counted t) in H
                                       end in
                             let r := count_hyps pred in
                             constr:(S r)
                         end
         end
  | _ => constr:(O)
  end.

Ltac assert_count0 pred n :=
  lazymatch count_hyps pred with
  | n => idtac
  | ?actual => fail "expected" n "but got" actual
  end.

Ltac uncount :=
  repeat match goal with
    | H: counted ?t |- _ => change t in H
    end.

Ltac assert_count pred n := assert_count0 pred n; uncount.

Ltac is_mem_hyp t :=
  lazymatch t with
  | with_mem _ _ => constr:(true)
  | _ => constr:(false)
  end.

Ltac is_mem_split_eq t :=
  lazymatch t with
  | _ = mmap.Def _ => constr:(true)
  | _ => constr:(false)
  end.

Ltac is_mem t :=
  lazymatch t with
  | @map.rep (@word.rep _ _) Coq.Init.Byte.byte _ => constr:(true)
  | _ => constr:(false)
  end.

#[export] Instance spec_of_test_if: fnspec :=                                .**/

uintptr_t test_if(uintptr_t px, uintptr_t py) /**#
  ghost_args := (R: mem -> Prop) x1 x2 y1 y2;
  requires t m := <{ * uint 32 (x1 + x2) px
                     * uint 32 (y1 + y2) py
                     * R }> m;
  ensures t' m' retv := t' = t /\
            <{ * uint 32 (x1 + x2) px
               * uint 32 (y1 + y2) py
               * R }> m' #**/                                              /**.
Derive test_if SuchThat (fun_correct! test_if) As test_if_ok.                   .**/
{                                                                          /**. .**/
  uintptr_t r = 0;                                                         /**. .**/
  if (load32(px) < load32(py)) {                                           /**. .**/
    r = load32(px);                                                        /**. .**/
  } else {                                                                 /**. .**/
    r = load32(py);                                                        /**. .**/
  } /**.

  assert_count is_mem_hyp 0%nat.
  assert_count is_mem_split_eq 0%nat.
  assert_count is_mem 0%nat.

  end if.

  assert_count is_mem_hyp 3%nat.
  assert_count is_mem_split_eq 1%nat.
  assert_count is_mem 4%nat.

  .**/ return r;                                                           /**. .**/
}                                                                          /**.
Qed.

End LiveVerif. Comments .**/ //.
