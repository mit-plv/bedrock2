Require Import compiler.ExprImp.
Require Import compiler.Pipeline.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Words32Naive.
Require Import riscv.Utility.DefaultMemImpl32.
Require        riscv.Utility.InstructionNotations.
Require Import riscv.Utility.Encode.
Require Import coqutil.Map.SortedList.
Require        coqutil.Map.SortedListString.
Require Import compiler.MemoryLayout.
Require        riscv.Utility.bverify.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope ilist_scope.

Local Instance funpos_env: map.map string Z := SortedListString.map _.

Definition compile_ext_call(posenv: funpos_env)(mypos stackoffset: Z)(s: FlatImp.stmt Z) : list Instruction := [].

(* low_bound, hi_bound are expected inclusive bounds for UseImmediate optimization *)
Definition test_imm_op(op: bopname.bopname)(low_bound: Z)(hi_bound: Z)
  : (string * (list string * list string * cmd )) :=
  (("main"),
    (["a0"], ["ret_val"],
      (cmd.seq (cmd.set "a0" (expr.op op (expr.var "a0")
                                (expr.literal (low_bound - 1))))
         (cmd.seq (cmd.set "a0" (expr.op op (expr.var "a0")
                                   (expr.literal (low_bound))))
            (cmd.seq (cmd.set "a0" (expr.op op (expr.var "a0")
                                      (expr.literal (hi_bound))))
               (cmd.set "ret_val" (expr.op op (expr.var "a0")
                                     (expr.literal (hi_bound+1))))))))).

Definition imm_ex1 := test_imm_op bopname.add (-2048) (2047).
Definition imm_ex2 := test_imm_op bopname.sub (-2047) (2048).
Definition imm_ex3 := test_imm_op bopname.ltu (-2048) (2047).
Definition imm_ex4 := test_imm_op bopname.lts (-2048) (2047).
Definition imm_ex5 := test_imm_op bopname.srs 0 31.
Definition imm_ex6 := test_imm_op bopname.slu 0 31.

Local Instance RV32I_bitwidth: FlatToRiscvCommon.bitwidth_iset 32 RV32I.
Proof. reflexivity. Qed.

Definition multi_compile funs_lists :=
  List.all_success
    (List.map
       (fun x => '(insts, _, _) <- (compile compile_ext_call x) ;; Success insts) funs_lists).

(* Expressing nested list literals as [[x]] is wonky
   because of [[]] being used for list of Instructions *)
Definition imm_asm: list (list Instruction).
  let r := eval cbv in (multi_compile
                          ([imm_ex1] ::
                             [imm_ex2] ::
                             [imm_ex3] ::
                             [imm_ex4] ::
                             [imm_ex5] ::
                             [imm_ex6] :: [])) in set (res := r).
  match goal with
  | res := Success (?x) |- _ => exact x
  end.
Defined.

Module PrintAssembly.
  Import riscv.Utility.InstructionNotations.
  Goal True. let r := eval unfold imm_asm in imm_asm in idtac (* r *). Abort.
End PrintAssembly.

Module CheckAssembly.
  Goal Forall (bverify.validInstructions RV32I) imm_asm.
    repeat (constructor; [solve
                            [apply bverify.bvalidInstructions_valid;
                             vm_compute; reflexivity]
                         | ]).
    constructor.
  Qed.
End CheckAssembly.
