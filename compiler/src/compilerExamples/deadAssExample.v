Require Import compiler.ExprImp.
Require Import compiler.Pipeline.
Require Import compiler.DeadAssignmentDef.
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


 (* dead assignments because of immediate optimization *)

  (* loading a constant into a variable usually assigns the constant first to a
     temp variable, but with the useimmediate optimization the temp variable shouldn't
     be used *)
  Definition test_constant : (string * (list string * list string * cmd))
    :=  ("main", ([]: list string, ["ret_val"],
                     (cmd.seq
                           (cmd.set "ret_val" (expr.literal 420))
                           (cmd.set "ret_val" (expr.literal 69))))).

  (* making sure that the optimization doesn't optimize out an assignment to the
     same variable (e.g. x = x + constant), and that it recurses into a stack alloc. *)
  Definition test_stackalloc : (string * (list string * list string * cmd))
    :=  ("main", ([]: list string, ["ret_val"],
                     (cmd.stackalloc "x" 4
                        (cmd.seq (cmd.set "x" (expr.literal 127))
                           (cmd.seq (cmd.set "x" (expr.op bopname.add (expr.var "x")
                                                    (expr.literal 85)))
                                    (cmd.set "ret_val" (expr.var "x"))))))).


  (* checking that if-else's are recursed into *)
  Definition test_ifelse : (string * (list string * list string * cmd))
    :=  ("main", ([]: list string, ["ret_val"],
                     (cmd.seq (cmd.set "ret_val" (expr.literal 91))
                        (cmd.cond
                           (expr.var "ret_val")
                           (cmd.set "ret_val" (expr.literal 63))
                           (cmd.seq
                              (cmd.set "ret_val" (expr.literal 123))
                              (cmd.set "ret_val" (expr.literal 369)))
        )))).



(* test to check breaking a call*)
  Definition test_call_fn : (string * (list string * list string * cmd))
    :=  ("add", (["x"; "y"], ["ret_val"],
                  (cmd.set "ret_val"
                     (expr.op bopname.add
                        (expr.var "x")
                        (expr.var "y"))))).

  Definition test_call:  (string * (list string * list string * cmd))
    :=  ("main", ([]: list string, ["ret_val"],
                     (cmd.call ["ret_val"] "add" [expr.literal 131; expr.literal (-97)]))).
  (* test to check simple loops *)
  Definition test_loop_fn : (string * (list string * list string * cmd))
    :=  ("add", (["x"; "y"], ["ret_val"],
                  (cmd.seq (cmd.set "ret_val" (expr.var "x"))
                     (cmd.while
                        (expr.op
                           bopname.or
                           (expr.op
                              bopname.lts
                              (expr.var "y")
                              (expr.literal 0))
                           (expr.op
                              bopname.lts
                              (expr.literal 0)
                              (expr.var "y")))
                        (cmd.cond
                           (expr.op
                              bopname.lts
                              (expr.var "y")
                              (expr.literal 0))
                           (cmd.seq
                              (cmd.set "ret_val"
                                 (expr.op
                                    bopname.sub
                                    (expr.var "ret_val")
                                    (expr.literal 1)))
                              (cmd.set "y"
                                 (expr.op
                                    bopname.add
                                    (expr.var "y")
                                    (expr.literal 1))))
                           (cmd.seq
                              (cmd.set "ret_val"
                                 (expr.op
                                    bopname.add
                                    (expr.var "ret_val")
                                    (expr.literal 1)))
                              (cmd.set "y"
                                 (expr.op
                                    bopname.sub
                                    (expr.var "y")
                                    (expr.literal 1))))))))).

  Definition test_loop:  (string * (list string * list string * cmd))
    :=  ("main", ([]: list string, ["ret_val"],
                     (cmd.call ["ret_val"] "add" [expr.literal 131; expr.literal (-97)]))).

  Definition compile_ext_call(posenv: funpos_env)(mypos stackoffset: Z)(s: FlatImp.stmt Z) : list Instruction := [].

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
                          ([test_constant] ::
                             [test_stackalloc] ::
                             [test_ifelse] ::
                             [test_loop_fn; test_loop] ::
                             [test_call_fn; test_call] :: [])) in set (res := r).
  match goal with
  | res := Success (?x) |- _ => exact x
  end.
Defined.



Definition multi_compile' funs_lists :=
  List.all_success
    (List.map
       (fun x => '(insts, _, _) <- (compile' compile_ext_call x) ;; Success insts) funs_lists).

Definition imm_asm' : list (list Instruction).
  let r := eval cbv in (multi_compile'
                          ([test_constant] ::
                             [test_stackalloc] ::
                             [test_ifelse] ::
                             [test_loop_fn; test_loop] ::
                             [test_call_fn; test_call] :: []))  in set (res := r).
  match goal with
  | res := Success (?x) |- _ => exact x
  end.
Defined.

Module PrintAssembly.
  Import riscv.Utility.InstructionNotations.
  Goal True. let r := eval unfold imm_asm in imm_asm in idtac (* r *)  . Abort.
End PrintAssembly.


Module PrintAssembly'.
  Import riscv.Utility.InstructionNotations.
  Goal True. let r := eval unfold imm_asm' in imm_asm' in idtac (* r *)  . Abort.

End PrintAssembly'.

Module CheckAssembly.
  Goal Forall (bverify.validInstructions RV32I) imm_asm'.
    repeat (constructor; [solve
                            [apply bverify.bvalidInstructions_valid;
                             vm_compute; reflexivity]
                         | ]).
    constructor.
  Qed.
End CheckAssembly.
