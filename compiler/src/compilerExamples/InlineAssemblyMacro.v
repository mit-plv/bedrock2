Require Import Coq.ZArith.ZArith.
Require Import compiler.util.Common.
Require Import riscv.Utility.Monads.
Require Import coqutil.Map.SortedList.
Require Import compiler.FlatImp.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.PseudoInstructions.
Require Import riscv.Utility.InstructionCoercions.
Require Import riscv.Spec.Machine.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.FlatToRiscvCommon.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MinimalMMIO. (* not really *)
Require Import coqutil.Word.Naive riscv.Utility.Words32Naive.
Require Import riscv.Utility.DefaultMemImpl32.
Require Import coqutil.Map.Empty_set_keyed_map.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import coqutil.Map.SortedListString.
Import ListNotations.

Open Scope ilist_scope.

Axiom TODO: False.

Definition var: Set := Z.
Definition func: Set := string.
Definition act: Set := string.


Inductive ext_spec: act -> list Empty_set -> list word32 ->
                    (list Empty_set -> list word32 -> Prop) -> Prop :=
| ext_select: forall i selector args,
    i = word.unsigned (word.sru selector (word.of_Z 2)) ->
    0 <= i < Z.of_nat (length args) ->
    ext_spec "Select"%string nil (selector :: args)
             (fun t' results =>
                t' = nil /\
                exists garbageWord,
                  results = [nth (Z.to_nat i) args (word.of_Z 0); garbageWord]).


Definition map_with_index{A B: Type}(f: A -> Z -> B)(l: list A): list B :=
  fst (List.fold_right (fun elem '(acc, i) => (f elem i :: acc, i-1)) (nil, Z.of_nat (List.length l) - 1) l).


(* later, we'll modify the compiler to receive the absolute position of the code
   as an argument, which would allow us to use JALR here and get rid of the helpervar *)
Definition compile_interact(results: list var)(a: act)(args: list var): list Instruction :=
  match a with
  | Select =>
    match results, args with
    | resvar :: helpervar :: nil, selectorvar :: argvars => [[
        Auipc helpervar 0;
        Add helpervar helpervar selectorvar;
        Jalr Register0 helpervar 8
      ]] ++ concat
        (map_with_index
           (fun argvar i => [[ Addi resvar argvar 0; J ((Z.of_nat (List.length argvars) - i) * 8 - 4) ]])
           argvars)
    | _, _ => [[ ]] (* invalid *)
    end
  end.

Local Instance funpos_env: map.map string Z := SortedListString.map _.

Definition compile_ext_call(posenv: funpos_env)(mypos stackoffset: Z)(s: stmt Z) :=
  match s with
  | SInteract results a args => compile_interact results a args
  | _ => []
  end.

(*
def test(addr, inp1, inp2):
    s = *addr // might take a long time to load
    // precompute possible operations while waiting for s
    a = inp1 | inp2
    b = inp1 + inp2
    c = inp1 - inp2
    (r, garbage) = select(s, a, b, c)
    return r
 *)

Definition _addr: var := 1.
Definition _inp1: var := 2.
Definition _inp2: var := 3.
Definition _a: var := 4.
Definition _b: var := 5.
Definition _c: var := 6.
Definition _r: var := 7.
Definition _garbage: var := 31.
Definition _s: var := 9.

Definition test: stmt var :=
  (SSeq (SLoad Syntax.access_size.four _s _addr 0)
  (SSeq (SOp _a Syntax.bopname.or _inp1 _inp2)
  (SSeq (SOp _b Syntax.bopname.add _inp1 _inp2)
  (SSeq (SOp _c Syntax.bopname.sub _inp1 _inp2)
        (SInteract [_r; _garbage] "Select"%string [_s; _a; _b; _c]))))).

Definition compiled0: list Instruction.
  refine (compile_stmt RV32I compile_ext_call map.empty 0 0 test).
Defined.

Goal False. Proof. let r := eval cbv in compiled0 in set (compiled := r). Abort.
