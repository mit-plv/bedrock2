Require Import Coq.ZArith.ZArith.
Require Import riscv.util.Word.
Require Import riscv.util.BitWidths.
Require Import compiler.util.Common.
Require Import compiler.Op.
Require Import riscv.util.BitWidth32.
Require Import compiler.util.List_Map.
Require Import compiler.util.List_Set.
Require Import compiler.FlatImp.
Require Import riscv.MachineWidth32.
Require Import riscv.util.ListLib.
Require Import riscv.Decode.
Require Import riscv.PseudoInstructions.
Require Import riscv.InstructionCoercions.
Require Import riscv.Program.
Import ListNotations.

Open Scope ilist_scope.

Definition var: Set := Z.
Definition func: Set := Empty_set.
Inductive act: Set := Select. (* only one action (= "external call" = inline assembly snippet) *)

Instance act_dec: DecidableEq act. left. destruct x; destruct y. reflexivity. Defined.

Instance myparams: Basic_bopnames.parameters := {|
  varname := var;
  funcname := func;
  actname := act;
|}.

Instance annoying: DecidableEq (list varname * list varname * stmt). Admitted.


Inductive ext_spec: act -> list Empty_set -> list (word 32) ->
                    (list Empty_set -> list (word 32) -> Prop) -> Prop :=
| ext_select: forall i selector args,
    i = uwordToZ (wshiftr selector (ZToWord 32 2)) ->
    0 <= i < Zlength args ->
    ext_spec Select nil (selector :: args)
             (fun t' results =>
                t' = nil /\
                exists garbageWord,
                  results = [Znth args i (ZToWord 32 0); garbageWord]).


Instance myFlatImpParams: FlatImp.parameters := {|
  FlatImp.bopname_params := myparams;
  FlatImp.Event := Empty_set; (* no trace to keep track of external calls *)
  FlatImp.ext_spec := ext_spec;
|}.

Definition map_with_index{A B: Type}(f: A -> Z -> B)(l: list A): list B :=
  fst (List.fold_right (fun elem '(acc, i) => (f elem i :: acc, i-1)) (nil, Zlength l - 1) l).


(* later, we'll modify the compiler to receive the absolute position of the code
   as an argument, which would allow us to use JALR here and get rid of the helpervar *)
Definition compile_ext_call(args: list var)(a: act)(results: list var): list Instruction :=
  match a with
  | Select =>
    match args, results with
    | selectorvar :: argvars, resvar :: helpervar :: nil => [[
        Auipc helpervar 0;
        Add helpervar helpervar selectorvar;
        Jalr Register0 helpervar 8
      ]] ++ concat
        (map_with_index
           (fun argvar i => [[ Addi resvar argvar 0; J ((Zlength argvars - i) * 8 - 4) ]])
           argvars)
    | _, _ => [[ ]] (* invalid *)
    end
  end.


(*
def test(addr, inp1, inp2):
    s = *addr // might take a long time to load
    // precompute possible operations while waiting for s
    a = inp1 * inp2
    b = inp1 + inp2
    c = inp1 - inp2
    (r, garbage) = select(s, a, b, c)
    return r
 *)

Definition _addr: varname := 1.
Definition _inp1: varname := 2.
Definition _inp2: varname := 3.
Definition _a: varname := 4.
Definition _b: varname := 5.
Definition _c: varname := 6.
Definition _r: varname := 7.
Definition _garbage: varname := 8.
Definition _s: varname := 9.

Definition test: stmt :=
  (SSeq (SLoad _s _addr)
  (SSeq (SOp _a bopname.mul _inp1 _inp2)
  (SSeq (SOp _b bopname.add _inp1 _inp2)
  (SSeq (SOp _c bopname.sub _inp1 _inp2)
        (SInteract [_r; _garbage] Select [_s; _a; _b; _c]))))).
