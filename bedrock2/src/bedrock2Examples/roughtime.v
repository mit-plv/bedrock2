
Require Import bedrock2.BasicCSyntax bedrock2.NotationsInConstr bedrock2.NotationsCustomEntry.
Require Import bedrock2.Array bedrock2.Scalars.
Import Syntax BinInt String List.ListNotations ZArith.
Require Import coqutil.Z.Lia.
From coqutil Require Import Word.Interface Map.Interface.
Require Import coqutil.Byte coqutil.Z.HexNotation.
From bedrock2.Map Require Import Separation SeparationLogic.

Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Coercion literal (z : Z) : Syntax.expr := Syntax.expr.literal z.
Local Coercion var (x : string) : Syntax.expr := Syntax.expr.var x.
Local Definition bedrock_func : Type := String.string * (list String.string * list String.string * cmd).
Local Coercion name_of_func (f : bedrock_func) := fst f.

Definition addToBuffer : bedrock_func :=
  let buffer := "buffer" in
  let x := "x" in
  let start := "start" in
  let num_bytes := "num_bytes" in
  let i := "i" in
  ("addToBuffer", ([buffer; x; start; num_bytes], []:list String.string, bedrock_func_body:(
  i = (constr:(1));
  while (i < num_bytes) {{
    store(buffer + start, x >> (i << constr:(3)) & constr:(Ox"FF"));
    i = (i + constr:(1))
  }}
))).

Definition createTimestampMessage :=
  let buffer := "buffer" in
  ("createTimestampMessage", ([buffer], []:list String.string, bedrock_func_body:(
  addToBuffer(buffer, constr:(5), constr:(0), constr:(4))
  (*TODO*)
))).

Require bedrock2.WeakestPrecondition.
Require Import bedrock2.Semantics bedrock2.FE310CSemantics.
Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic.

Require bedrock2.WeakestPreconditionProperties.
From coqutil.Tactics Require Import letexists eabstract.
Require Import bedrock2.ProgramLogic bedrock2.Scalars.


Section WithParameters.
  Context {p : FE310CSemantics.parameters}.

  Instance spec_of_addToBuffer : spec_of "addToBuffer" := fun functions =>
    forall p_addr (buf:list byte) x start num_bytes R m t,
      WeakestPrecondition.call (p:=@semantics_parameters p) functions "addToBuffer" t m [p_addr; x; start; num_bytes]
      (fun t' m' rets => t=t' /\ (sep (scalar p_addr x) R) m /\ rets = nil) .


  Lemma addToBuffer_ok : program_logic_goal_for_function! addToBuffer.
  Proof.
    repeat straightline.
  Abort.

  (* TODO
  Instance spec_of_createTimestampMessage := fun functions =>
      forall p_addr (buf:list byte) R m t,
        WeakestPrecondition.call functions "createTimestampMessage" t m [p_addr] (fun t' m' rets =>
  )
  *)
