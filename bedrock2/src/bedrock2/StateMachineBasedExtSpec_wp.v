Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import bedrock2.Semantics.

Section WithMem.
  Context {width: Z} {BW: Bitwidth width}
          {word: word.word width} {mem: map.map word Byte.byte}.

  Context (state: Type).
  Context (is_initial_state: state -> Prop).
  Context (step:
            (* intial state *)
            state ->
            (* input to external call: memory given away, function name, list of arguments *)
            mem -> string -> list word ->
            (* output (as a arguments to a postcondition):
               memory received back, return values, new state *)
            (mem -> list word -> state -> Prop) ->
            Prop).

(*
  Fixpoint trace_leads_to_state_satisfying(t: trace)(initial: state)
    (post: state -> Prop): Prop :=
    match t with
    | nil => post initial
    | cons ((mGive, action, args), (mReceive, rets)) t' =>
        trace_leads_to_state_satisfying initial t' (fun s =>
          step mGive action args (fun mReceive' rets' => ??
  Abort.
*)
End WithMem.
