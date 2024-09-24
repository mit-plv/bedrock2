From Coq Require Import List.
Require Import bedrock2.ReversedListNotations. Local Open Scope list_scope.

Section Interleave.
  Context [E: Type]. (* type of events (trace elements) *)

  (* A tracelet is the trace of one request and its response. *)

  (* Interleaves a list of tracelets into one trace *)
  Inductive interleave: list (list E) -> list E -> Prop :=
  | interleave_nil: forall trs,
      List.Forall (eq nil) trs ->
      interleave trs nil
  | interleave_cons: forall (trs1 trs2: list (list E)) (tr: list E) (e: E) (es: list E),
      interleave (trs1 ;+ tr ;++ trs2) es ->
      interleave (trs1 ;+ (tr ;+ e) ;++ trs2) (es ;+ e).

  (* Q: Why not a set of tracelets instead of a list of tracelets?
     A: Order of tracelets will matter later below, when we apply them on the state *)

  Context [S: Type].

  (* accepts a list of E that make up the request, then atomically reads and
     updates the state, and returns a list of E that make up the response *)
  Context (handle_request: list E -> S -> S * list E).

  (* Note that the list of tracelets is ordered by the sequence in which their
     handling updates the state *)

  Fixpoint tracelets_handle_requests(sInit: S)(tracelets: list (list E))(sFinal: S) :=
    match tracelets with
    | trs ;+ tr =>
        exists sMid, tracelets_handle_requests sInit trs sMid /\
        exists req resp, tr = req ;++ resp /\
        handle_request req sMid = (sFinal, resp)
    | nil => sInit = sFinal
    end.

  Definition trace_handles_requests(sInit: S)(trace: list E)(sFinal: S) :=
    exists (tracelets: list (list E)),
      interleave tracelets trace /\ tracelets_handle_requests sInit tracelets sFinal.

End Interleave.
