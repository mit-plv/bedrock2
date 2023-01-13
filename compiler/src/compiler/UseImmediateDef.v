Require Import compiler.util.Common.
Require Import compiler.FlattenExprDef. (* Only imported for testing UseImmediate *)
Require Import compiler.StringNameGen. (* Only imported for testing UseImmediate *)
Require Import compiler.FlatImp.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.Syntax.
Require Import coqutil.Tactics.fwd.
Require Import String.
Open Scope string_scope. (* Only used for examples. *) 
Open Scope Z_scope.



Section WithArgs.
  Context (is5BitImmediate : Z -> bool).
  Context (is12BitImmediate: Z -> bool).

  
  
  Fixpoint useImmediate(s: stmt string) : stmt string :=
    match s with
    | SIf c s1 s2 => SIf c (useImmediate s1) (useImmediate s2)
    | SLoop s1 c s2 => SLoop (useImmediate s1) c (useImmediate s2)
    | SStackalloc v1 sz1 s => SStackalloc v1 sz1 (useImmediate s)
    | SSeq s1 s2 =>
        let used1 := useImmediate s1 in
        let used2 := useImmediate s2 in
        let default := SSeq used1 used2 in
        match used1, used2 with
        | SSkip, _ => used2
        | _, SSkip => used1
        | SLit v1 l1, SOp v2 op v2a (Var v2b) =>
            match op with
            | Syntax.bopname.add
            | Syntax.bopname.and
            | Syntax.bopname.or
            | Syntax.bopname.xor => if (is12BitImmediate l1) then
                                      if eqb v1 v2b then
                                        SOp v2 op v2a (Const l1)
                                      else if eqb v1 v2a then
                                             SOp v2 op v2b (Const l1)
                                           else default
                                    else default
            | Syntax.bopname.ltu
            | Syntax.bopname.lts => if (is12BitImmediate l1) then
                                      if eqb v1 v2b then
                                        SOp v2 op v2a (Const l1)
                                      else default
                                    else default
            | Syntax.bopname.srs
            | Syntax.bopname.sru
            | Syntax.bopname.slu => if (is5BitImmediate l1) then
                                      if eqb v1 v2b then
                                        SOp v2 op v2a (Const l1)
                                      else default
                                    else default
            | Syntax.bopname.sub => if (is12BitImmediate (-l1)) then
                                      if eqb v1 v2b then
                                        SOp v2 Syntax.bopname.add v2a (Const (-l1))
                                      else default
                                    else default
            | _ => default
            end
        | SLit v1 l1, SSeq (SLit v1b l1b) (SOp v2 op v2a (Var v2b)) =>
            if (eqb v1 v1b) then default
            else match op with
            | Syntax.bopname.add
            | Syntax.bopname.and
            | Syntax.bopname.or
            | Syntax.bopname.xor => if (is12BitImmediate l1) then
                                      if eqb v1 v2b then
                                        SSeq (SLit v1b l1b) (SOp v2 op v2a (Const l1))
                                      else if eqb v1 v2a then
                                             SSeq (SLit v1b l1b) (SOp v2 op v2b (Const l1))
                                           else default
                                    else default
            | _ => default
            end
        | _, _ => default
        end
    | _ => s
    end.
End WithArgs. 



Definition ex0 := (["a"], [] : list string, Syntax.cmd.set "a" (Syntax.expr.op bopname.add (Syntax.expr.literal 1) (Syntax.expr.literal 16))).
Definition ex1 := (["b"], ["a"], Syntax.cmd.set "b" (Syntax.expr.op bopname.slu (Syntax.expr.var "a") (Syntax.expr.literal 16))).
Definition ex2 := (["b"], ["a"], Syntax.cmd.set "b" (Syntax.expr.op bopname.add (Syntax.expr.literal 1) (Syntax.expr.var "a"))).
Definition ex3 := (["b"], ["a"], Syntax.cmd.set "b" (Syntax.expr.op bopname.ltu (Syntax.expr.var "a") (Syntax.expr.literal 16))).
                                                          
                                                    
                                                                                       

Definition sourceExs := [ex0; ex1; ex2; ex3].
Definition unwrappedFlattenExs := let tmp :=  List.all_success (map flatten_function sourceExs) in
                                  match tmp with
                                  | Success l => l
                                  | _ => []
                                  end.
Compute unwrappedFlattenExs.


Definition useImmOnFlats (t: (list string * list string * stmt string)) : (list string * list string * stmt string)
  := match t with
     | (targs, trets, tstmt) => (targs, trets, (useImmediate (fun x => true) (fun x => true) tstmt))
     end.

Definition immediateExs := map useImmOnFlats unwrappedFlattenExs.

(* Check that is5BitImmediate is used. *)
Definition useImmOnFlats' (t: (list string * list string * stmt string)) : (list string * list string * stmt string)
  := match t with
     | (targs, trets, tstmt) => (targs, trets, (useImmediate (fun x => Z.ltb x 16) (fun x => true) tstmt))
     end.

Definition immediateExs' := map useImmOnFlats' unwrappedFlattenExs.



(* Check that is12BitImmediate is used. *)
Definition useImmOnFlats'' (t: (list string * list string * stmt string)) : (list string * list string * stmt string)
  := match t with
     | (targs, trets, tstmt) => (targs, trets, (useImmediate (fun x => true) (fun x => Z.ltb x 16) tstmt))
     end.

Definition immediateExs'' := map useImmOnFlats'' unwrappedFlattenExs.

Compute unwrappedFlattenExs.
Compute immediateExs. (* All constants are small enough. *)
Compute immediateExs'. (* is5BitImmediate is true only for < 16. *)
Compute immediateExs''. (* is12BitImmediate is true only for < 16. *)
