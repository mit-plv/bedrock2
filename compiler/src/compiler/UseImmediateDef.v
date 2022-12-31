Require Import compiler.util.Common.
Require Import compiler.FlattenExprDef. (* Only imported for testing UseImmediate *)
Require Import compiler.StringNameGen. (* Only imported for testing UseImmediate *)
Require Import compiler.FlatImp.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.Syntax.
Require Import coqutil.Tactics.fwd.
Require Import String.
 
Open Scope Z_scope.

Definition ex0 := (["a"], [] : list string, Syntax.cmd.set "a" (Syntax.expr.op bopname.add (Syntax.expr.literal 1) (Syntax.expr.literal 2))).
Definition ex1 := (["b"], ["a"], Syntax.cmd.set "b" (Syntax.expr.op bopname.add (Syntax.expr.var "a") (Syntax.expr.literal 1))).
Definition ex2 := (["b"], ["a"], Syntax.cmd.set "b" (Syntax.expr.op bopname.add (Syntax.expr.literal 1) (Syntax.expr.var "a"))).
Definition ex3 := (["c"], ["a"], Syntax.cmd.stackalloc "b" 4
                                              (Syntax.cmd.seq
                                                 (Syntax.cmd.set "b"
                                                    (Syntax.expr.op bopname.mul
                                                       (Syntax.expr.literal 1)
                                                       (Syntax.expr.op bopname.add
                                                          (Syntax.expr.var "a")
                                                          (Syntax.expr.literal 2))))
                                                 (Syntax.cmd.set "c"
                                                    (Syntax.expr.op bopname.add
                                                       (Syntax.expr.literal 0)
                                                       (Syntax.expr.op bopname.mul
                                                          (Syntax.expr.literal 3)
                                                          (Syntax.expr.var "b")))))).
                                                          
                                                    
                                                                                       

Definition sourceExs := [ex0; ex1; ex2; ex3].
Definition unwrappedFlattenExs := let tmp :=  List.all_success (map flatten_function sourceExs) in
                                  match tmp with
                                  | Success l => l
                                  | _ => []
                                  end.
Compute unwrappedFlattenExs.
(* Fixpoint list_len {A: Type} (l: list A) : nat :=
  match l with
  | hd :: tl => 1 + list_len tl
  | _ => 0
  end.

Compute list_len sourceExs.
Compute list_len unwrappedFlattenExs.*)
(*
Definition unsignedFitsBits(bitwidth: Z)(lit: Z): bool := (0 <=? lit) && (lit <? Z.pow 2 bitwidth).
Definition signedFitsBits(bitwidth: Z)(lit: Z): bool := (- (Z.pow 2 (bitwidth - 1)) <=? lit) && (lit <? (Z.pow 2 (bitwidth - 1))).
*)
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
        | SLit v1 l1, SOp v2 op v2a (Var v2b) => default
        | SLit v1 l1, SSeq (SLit v1b l1b) (SOp v2 op v2a (Var v2b)) =>
            if (eqb v1 v1b) then default else default
        | _, _ => default
        end
    | _ => s
    end.
  (*
  Fixpoint useImmediate(s: stmt string) : stmt string :=
    match s with               
    | SSeq s12 s3 =>
        let default := SSeq (useImmediate s12) (useImmediate s3)
        in match s12, s3 with
           | SSeq s1 s2, SOp v3 op v1' (Var v2') =>
               match op with
               | Syntax.bopname.add
               | Syntax.bopname.and
               | Syntax.bopname.or
               | Syntax.bopname.xor =>
                   match s1, s2 with
                   | SLit v1 l1, SLit v2 l2 =>
                       if andb (eqb v2 v2') (is12BitImmediate l2)
                       then SSeq s1 (SOp v3 op v1' (Const l2))
                       else
                         if andb (eqb v1 v1') (is12BitImmediate l1)
                         then SSeq s2 (SOp v3 op v2' (Const l1))
                         else default
                   | SLit v1 l1, _ =>
                       if andb (eqb v1 v1') (is12BitImmediate l1)
                       then SSeq s2 (SOp v3 op v2' (Const l1))
                       else default
                   | _, SLit v2 l2 =>
                       if andb (eqb v2 v2') (is12BitImmediate l2)
                       then SSeq s1 (SOp v3 op v1' (Const l2))
                       else default
                   | _, _ => default
                   end
               | Syntax.bopname.ltu => (* 0 to 12-bits and all 32 bits down by 12 bits  (FIX THIS LATER) *)
                   match s2 with
                   | SLit v2 l2 =>
                       if andb (eqb v2 v2') (is12BitImmediate l2)
                       then SSeq s1 (SOp v3 op v1' (Const l2))
                       else default
                   | _ => default
                   end
               | Syntax.bopname.lts =>
                   match s2 with
                   | SLit v2 l2 =>
                       if andb (eqb v2 v2') (is12BitImmediate l2)
                       then SSeq s1 (SOp v3 op v1' (Const l2))
                       else default
                   | _ => default
                   end
               | Syntax.bopname.srs
               | Syntax.bopname.slu
               | Syntax.bopname.sru =>
                   match s2 with
                   | SLit v2 l2 =>
                       if andb (eqb v2 v2') (is5BitImmediate l2)
                       then SSeq s1 (SOp v3 op v1' (Const l2))
                       else default
                   | _ => default
                   end
               | Syntax.bopname.sub =>
                   match s2 with
                   | SLit v2 l2 =>
                       if andb (eqb v2 v2') (is12BitImmediate (-l2))
                       then SSeq s1 (SOp v3 Syntax.bopname.add v1' (Const (-l2)))
                       else default
                   | _ => default
                   end
               | _ => default
               end
           | _, _ =>  default
           end
    | SStackalloc v1 sz1 s => SStackalloc v1 sz1 (useImmediate s) 
    | _ => s
    end.*)
End WithArgs. 






Definition useImmOnFlats (t: (list string * list string * stmt string)) : (list string * list string * stmt string)
  := match t with
     | (targs, trets, tstmt) => (targs, trets, (useImmediate (fun x => true) (fun x => true)  tstmt))
     end.

Definition immediateExs := map useImmOnFlats unwrappedFlattenExs.
Compute immediateExs.

