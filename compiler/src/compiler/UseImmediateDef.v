Require Import compiler.util.Common.
Require Import compiler.FlatImp.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.Syntax.
Require Import coqutil.Tactics.fwd.
Require Import String.
 
Open Scope Z_scope.

Print stmt.
Print exec.
Print operand.

Definition literalFitsInBits(signed: bool)(bitwidth: Z)(lit: Z): bool :=
  match signed with
  | true =>  (- (Z.pow 2 (bitwidth - 1)) <=? lit) && (lit <? (Z.pow 2 (bitwidth - 1)))
  | false => (0 <? lit) && (lit <? (Z.pow 2 bitwidth))
  end.

Fixpoint useImmediate(s: stmt string) : stmt string :=
  match s with               
  | SSeq s12 s3 => let default := SSeq (useImmediate s12) (useImmediate s3)
                   in
                   match s12, s3 with
                   | SSeq s1 s2, SOp v3 op v1' (Var v2') => match op with
                                                            | Syntax.bopname.add
                                                            | Syntax.bopname.and
                                                            | Syntax.bopname.or
                                                            | Syntax.bopname.xor => match s1, s2 with
                                                                                    | SLit v1 l1, SLit v2 l2 =>
                                                                                        (*maybe stronger optimization, given both literals known? *)
                                                                                        if andb (eqb v2 v2') (literalFitsInBits true 12 l2)
                                                                                        then
                                                                                          SSeq s1 (SOp v3 op v1' (Const l2))
                                                                                        else
                                                                                          if andb (eqb v1 v1') (literalFitsInBits true 12 l1)
                                                                                          then
                                                                                            SSeq s2 (SOp v3 op v2' (Const l1))
                                                                                          else default
                                                                                        
                                                                                    | SLit v1 l1, _ => if andb (eqb v1 v1') (literalFitsInBits true 12 l1)
                                                                                                       then
                                                                                                         SSeq s2 (SOp v3 op v2' (Const l1))
                                                                                                       else
                                                                                                         default
                                                                                    | _, SLit v2 l2 => if andb (eqb v2 v2') (literalFitsInBits true 12 l2) 
                                                                                                       then
                                                                                                         SSeq s1 (SOp v3 op v1' (Const l2))
                                                                                                       else
                                                                                                         default
                                                                                    | _, _ => default
                                                                                    end
                                                            | Syntax.bopname.ltu
                                                            | Syntax.bopname.lts => match s2 with
                                                                                    | SLit v2 l2 => if andb (eqb v2 v2') (literalFitsInBits true 12 l2) 
                                                                                                       then
                                                                                                         SSeq s1 (SOp v3 op v1' (Const l2))
                                                                                                       else
                                                                                                         default
                                                                                    | _ => default
                                                                                    end
                                                            | Syntax.bopname.srs
                                                            | Syntax.bopname.slu
                                                            | Syntax.bopname.sru => match s2 with
                                                                                    | SLit v2 l2 => if andb (eqb v2 v2') (literalFitsInBits false 5 l2) 
                                                                                                       then
                                                                                                         SSeq s1 (SOp v3 op v1' (Const l2))
                                                                                                       else
                                                                                                         default
                                                                                    | _ => default
                                                                                    end
                                                            | Syntax.bopname.sub => match s2 with
                                                                                    | SLit v2 l2 => if andb (eqb v2 v2') (literalFitsInBits true 12 (-l2)) 
                                                                                                       then
                                                                                                         SSeq s1 (SOp v3 Syntax.bopname.add v1' (Const (-l2)))
                                                                                                       else
                                                                                                         default
                                                                                    | _ => default
                                                                                    end
                                                            | _ => default
                                                            end 
                   | _, _ =>  default
                   end
  | _ => s
  end.

