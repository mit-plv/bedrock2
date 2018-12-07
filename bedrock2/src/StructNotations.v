Require Import coqutil.subst coqutil.unique bedrock2.Syntax.
Require Import bedrock2.BasicALU bedrock2.Structs.
Require Import Coq.ZArith.BinIntDef Coq.Lists.List Coq.Strings.String.


Definition require_scalar (t : type)
: match t with
  | Bytes _ => Z
  | _ => NotAScalar
  end :=
  match t as t return match t with
                      | Bytes _ => Z
                      | _ => NotAScalar
                      end
  with
  | Bytes n => n
  | t => mk_NotAScalar t
  end.

Definition rlookup_scalar {par : parameters} {balu : operations}
           {T : Set} (ok : Z -> expr.expr -> T)
           (t : type) (base : expr.expr) (p : path expr.expr)
: match @gen_access par bop_add bop_mul base t p with
  | inl err => _
  | inr (Bytes _, _) => T
  | inr _ => NotAScalar
  end :=
  match @gen_access par bop_add bop_mul base t p as z
        return match z with
               | inl err => _
               | inr (Bytes _, _) => T
               | inr _ => NotAScalar
               end
  with
  | inl err => err
  | inr (t,e) => match t with
                | Bytes sz => ok sz e
                | _ => mk_NotAScalar t
                end
  end.

Require Export bedrock2.NotationsInConstr.

(* record field access *)

Notation "e 'as' t *> a '!' .. '!' c" :=
  (@rlookup_scalar _ _ expr.expr
            (fun sz exp => expr.load sz exp)
            t%list%string e%bedrock_expr
            (cons (Field a%string) .. (cons (Field c%string) nil) .. ))
  (at level 60, a at level 25, c at level 25) : bedrock_expr.
Notation "e 'as' t *> a '!' .. '!' c = rhs" :=
  (@rlookup_scalar _ _ cmd.cmd
            (fun sz exp => cmd.store sz exp rhs)
            t%list%string e%bedrock_expr
            (cons (Field a%string) .. (cons (Field c%string) nil) .. ))
  (at level 76, a at level 60, c at level 60) : bedrock_cmd.

Notation "'&field' a '!' .. '!' c 'of' t 'at' e" :=
  (@rlookup_scalar _ _ expr.expr
            (fun _ exp => exp)
            t%list%string e%bedrock_expr (cons (Field a%string) .. (cons (Field c%string) nil) .. ))
  (at level 60, t at level 25, e at level 60, a at level 25, c at level 25) : bedrock_expr.
Notation "'field' a '!' .. '!' c 'of' t 'at' e  = rhs" :=
  (@rlookup_scalar _ _ cmd.cmd
            (fun sz exp => cmd.store sz exp rhs)
            t%list%string e%bedrock_expr
            (cons (Field a%string) .. (cons (Field c%string) nil) .. ))
  (at level 76, t at level 60, e at level 60, a at level 60, c at level 60) : bedrock_cmd.

(*
Notation "s 'at' e '=' rhs" := (SStore s e%bedrock_expr rhs%bedrock_expr)
(at level TODO, e at level 60) : bedrock_cmd.
 *)
