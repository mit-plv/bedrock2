Require Import bedrock2.Macros bedrock2.Syntax.

Require Import Coq.ZArith.BinIntDef Coq.Lists.List Coq.Strings.String.

Delimit Scope bedrock_var with bedrock_var.

Delimit Scope bedrock_expr with bedrock_expr.
Bind Scope bedrock_expr with expr.
Notation "(uintptr_t) v 'ULL'" := (expr.literal v)
 (at level 1, no associativity, format "(uintptr_t) v 'ULL'") : bedrock_expr.

Notation "*(uint8_t*) e" := (expr.load 1 e%bedrock_expr)
  (at level 10, no associativity) : bedrock_expr.
Notation "*(uint16_t*) e" := (expr.load 2 e%bedrock_expr)
  (at level 10, no associativity) : bedrock_expr.
Notation "*(uint32_t*) e" := (expr.load 4 e%bedrock_expr)
  (at level 10, no associativity) : bedrock_expr.
Notation "*(uint64_t*) e" := (expr.load 8 e%bedrock_expr)
  (at level 10, no associativity) : bedrock_expr.

Delimit Scope bedrock_cmd with bedrock_cmd.
Bind Scope bedrock_cmd with cmd.
Notation "'/*skip*/'" := cmd.skip
  : bedrock_cmd.
Notation "x = e" := (cmd.set x%bedrock_var e%bedrock_expr)
  : bedrock_cmd.

Notation "*(uint8_t*) ea = ev" := (cmd.store 1 ea%bedrock_var ev%bedrock_expr)
  (at level 76, ea at level 60) : bedrock_cmd.
Notation "*(uint16_t*) ea = ev" := (cmd.store 2 ea%bedrock_var ev%bedrock_expr)
  (at level 76, ea at level 60) : bedrock_cmd.
Notation "*(uint32_t*) ea = ev" := (cmd.store 4 ea%bedrock_var ev%bedrock_expr)
  (at level 76, ea at level 60) : bedrock_cmd.
Notation "*(uint64_t*) ea = ev" := (cmd.store 8 ea%bedrock_var ev%bedrock_expr)
  (at level 76, ea at level 60) : bedrock_cmd.

Notation "c1 ; c2" := (cmd.seq c1%bedrock_cmd c2%bedrock_cmd)
  (at level 76, right associativity, c2 at level 76, format "'[v' c1 ; '/' c2 ']'") : bedrock_cmd.
Notation "'if' ( e ) { { c1 } } 'else' { { c2 } }" := (cmd.cond e%bedrock_expr c1%bedrock_cmd c2%bedrock_cmd)
 (at level 76, no associativity, c1 at level 76, c2 at level 76, format "'[v' 'if'  ( e )  { {  '/  ' c1 '/' } }  'else'  { {  '/  ' c2 '/' } } ']'") : bedrock_cmd.
Notation "'if' ( e ) { { c } }" := (cmd.cond e%bedrock_expr c%bedrock_cmd cmd.skip)
 (at level 76, no associativity, c at level 76, format "'[v' 'if'  ( e )  { {  '/  ' c '/' } } ']'") : bedrock_cmd.
Notation "'while' ( e ) { { c } }" := (cmd.while e%bedrock_expr c%bedrock_cmd)
 (at level 76, no associativity, c at level 76, format "'[v' 'while'  ( e )  { {  '/  ' c '/' } } ']'") : bedrock_cmd.

Delimit Scope bedrock_func with bedrock_func.
Notation "'require' ( e ) 'else' { { ce } } c" := (cmd.cond e%bedrock_expr c%bedrock_func%bedrock_cmd ce%bedrock_cmd)
 (at level 76, right associativity, ce at level 76, c at level 76, format "'[v' 'require'  ( e )  'else'  { { '/  '  ce '/' } } '//' c ']'") : bedrock_func.
Notation "c1 ; c2" := (cmd.seq c1%bedrock_cmd c2%bedrock_func%bedrock_cmd)
  (at level 76, right associativity, c2 at level 76, format "'[v' c1 ; '/' c2 ']'") : bedrock_func.
Notation "'while' ( e ) { { c } }" := (cmd.while e%bedrock_expr c%bedrock_cmd)
  (at level 76, no associativity, c at level 76, format "'[v' 'while'  ( e )  { {  '/  ' c '/' } } ']'") : bedrock_func.
Notation "'if' ( e ) { { c1 } } 'else' { { c2 } }" := (cmd.cond e%bedrock_expr c1%bedrock_func c2%bedrock_func)
 (at level 76, no associativity, c1 at level 76, c2 at level 76, format "'[v' 'if'  ( e )  { {  '/  ' c1 '/' } }  'else'  { {  '/  ' c2 '/' } } ']'") : bedrock_func.
Notation "'if' ( e ) { { c } }" := (cmd.cond e%bedrock_expr c%bedrock_func cmd.skip)
 (at level 76, no associativity, c at level 76, format "'[v' 'if'  ( e )  { {  '/  ' c '/' } } ']'") : bedrock_func.

Definition bedrock_func {p} (x:@cmd p) := x.
Arguments bedrock_func {_} _%bedrock_func.
Undelimit Scope bedrock_func.

Require Import bedrock2.BasicALU bedrock2.Structs.

(* record field access *)
Notation "e 'as' t *> a '!' .. '!' c" := (let '(ofs, sz) := scalar (t%list%string, (cons a%string .. (cons c%string nil) .. )) (rlookup (cons a%string .. (cons c%string nil) .. ) t%list%string) in (expr.load sz (expr.op bop_add e (expr.literal ofs))))
  (at level 76, a at level 60, c at level 60) : bedrock_expr.
Notation "e 'as' t *> a '!' .. '!' c = rhs" := (let '(ofs, sz) := scalar (t%list%string, (cons a%string .. (cons c%string nil) .. )) (rlookup (cons a%string .. (cons c%string nil) .. ) t%list%string) in (cmd.store sz (expr.op bop_add e (expr.literal ofs)) rhs))
  (at level 76, a at level 60, c at level 60) : bedrock_cmd.

Notation "'&field' a '!' .. '!' c 'of' t 'at' e" := (let '(ofs, _) := scalar (t%list%string, (cons a%string .. (cons c%string nil) .. )) (rlookup (cons a%string .. (cons c%string nil) .. ) t%list%string) in ((expr.op bop_add e (expr.literal ofs))))
  (at level 76, t at level 60, e at level 60, a at level 60, c at level 60) : bedrock_expr.
Notation "'field' a '!' .. '!' c 'of' t 'at' e  = rhs" := (let '(ofs, sz) := scalar (t%list%string, (cons a%string .. (cons c%string nil) .. )) (rlookup (cons a%string .. (cons c%string nil) .. ) t%list%string) in (cmd.store sz (expr.op bop_add e (expr.literal ofs)) rhs))
  (at level 76, t at level 60, e at level 60, a at level 60, c at level 60) : bedrock_cmd.

(*
Notation "s 'at' e '=' rhs" := (SStore s e%bedrock_expr rhs%bedrock_expr)
(at level 76, e at level 60) : bedrock_cmd.
 *)

Notation "e1 + e2" := (expr.op bop_add e1%bedrock_expr e2%bedrock_expr)
  : bedrock_expr.
Notation "e1 - e2" := (expr.op bop_sub e1%bedrock_expr e2%bedrock_expr)
  : bedrock_expr.
Notation "e1 == e2" := (expr.op bop_eq e1%bedrock_expr e2%bedrock_expr)
  (at level 100, no associativity) : bedrock_expr.
Notation "e1 < e2" := (expr.op bop_ltu e1%bedrock_expr e2%bedrock_expr)
  : bedrock_expr.
Notation "e1 <. e2" := (expr.op bop_lts e1%bedrock_expr e2%bedrock_expr)
  (at level 100, no associativity) : bedrock_expr.
Notation "e1 & e2" := (expr.op bop_and e1%bedrock_expr e2%bedrock_expr)
  (at level 40, no associativity) : bedrock_expr.
Notation "e1 >> e2" := (expr.op bop_sru e1%bedrock_expr e2%bedrock_expr)
  (at level 60, no associativity) : bedrock_expr.
Notation "e1 >>. e2" := (expr.op bop_srs e1%bedrock_expr e2%bedrock_expr)
  (at level 60, no associativity) : bedrock_expr.
Notation "e1 << e2" := (expr.op bop_slu e1%bedrock_expr e2%bedrock_expr)
  (at level 60, no associativity) : bedrock_expr.