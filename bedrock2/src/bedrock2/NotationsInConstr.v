Require Import Coq.ZArith.BinIntDef.
Require Import coqutil.Macros.subst coqutil.Macros.unique bedrock2.Syntax.

Declare Scope bedrock_var.
Delimit Scope bedrock_var with bedrock_var.

Declare Scope bedrock_expr.
Delimit Scope bedrock_expr with bedrock_expr.
Bind Scope bedrock_expr with expr.
Notation "(uintptr_t) v 'ULL'" := (expr.literal v)
 (at level 1, no associativity, format "(uintptr_t) v 'ULL'") : bedrock_expr.

Notation "*(uint8_t*) e" := (expr.load access_size.one e%bedrock_expr)
  (at level 10, no associativity) : bedrock_expr.
Notation "*(uint16_t*) e" := (expr.load access_size.two e%bedrock_expr)
  (at level 10, no associativity) : bedrock_expr.
Notation "*(uint32_t*) e" := (expr.load access_size.four e%bedrock_expr)
  (at level 10, no associativity) : bedrock_expr.
Notation "*(uintptr_t*) e" := (expr.load access_size.word e%bedrock_expr)
  (at level 10, no associativity) : bedrock_expr.

Declare Scope bedrock_cmd.
Delimit Scope bedrock_cmd with bedrock_cmd.
Bind Scope bedrock_cmd with cmd.
Notation "'/*skip*/'" := cmd.skip
  : bedrock_cmd.
Notation "x = e" := (cmd.set x%bedrock_var e%bedrock_expr)
  : bedrock_cmd.

Notation "*(uint8_t*) ea = ev" := (cmd.store access_size.one ea%bedrock_var ev%bedrock_expr)
  (at level 76, ea at level 60) : bedrock_cmd.
Notation "*(uint16_t*) ea = ev" := (cmd.store access_size.two ea%bedrock_var ev%bedrock_expr)
  (at level 76, ea at level 60) : bedrock_cmd.
Notation "*(uint32_t*) ea = ev" := (cmd.store access_size.four ea%bedrock_var ev%bedrock_expr)
  (at level 76, ea at level 60) : bedrock_cmd.
Notation "*(uintptr_t*) ea = ev" := (cmd.store access_size.word ea%bedrock_var ev%bedrock_expr)
  (at level 76, ea at level 60) : bedrock_cmd.

Notation "c1 ;; c2" := (cmd.seq c1%bedrock_cmd c2%bedrock_cmd)
  (at level 76, right associativity, c2 at level 76, format "'[v' c1 ;; '/' c2 ']'") : bedrock_cmd.
Notation "'if' ( e ) { { c1 } } 'else' { { c2 } }" := (cmd.cond e%bedrock_expr c1%bedrock_cmd c2%bedrock_cmd)
 (at level 76, no associativity, c1 at level 76, c2 at level 76, format "'[v' 'if'  ( e )  { {  '/  ' c1 '/' } }  'else'  { {  '/  ' c2 '/' } } ']'") : bedrock_cmd.
Notation "'if' ( e ) { { c } }" := (cmd.cond e%bedrock_expr c%bedrock_cmd cmd.skip)
 (at level 76, no associativity, c at level 76, format "'[v' 'if'  ( e )  { {  '/  ' c '/' } } ']'") : bedrock_cmd.
Notation "'while' ( e ) { { c } }" := (cmd.while e%bedrock_expr c%bedrock_cmd)
 (at level 76, no associativity, c at level 76, format "'[v' 'while'  ( e )  { {  '/  ' c '/' } } ']'") : bedrock_cmd.

Declare Scope bedrock_func_body.
Delimit Scope bedrock_func_body with bedrock_func_body.
Notation "'require' ( e ) 'else' { { ce } } c" := (cmd.cond e%bedrock_expr c%bedrock_func_body%bedrock_cmd ce%bedrock_cmd)
 (at level 76, right associativity, ce at level 76, c at level 76, format "'[v' 'require'  ( e )  'else'  { { '/  '  ce '/' } } '//' c ']'") : bedrock_func_body.
Notation "c1 ;; c2" := (cmd.seq c1%bedrock_cmd c2%bedrock_func_body%bedrock_cmd)
  (at level 76, right associativity, c2 at level 76, format "'[v' c1 ;; '/' c2 ']'") : bedrock_func_body.
Notation "'while' ( e ) { { c } }" := (cmd.while e%bedrock_expr c%bedrock_cmd)
  (at level 76, no associativity, c at level 76, format "'[v' 'while'  ( e )  { {  '/  ' c '/' } } ']'") : bedrock_func_body.
Notation "'if' ( e ) { { c1 } } 'else' { { c2 } }" := (cmd.cond e%bedrock_expr c1%bedrock_func_body c2%bedrock_func_body)
 (at level 76, no associativity, c1 at level 76, c2 at level 76, format "'[v' 'if'  ( e )  { {  '/  ' c1 '/' } }  'else'  { {  '/  ' c2 '/' } } ']'") : bedrock_func_body.
Notation "'if' ( e ) { { c } }" := (cmd.cond e%bedrock_expr c%bedrock_func_body cmd.skip)
 (at level 76, no associativity, c at level 76, format "'[v' 'if'  ( e )  { {  '/  ' c '/' } } ']'") : bedrock_func_body.

Notation "bedrock_func_body: x" := ((x: cmd)%bedrock_func_body) (at level 10).
Undelimit Scope bedrock_func_body.


Notation "e1 >> e2" := (expr.op bopname.sru e1%bedrock_expr e2%bedrock_expr)
  (at level 32, left associativity) : bedrock_expr.
Notation "e1 !>> e2" := (expr.op bopname.srs e1%bedrock_expr e2%bedrock_expr)
  (at level 32, left associativity) : bedrock_expr.
Notation "e1 << e2" := (expr.op bopname.slu e1%bedrock_expr e2%bedrock_expr)
  (at level 32, left associativity) : bedrock_expr.

Notation "e1 .& e2" := (expr.op bopname.and e1%bedrock_expr e2%bedrock_expr)
  (at level 40, left associativity) : bedrock_expr.

(* same level:   *    *)
(* FIXME: intermediate level for  %  /  *)
Notation "e1 * e2" := (expr.op bopname.mul e1%bedrock_expr e2%bedrock_expr)
  (at level 40, left associativity) : bedrock_expr.

Notation "e1 + e2" := (expr.op bopname.add e1%bedrock_expr e2%bedrock_expr)
  (at level 50, left associativity) : bedrock_expr.
Notation "e1 - e2" := (expr.op bopname.sub e1%bedrock_expr e2%bedrock_expr)
  (at level 50, left associativity) : bedrock_expr.
Notation "e1 .| e2" := (expr.op bopname.or e1%bedrock_expr e2%bedrock_expr)
  (at level 50, left associativity) : bedrock_expr.
Notation "e1 .^ e2" := (expr.op bopname.xor e1%bedrock_expr e2%bedrock_expr)
  (at level 50, left associativity) : bedrock_expr.

Notation "e1 == e2" := (expr.op bopname.eq e1%bedrock_expr e2%bedrock_expr)
  (at level 100, no associativity) : bedrock_expr.
Notation "e1 < e2" := (expr.op bopname.ltu e1%bedrock_expr e2%bedrock_expr)
  : bedrock_expr.
Notation "e1 <. e2" := (expr.op bopname.lts e1%bedrock_expr e2%bedrock_expr)
  (at level 100, no associativity) : bedrock_expr.
