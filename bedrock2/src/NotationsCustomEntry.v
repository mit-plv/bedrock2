Require Import Coq.ZArith.BinIntDef.
Require Import coqutil.Macros.subst coqutil.Macros.unique bedrock2.Syntax.

(** Grammar for expressions *)

Import bopname.
Declare Custom Entry bedrock_expr.
Notation "bedrock_expr:( e )"   := e   (e custom bedrock_expr,
                                        format "'bedrock_expr:(' e ')'").
Notation "constr:( e )"         := e   (in custom bedrock_expr, e constr,
                                        format "'constr:(' e ')'").
Notation  "( e )" := e                 (in custom bedrock_expr at level 0).
Notation "x" := x (in custom bedrock_expr at level 0, x ident).

Infix  "<<" := (expr.op slu)  (in custom bedrock_expr at level 3, left associativity). (* DRAFT level *)
Infix  ">>" := (expr.op sru)  (in custom bedrock_expr at level 3, left associativity). (* DRAFT level *)
Infix ".>>" := (expr.op srs)  (in custom bedrock_expr at level 3, left associativity). (* DRAFT *)

Infix "*"   := (expr.op mul)  (in custom bedrock_expr at level 4, left associativity).

(* Infix "/" := (expr.op div) (in custom bedrock_expr at level 5, left associativity). (* DRAFT level *) *)

Infix "+"   := (expr.op add)  (in custom bedrock_expr at level 6, left associativity).
Infix "-"   := (expr.op sub)  (in custom bedrock_expr at level 6, left associativity).

Infix "&"   := (expr.op and)  (in custom bedrock_expr at level 7, left associativity). 

Infix "^"   := (expr.op xor)  (in custom bedrock_expr at level 8, left associativity). 

Infix "|"   := (expr.op or)   (in custom bedrock_expr at level 9, left associativity). 

Infix  "<"  := (expr.op ltu)  (in custom bedrock_expr at level 10, no associativity).
Infix ".<"  := (expr.op lts)  (in custom bedrock_expr at level 10, no associativity). (* DRAFT *)
Infix "=="  := (expr.op lts)  (in custom bedrock_expr at level 10, no associativity).

(* DRAFT *)
Notation "load1( a )" := (expr.load access_size.one a)
                              (in custom bedrock_expr at level 0, a custom bedrock_expr).
Notation "load2( a )" := (expr.load access_size.two a)
                              (in custom bedrock_expr at level 0, a custom bedrock_expr).
Notation "load4( a )" := (expr.load access_size.four a)
                              (in custom bedrock_expr at level 0, a custom bedrock_expr).
Notation  "load( a )" := (expr.load access_size.word a)
                              (in custom bedrock_expr at level 0, a custom bedrock_expr).

(** Grammar for commands *)

Import cmd.
Declare Custom Entry bedrock_cmd.
Delimit Scope bedrock_nontail with bedrock_nontail.
Notation "bedrock_cmd:( c )"   := c   (c custom bedrock_cmd at level 0,
                                       format "'bedrock_cmd:(' c ')'").
Notation "constr:( c )"        := c   (in custom bedrock_cmd, c constr,
                                       format "'constr:(' c ')'").
Notation  "{ c }" := c                 (in custom bedrock_cmd at level 0).
Notation "x" := x (in custom bedrock_cmd at level 0, x ident).

Notation "c1 ; c2" := (seq c1%bedrock_nontail c2) (in custom bedrock_cmd at level 0, right associativity,
                                   format "'[v' c1 ; '/' c2 ']'").
Notation "'if' e { c1 } 'else' { c2 }" := (cond e c1 c2)
  (in custom bedrock_cmd at level 0, no associativity, e custom bedrock_expr, c1 at level 0, c2 at level 0,
  format "'[v' 'if'  e  {  '/  ' c1 '/' }  'else'  { '/  ' c2 '/' } ']'").
Notation "'if' e { c }" := (cond e c skip)
  (in custom bedrock_cmd at level 0, no associativity, e custom bedrock_expr, c at level 0,
  format "'[v' 'if'  e  {  '/  ' c '/' } ']'").
Notation "'while' e { c }" := (while e c%bedrock_nontail)
  (in custom bedrock_cmd at level 0, no associativity, e custom bedrock_expr, c at level 0,
  format "'[v' 'while'  e  {  '/  ' c '/' } ']'").

(* COQBUG(9517) *)
Notation "{ x = e }" := (set x e) (in custom bedrock_cmd at level 0, x constr at level 0, e custom bedrock_expr).
(* DRAFT: *)
Notation "/*skip*/" := skip (in custom bedrock_cmd).
Notation "store1( a , v )" := (store access_size.one a v)
                              (in custom bedrock_cmd at level 0, a custom bedrock_expr, v custom bedrock_expr).
Notation "store2( a , v )" := (store access_size.two a v)
                              (in custom bedrock_cmd at level 0, a custom bedrock_expr, v custom bedrock_expr).
Notation "store4( a , v )" := (store access_size.four a v)
                              (in custom bedrock_cmd at level 0, a custom bedrock_expr, v custom bedrock_expr).
Notation  "store( a , v )" := (store access_size.word a v)
                              (in custom bedrock_cmd at level 0, a custom bedrock_expr, v custom bedrock_expr).

(* require statements are only allowed at tail-call positions *)

Delimit Scope bedrock_tail with bedrock_tail.
Notation "bedrock_func_body:( c )"   := (c%bedrock_tail) (c custom bedrock_cmd at level 0,
                                                          format "'bedrock_func_body:(' c ')'").
Definition require_is_not_available_inside_conditionals_and_loops := I.
Notation "'require' e 'else' { c1 } ; c2" := (cond e c2 c1)
  (in custom bedrock_cmd at level 1, no associativity, e custom bedrock_expr, c1 at level 0, c2 at level 0,
  format "'[v' 'require'  e  'else'  {  '/  ' c1 '/' } ; '//' c2 ']'") : bedrock_tail.
Notation "'require' e 'else' { c1 } ; c2" := (require_is_not_available_inside_conditionals_and_loops)
  (only parsing, in custom bedrock_cmd at level 1, no associativity, e custom bedrock_expr, c1 at level 0, c2 at level 0,
  format "'[v' 'require'  e  'else'  {  '/  ' c1 '/' } ; '//' c2 ']'") : bedrock_nontail.
Undelimit Scope bedrock_tail.
Undelimit Scope bedrock_nontail.


Module test.
  Notation "1" := (expr.literal 1) (in custom bedrock_expr).
  
  Goal True.
  assert (p : parameters) by admit.
  epose (fun x => bedrock_cmd:( store1(1<<(1+1+1), 1+1) ; if 1 { store1(1,1) } ; { _ = 1 } )).
  epose (fun W a b e x y => bedrock_func_body:(
    require (load(1) ^ constr:(expr.literal 231321) ) else { _ };
    require (1 ^ load4(1+1+1+load(1))) else { _ };
    { a = (1+1) } ;
    require (1 ^ 1) else { _ };
    store1(e, load2(1)+load4(1)+load1(load(1))) ;
    store2(e, 1+1+1);
    store4(e, 1+1+1) ;
    store(e, load(load(load(1))));
    require (1 ^ 1) else { _ };
    if (W+1<<(1+1)*(1+1) ^ (1+1+1)) {
      x
    } else {
      while (W+1<<(1+1)*(1+1) ^ (1+1+1)) {
        store(1,1)
      }
    }
  )).

  let lhs := open_constr:( bedrock_func_body:(
    require 1 else { store1(1,1) } ;
    require 1 else { store2(1,1) } ;
    store4(1,1)
  )) in
  let rhs := open_constr:( bedrock_func_body:(
    if 1 {
      if 1 {
        store4(1,1)
      }
      else {
        store2(1,1)
      }
    }
    else {
      store1(1,1)
    }
  )) in
  assert (lhs = rhs) by exact eq_refl.

  epose bedrock_func_body:(
      if (1<<(1+1)*(1+1) ^ (1+1+1)) {
          require (1 ^ 1) else { _ }; _
      }).

  epose bedrock_func_body:(
      if (1<<(1+1)*(1+1) ^ (1+1+1)) {
             _ } else {
          require (1 ^ 1) else { _ }; _
      }).

  epose bedrock_func_body:(
   require (1 ^ 1) else {
       require (1 ^ 1) else { _ };
       _
   };
    _
  ).

  assert_fails (epose bedrock_func_body:(
    if (1) { require (1 ^ 1) else { _ }; _  } ;
    { _ = _}
  )).

  assert_fails (epose bedrock_func_body:(
    if (1) { require (1 ^ 1) else { _ }; _  }
    else { _ };
    { _ = _}
  )).

  assert_fails (epose bedrock_func_body:(
    if (1) { _  } else { require (1 ^ 1) else { _ }; _ };
    { _ = _}
  )).
  
  assert_fails (epose bedrock_func_body:(
    while (1) { require (1 ^ 1) else { _ }; _ };
    { _ = _}
  )).

  assert_fails (epose bedrock_func_body:(
    while (1) { require (1 ^ 1) else { _ }; _ }
  )).
  Abort.
End test.