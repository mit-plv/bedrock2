Require Import Coq.ZArith.BinIntDef Coq.Strings.String.
Require Import coqutil.Macros.subst coqutil.Macros.unique bedrock2.Syntax.
Require Import coqutil.Macros.ident_to_string.

Export Coq.Strings.String.StringSyntax.
Export bedrock2.Syntax.Coercions.
Number Notation BinInt.Z BinInt.Z.of_num_int BinInt.Z.to_num_int : Z_scope.

(** Grammar for expressions *)
Import bopname.
Declare Custom Entry bedrock_expr.
Notation "bedrock_expr:( e )" := e (e custom bedrock_expr, format "'bedrock_expr:(' e ')'").
Notation "coq:( e )"          := e (in custom bedrock_expr, e constr, format "'coq:(' e ')'").
Notation "$ e"                := e%string%Z (in custom bedrock_expr at level 0, e constr at level 0, format "'$' e").
Notation  "( e )" := e             (in custom bedrock_expr).
Notation "x" := (ident_to_string! x) (in custom bedrock_expr, x ident, only parsing).

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
Infix "=="  := (expr.op  eq)  (in custom bedrock_expr at level 10, no associativity).

(* DRAFT *)
(* TODO(after dropping Coq 8.14): split "load(" into 'load' '(' *)
Notation "load1( a )" := (expr.load access_size.one a)
  (in custom bedrock_expr, a custom bedrock_expr, format "load1( a )").
Notation "load2( a )" := (expr.load access_size.two a)
  (in custom bedrock_expr, a custom bedrock_expr, format "load2( a )").
Notation "load4( a )" := (expr.load access_size.four a)
  (in custom bedrock_expr, a custom bedrock_expr, format "load4( a )").
Notation  "load( a )" := (expr.load access_size.word a)
  (in custom bedrock_expr, a custom bedrock_expr, format "load( a )").

(** Grammar for commands *)

Import cmd.
Declare Custom Entry bedrock_cmd.
Declare Scope bedrock_nontail.
Delimit Scope bedrock_nontail with bedrock_nontail.
Notation "bedrock_cmd:( c )" := c (c custom bedrock_cmd, format "'bedrock_cmd:(' '/  ' c '/ ' ')'").
Notation "coq:( c )"         := c (in custom bedrock_cmd, c constr, format "'coq:(' c ')'").
Notation "$ c"               := c (in custom bedrock_cmd at level 0, c constr at level 0, format "'$' c").
Notation "{ c }" := c             (in custom bedrock_cmd, c custom bedrock_cmd).

(* must be at level 1 or higher to arguments make sense, see coq/coq#15336 *)
Notation "c1 ; c2" := (seq c1%bedrock_nontail c2)
  (in custom bedrock_cmd at level 1, right associativity, format "'[v' c1 ; '/' c2 ']'").

(* the notations that start with a word must be at level 0 to avoid making that
   word into a global keyword, see coq/coq#15349 coq/coq#14562 *)
Notation "'while' e { c }" := (while e c%bedrock_nontail)
  (in custom bedrock_cmd at level 0, e custom bedrock_expr, format "'[v' 'while'  e  {  '/  ' c '/' } ']'").

Notation "'if' e { c1 } 'else' c2"     := (cond e c1 c2)    (in custom bedrock_cmd at level 0,
  e custom bedrock_expr at level 1, c2 at level 0,
  format "'[v' 'if'  e  {  '/  ' c1 '/' }  'else'  c2 ']'").
Notation "'if' '!' e { c1 } 'else' c2" := (cond e c2 c1)    (in custom bedrock_cmd at level 0,
  e custom bedrock_expr at level 1, c2 at level 0,
  format "'[v' 'if'  '!' e  {  '/  ' c1 '/' }  'else'  c2 ']'").
Notation "'if' e { c1 }"               := (cond e c1 skip)  (in custom bedrock_cmd at level 0,
  e custom bedrock_expr at level 1, format "'[v' 'if'  e  {  '/  ' c1 '/' } ']'").
Notation "'if' '!' e { c1 }"           := (cond e skip c1)  (in custom bedrock_cmd at level 0,
  e custom bedrock_expr at level 1, format "'[v' 'if'  '!' e   {  '/  ' c1 '/' } ']'").

(* DRAFT: *)
Notation "'stackalloc' z 'as' x ; c" := (stackalloc (ident_to_string! x) z c)
  (in custom bedrock_cmd at level 0,  x ident, z constr, c at level 999,
   format "'[v' 'stackalloc'  z  as  x ;  '//' c ']'").
Notation "'stackalloc' z 'as' $ x ; c" := (cmd.stackalloc x z c)
  (in custom bedrock_cmd at level 0,  x constr at level 0, z constr, c at level 999,
   format "'[v' 'stackalloc'  z  as  '$' x ;  '//' c ']'").

Notation "x = e" := (set (ident_to_string! x) e) (in custom bedrock_cmd, x ident, only parsing, e custom bedrock_expr).
Notation "$ x = e" := (set x%string e) (in custom bedrock_cmd at level 0, x constr at level 0, e custom bedrock_expr, format "'$' x  =  e").
(* DRAFT: *)
Notation "/*skip*/" := skip (in custom bedrock_cmd).
(* TODO(after dropping Coq 8.14): split "load(" into 'load' '(' *)
Notation "store1( a , v )" := (store access_size.one a v)   (in custom bedrock_cmd,
  a custom bedrock_expr, v custom bedrock_expr, format "store1( a ,  v )").
Notation "store2( a , v )" := (store access_size.two a v)   (in custom bedrock_cmd,
  a custom bedrock_expr , v custom bedrock_expr,  format "store2( a ,  v )").
Notation "store4( a , v )" := (store access_size.four a v)  (in custom bedrock_cmd,
  a custom bedrock_expr , v custom bedrock_expr, format "store4( a ,  v )").
Notation  "store( a , v )" := (store access_size.word a v)  (in custom bedrock_cmd,
  a custom bedrock_expr , v custom bedrock_expr, format "store( a ,  v )").

Declare Custom Entry bedrock_ident.
Notation "x" := (ident_to_string! x) (in custom bedrock_ident, x ident, only parsing).
Notation "$ x" := x (in custom bedrock_ident at level 0, x constr at level 0, format "'$' x").

Declare Custom Entry bedrock_call_lhs.
(* COQBUG(15335): making this "only parsing" does not work *)
(* Notation "bedrock_call_lhs:( e )"  := e  (e custom bedrock_call_lhs, format "'bedrock_call_lhs:(' e ')'", only parsing). *)
Notation "coq:( e )"               := e  (in custom bedrock_call_lhs, e constr, format "'coq:(' e ')'").
Notation "x" := (@cons String.string x nil) (in custom bedrock_call_lhs at level 0, x custom bedrock_ident).
Notation "x , y , .. , z" := (@cons String.string x (@cons String.string y .. (@cons String.string z (@nil String.string)) ..))
  (in custom bedrock_call_lhs at level 0, x custom bedrock_ident, y custom bedrock_ident, z custom bedrock_ident).

Declare Custom Entry bedrock_args.
(* COQBUG(15335): making this "only parsing" does not work *)
(* Notation "bedrock_args:( e )"   := e  (e custom bedrock_args, format "'bedrock_args:(' e ')'", only parsing). *)
Notation "coq:( e )" := e  (in custom bedrock_args, e constr, format "'coq:(' e ')'").
Notation "( )" := (@nil expr) (in custom bedrock_args).
Notation "()" := (@nil expr) (in custom bedrock_args).
Notation "( x )" := (@cons expr x (@nil expr)) (in custom bedrock_args at level 0, x custom bedrock_expr ).
Notation "( x , y , .. , z )" := (@cons expr x (@cons expr y .. (@cons expr z (@nil expr)) ..))
  (in custom bedrock_args at level 0, x custom bedrock_expr , y custom bedrock_expr , z custom bedrock_expr ).

Notation "io! lhs = f args" :=  (interact lhs f args) (in custom bedrock_cmd at level 0, lhs custom bedrock_call_lhs , f custom bedrock_ident, args custom bedrock_args ).
Notation "output! f args" :=  (interact nil f args) (in custom bedrock_cmd at level 0, f custom bedrock_ident, args custom bedrock_args ).
Notation "unpack! lhs = f args" :=  (call lhs f args) (in custom bedrock_cmd at level 0, lhs custom bedrock_call_lhs , f custom bedrock_ident, args custom bedrock_args ).
Notation "( lhs ) = f args" :=  (call lhs f args) (in custom bedrock_cmd at level 0, lhs custom bedrock_call_lhs , f custom bedrock_ident, args custom bedrock_args ,
  format "'(' lhs ')'  =  f args").
Notation "f args" :=  (call nil (ident_to_string! f) args) (in custom bedrock_cmd at level 0,
  f ident, args custom bedrock_args, format "f args").
Notation "$ f args" :=  (call nil f args) (in custom bedrock_cmd at level 0,
  f constr at level 0, args custom bedrock_args, format "'$' f args").

Declare Scope bedrock_tail.
Delimit Scope bedrock_tail with bedrock_tail.
(* COQBUG(15335): making this "only parsing" does not work *)
Notation "bedrock_func_body:( c )"   := (c%bedrock_tail) (c custom bedrock_cmd,
  format "'bedrock_func_body:(' '/  ' c '/ ' ')'").
Definition require_is_not_available_inside_conditionals_and_loops := I.
Notation "'require' e ; c2" := (cond e c2 skip) (in custom bedrock_cmd at level 0,
  e custom bedrock_expr at level 1, c2 at level 999, format "'[v' 'require'  e ; '//' c2 ']'") : bedrock_tail.
Notation "'require' '!' e ; c2" := (cond e skip c2) (in custom bedrock_cmd at level 0,
  e custom bedrock_expr at level 1, c2 at level 999, format "'[v' 'require' '!'  e ; '//' c2 ']'") : bedrock_tail.
Notation "'require' e 'else' { c1 } ; c2" := (cond e c2 c1) (in custom bedrock_cmd at level 0,
  e custom bedrock_expr at level 1, c2 at level 999,
  only parsing, format "'[v' 'require'  e  'else'  {  '/  ' c1 '/' } ; '//' c2 ']'") : bedrock_tail.
Notation "'require' '!' e 'else' { c1 } ; c2" := (cond e c1 c2) (in custom bedrock_cmd at level 0,
  e custom bedrock_expr at level 1, c2 at level 999,
  only parsing, format "'[v' 'require' '!'  e  'else'  {  '/  ' c1 '/' } ; '//' c2 ']'") : bedrock_tail.
Notation "'require' e 'else' { c1 } ; c2" := (require_is_not_available_inside_conditionals_and_loops)
  (in custom bedrock_cmd at level 0, e custom bedrock_expr at level 1, c2 at level 999,
  only parsing, format "'[v' 'require'  e  'else'  {  '/  ' c1 '/' } ; '//' c2 ']'") : bedrock_nontail.
Notation "'require' '!' e 'else' { c1 } ; c2" := (require_is_not_available_inside_conditionals_and_loops)
  (in custom bedrock_cmd at level 0, e custom bedrock_expr at level 1, c2 at level 999,
  only parsing, format "'[v' 'require' '!'  e  'else'  {  '/  ' c1 '/' } ; '//' c2 ']'") : bedrock_nontail.
Undelimit Scope bedrock_tail.
Undelimit Scope bedrock_nontail.


Module test.
  Local Notation "1" := (bedrock_expr:($1)) (in custom bedrock_expr at level 0).
  Local Notation "2" := (bedrock_expr:($2)) (in custom bedrock_expr at level 0).

  Local Open Scope Z_scope.
  Local Open Scope string_scope.

  Goal True.

  pose (cons "a" (cons "b" nil)).
  pose (cons (expr.var "a") (cons (expr.var "b") nil)).
  pose (cons (expr.literal 5) (cons (expr.literal 8) nil)).

  (* TODO(after dropping 8.14): test the following:
  pose (fun while : nat => while=while).
  pose (fun stackalloc : nat => stackalloc=stackalloc).
  pose (fun require : nat => require=require).
  *)

  pose (seq skip (seq bedrock_cmd:(if 1 { /*skip*/ } else { /*skip*/ } ) (seq skip skip))).
  pose (seq (seq skip skip) (seq skip skip)).
  pose (bedrock_cmd:(/*skip*/;while 1 { /*skip*/ } ; /*skip*/)).

  epose (bedrock_expr:( $"x" + $1 )).
  epose (bedrock_cmd:( $"x" = $1 )).

  epose (bedrock_expr:( x + $1 )).
  epose (bedrock_cmd:( x = $1 )).

  epose (bedrock_cmd:( store1(1<<(1+1+1), 1+1) ; if 1 { store1(1,1) } ; x = 1 )).
  epose (bedrock_cmd:( if 1 { x = (1);  x = (a) } )).
  epose (bedrock_cmd:( if 1 { x = 1;  x = a } )).
  epose (bedrock_cmd:( if 1 { x = (1);  y = (a) } )).
  epose (bedrock_cmd:( a () )).
  epose (bedrock_cmd:( a ( ) )).
  epose (bedrock_cmd:( a (1+1) )).
  epose (bedrock_cmd:( a (1+1 , 1+1,1 ) )).
  epose (bedrock_cmd:( a (1+1 , 1+1,1, 1 ) )).
  epose (bedrock_cmd:( a (1+1 , 1+1,1, 1 ,1 ) )).
  epose (bedrock_cmd:( a (1+1 , 1+1,1, 1,1,1 ) )).
  epose (bedrock_cmd:( unpack! a,b,c,d = f ( 1 + 1 , 1 + 1 ) )).
  epose (bedrock_cmd:( (a,b,c,d) = f ( 1 + 1 , 1 + 1 ) )).
  epose (bedrock_cmd:( (a,b) = f ( 1 + 1 , 1 + 1 ) )).
  epose (bedrock_cmd:( (a) = f ( 1 + 1 , 1 + 1 ) )).
  epose (bedrock_cmd:( unpack! a = f ( 1 + 1 , 1 + 1 ) ; a = (1) )).
  epose (bedrock_cmd:( if coq:(_) { coq:(_) } else if coq:(_) { coq:(_) } )).

  epose (bedrock_cmd:(if 1 { a = 1 + 1 } )).
  epose (bedrock_cmd:(if !1 { a = 1 + 1 } )).

  epose (bedrock_cmd:(
    if 1 { a = 1 } else if   1 { a = 1 + 1 } )).
  epose (bedrock_cmd:(
    if 1 { a = 1 } else if ! 1 { a = 1 + 1 } )).

  epose (bedrock_cmd:(
      if coq:(_) { coq:(_) }
      else if coq:(_) { coq:(_) }
      else if coq:(_) { coq:(_) }
      else if coq:(_) { coq:(_) };
      coq:(_))).

  epose bedrock_func_body:( require coq:(_) else { coq:(_) } ; coq:(_) ).
  epose bedrock_func_body:( require coq:(_) ; coq:(_) ).

  epose bedrock_func_body:(
   require (1 ^ 1) else {
       require (1 ^ 1) else { coq:(_) };
       coq:(_)
   };
    coq:(_)
  ).

  assert_fails (epose bedrock_func_body:(
    if (1) { require (1 ^ 1) else { coq:(_) }; coq:(_)  } ;
    { x = (coq:(_))}
  )).

  assert_fails (epose bedrock_func_body:(
    if (1) { require !(1 ^ 1) else { coq:(_) }; coq:(_)  }
    else { coq:(_) };
    x = (coq:(_))
  )).

  assert_fails (epose bedrock_func_body:(
    if (1) { coq:(_)  } else { require (1 ^ 1) else { coq:(_) }; coq:(_) };
    { x = (coq:(_))}
  )).

  assert_fails (epose bedrock_func_body:(
    while (1) { require (1 ^ 1) else { coq:(_) }; coq:(_) };
    { x = (coq:(_))}
  )).

  assert_fails (epose bedrock_func_body:(
    while (1) { require (1 ^ 1) else { coq:(_) }; x = (coq:(_)) }
  )).

  let lhs := open_constr:( bedrock_func_body:(
    require 1 else { store1(1,1) } ;
    require !1 else { store2(1,1) } ;
    store4(2,1);
    store4(2,1)
  )) in
  let rhs := open_constr:( bedrock_func_body:(
    if 1 {
      if !1 {
        store4(2,1);
        store4(2,1)
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

  epose (bedrock_func_body:(stackalloc 64 as x ; /*skip*/ )).
  epose (fun n => bedrock_func_body:(stackalloc n as x ; /*skip*/ )).
  epose (fun n => bedrock_func_body:( {stackalloc n as x ; /*skip*/ } ; /*skip*/ )).

  epose (bedrock_func_body:(
    stackalloc 64 as b ;
    require (load(1) ^ coq:(expr.literal 231321) ) else { /*skip*/ };
    require (1 ^ load4(1+1+1+load(1))) else { /*skip*/ };
    { a = (1+1 == 1) } ;
    require (1 ^ 1) else { /*skip*/ };
    store1(e, load2(1)+load4(1)+load1(load(1))) ;
    store2(e, 1+1+1);
    store4(e, 1+1+1) ;
    store(e, load(load(load(1))));
    require (1 ^ 1) else { /*skip*/ };
    if (W+1<<(1+1)-(1+1) ^ (1+1+1)) {
      a = x
    } else {
      while (W+1<<(1+1)-(1+1) ^ (1+1+1)) {
        stackalloc 64 as b;
        stackalloc 64 as $"B";
        a = (1);
        x = a;
        unpack! x = f(1,W,1, 1,1,1);
        unpack! x,a = f(1,W,1, 1,1,1);
        io! a, x = read(1,W,1, 1,1,1);
        io! a = read(1, 1);
        output! write(1,W,1, 1,1,1);
        store(1,1)
      }
    }
  )).

  epose bedrock_func_body:($"write" ($1, $"W", $1, $1, $1, $1)).

  epose bedrock_func_body:(
  stackalloc 64 as $"b";
  if (load($1) ^ $231321) {
    if ($1 ^ load4($1 + $1 + $1 + load($1))) {
      $"a" = $1 + $1 == $1;
      if ($1 ^ $1) {
        store1($"e", load2($1) + load4($1) + load1(load($1)));
        store2($"e", $1 + $1 + $1);
        store4($"e", $1 + $1 + $1);
        store($"e", load(load(load($1))));
        if ($1 ^ $1) {
          if !($"W" + $1 << ($1 + $1) - ($1 + $1) ^ $1 + $1 + $1) {
            while $"W" + $1 << ($1 + $1) - ($1 + $1) ^ $1 + $1 + $1 {
              stackalloc 64 as $"b";
              stackalloc 64 as $"B";
              $"a" = $1;
              $"x" = $"a";
              ($"x") = $"f"($1, $"W", $1, $1, $1, $1);
              ($"x", $"a") = $"f"($1, $"W", $1, $1, $1, $1);
              io! $"a", $"x" = $"read" ($1, $"W", $1, $1, $1, $1);
              io! $"a" = $"read" ($1, $1);
              output! $"write" ($1, $"W", $1, $1, $1, $1);
              store($1, $1)
            }
          } else $"a" = $"x"
        }
      }
    }
  }).

  epose bedrock_func_body:(
    $_
  ).

  epose bedrock_func_body:(
    x = $4 + x
  ).

  epose bedrock_func_body:(
    $"x" = $4 + $"x"
  ).
  epose bedrock_func_body:(
    $("x" ++ "y") = $(Z.div 4 2) + $("x" ++ "y")
  ).
  epose (bedrock_func_body:($"x" = $4)).

  let x := constr:(1+1) in pose x.

  epose (bedrock_cmd:( if 1 { x = (1<<a);  x = (a>>1) } )).

  Abort.
End test.
