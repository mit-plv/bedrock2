Require Import Coq.setoid_ring.InitialRing. (* for isZcst *)
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import bedrock2.Syntax.
Require Import LiveVerif.LiveExpr.
Require Import LiveVerif.LiveSnippet.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.reference_to_string.
(* TODO consolidate with variants in coqutil: *)
Require Import LiveVerif.string_to_ident.
Require Import bedrock2.ident_to_string.

Require Import Ltac2.Ltac2.

Ltac2 exact_basename_string_of_ref_constr(c: constr) :=
  let ref := reference_of_constr c in
  let s := ident_to_coq (List.last (Env.path ref)) in
  exact $s.

Ltac exact_basename_string_of_ref_constr :=
  ltac2:(c |- exact_basename_string_of_ref_constr (Option.get (Ltac1.to_constr c))).

Declare Custom Entry bound_name_or_literal.
Notation "x" :=
  (match x with
   | _ => ltac:(lazymatch type of x with
                | Z => exact x
                | _ => let h := head x in (* strip off (implicit) args *)
                       exact_basename_string_of_ref_constr h
                end)
   end)
  (in custom bound_name_or_literal at level 0, x constr at level 0, only parsing).

Declare Custom Entry binder_name.
Notation "x" := (ident_to_string x)
  (in custom binder_name at level 0, x constr at level 0, only parsing).

Declare Custom Entry bound_name_or_literal_list.
Notation "x" := (cons x nil)
  (in custom bound_name_or_literal_list at level 0, x custom bound_name_or_literal at level 0, only parsing).
Notation "h , t" := (cons h t)
  (in custom bound_name_or_literal_list at level 0,
   h custom bound_name_or_literal at level 0,
   t custom bound_name_or_literal_list at level 0,
   only parsing).

Declare Custom Entry live_expr.

Notation "'live_expr:(' e ')'" := e
  (e custom live_expr at level 100, only parsing).

Notation "( e )" := e (in custom live_expr at level 1, e custom live_expr at level 100).

(* Note: f can't be a literal, but the grammar has to allow it, because the
   grammar factorizer that resolves between "start of expression" and "start of call"
   only kicks in if we use the same entry (bound_name_or_literal) here as in the
   base case of live_expr. *)
Notation "f ()" := (RCall f nil)
  (in custom live_expr at level 1, f custom bound_name_or_literal at level 1).
Notation "f ( )" := (RCall f nil)
  (in custom live_expr at level 1, f custom bound_name_or_literal at level 1).
Notation "f '(' e1 ',' .. ',' en ')'" := (RCall f (cons e1 .. (cons en nil) ..))
  (in custom live_expr at level 1,
   f custom bound_name_or_literal at level 1,
   e1 custom live_expr at level 100, en custom live_expr at level 100).

Ltac cast_string_or_z_to_expr x :=
  lazymatch type of x with
  | String.string => exact (expr.var x)
  | Z => exact (expr.literal x)
  end.

Notation "x" := (match x with
                 | _ => ltac:(cast_string_or_z_to_expr x)
                 end)
  (in custom live_expr at level 1, x custom bound_name_or_literal at level 1, only parsing).

(* Using the same precedences as https://en.cppreference.com/w/c/language/operator_precedence *)
Notation "! x" := (expr.not x)
  (in custom live_expr at level 2, x custom live_expr, right associativity, only parsing).
Notation "- x" := (expr.op bopname.sub (expr.literal 0) x)
  (in custom live_expr at level 2, x custom live_expr, right associativity, only parsing).
Infix "*" := (expr.op bopname.mul)
  (in custom live_expr at level 3, left associativity, only parsing).
Infix "/" := (expr.op bopname.divu)
  (in custom live_expr at level 3, left associativity, only parsing).
Infix "%" := (expr.op bopname.remu)
  (in custom live_expr at level 3, left associativity, only parsing).
Infix "+" := (expr.op bopname.add)
  (in custom live_expr at level 4, left associativity, only parsing).
Infix "-" := (expr.op bopname.sub)
  (in custom live_expr at level 4, left associativity, only parsing).
Infix "<<" := (expr.op bopname.slu)
  (in custom live_expr at level 5, left associativity, only parsing).
Infix ">>" := (expr.op bopname.sru)
  (in custom live_expr at level 5, left associativity, only parsing).
Infix "<" := (expr.op bopname.ltu)
  (in custom live_expr at level 6, no associativity, only parsing).
Notation "a <= b" := (expr.not (expr.op bopname.ltu b a))
  (in custom live_expr at level 6, a custom live_expr, b custom live_expr,
   no associativity, only parsing).
Notation "a > b" := (expr.op bopname.ltu b a)
  (in custom live_expr at level 6, a custom live_expr, b custom live_expr,
   no associativity, only parsing).
Notation "a >= b" := (expr.not (expr.op bopname.ltu a b))
  (in custom live_expr at level 6, a custom live_expr, b custom live_expr,
   no associativity, only parsing).
Infix "==" := (expr.op bopname.eq)
  (in custom live_expr at level 7, no associativity, only parsing).
Notation "a != b" := (expr.not (expr.op bopname.eq a b))
  (in custom live_expr at level 7, no associativity, only parsing).
Remark unfolding_not_eq: forall a b: unit,
  live_expr:(a != b) = live_expr:((a == b) == 0).
Proof. intros _ _. unfold expr.not. reflexivity. Succeed Qed. Abort.
Infix "&" := (expr.op bopname.and)
  (in custom live_expr at level 8, left associativity, only parsing).
Infix "^" := (expr.op bopname.xor)
  (in custom live_expr at level 9, left associativity, only parsing).
Infix "|" := (expr.op bopname.or)
  (in custom live_expr at level 10, left associativity, only parsing).
Infix "&&" := expr.lazy_and
  (in custom live_expr at level 11, left associativity, only parsing).
Infix "||" := expr.lazy_or
  (in custom live_expr at level 12, left associativity, only parsing).
Notation "c ? e1 : e2" := (expr.ite c e1 e2)
  (in custom live_expr at level 13, right associativity, only parsing).

Notation "load8( a )" := (expr.load access_size.one a)
  (in custom live_expr at level 1, a custom live_expr at level 100, only parsing).
Notation "load16( a )" := (expr.load access_size.two a)
  (in custom live_expr at level 1, a custom live_expr at level 100, only parsing).
Notation "load32( a )" := (expr.load access_size.four a)
  (in custom live_expr at level 1, a custom live_expr at level 100, only parsing).
Notation "load( a )" := (expr.load access_size.word a)
  (in custom live_expr at level 1, a custom live_expr at level 100, only parsing).

Notation "deref8( a )" := (deref access_size.one a)
  (in custom live_expr at level 1, a custom live_expr at level 100, only parsing).
Notation "deref16( a )" := (deref access_size.two a)
  (in custom live_expr at level 1, a custom live_expr at level 100, only parsing).
Notation "deref32( a )" := (deref access_size.four a)
  (in custom live_expr at level 1, a custom live_expr at level 100, only parsing).
Notation "deref( a )" := (deref access_size.word a)
  (in custom live_expr at level 1, a custom live_expr at level 100, only parsing).

Set Ltac2 Backtrace.

Goal forall (word: Type) (x: word),
    live_expr:(x) = expr.var "x".
Proof. intros. reflexivity. Abort.

Goal forall (word: Type) (x: word),
    live_expr:(x + 3) = expr.op bopname.add (expr.var "x") (expr.literal 3).
Proof. intros. reflexivity. Abort.

Goal forall (word: Type) (x: word), live_expr:(x ( )) = RCall "x" nil.
Proof. intros. reflexivity. Abort.

Goal live_expr:(2 + 3) = expr.op bopname.add (expr.literal 2) (expr.literal 3).
Proof. intros. reflexivity. Abort.

Goal forall (word: Type) (x: word),
    live_expr:(x + 3) = expr.op bopname.add (expr.var "x") (expr.literal 3).
Proof. intros. reflexivity. Abort.

Goal forall (word: Type) (x: word),
  live_expr:(x <= 3) =
  expr.op bopname.eq (expr.op bopname.ltu (expr.literal 3) (expr.var "x")) (expr.literal 0).
Proof. intros. reflexivity. Abort.

Declare Custom Entry comment.
Notation "'comment:(' x ')'" := x (x custom comment at level 2, only parsing).
Notation "x" := tt (in custom comment at level 0, x ident, only parsing).
Notation "," := tt (in custom comment at level 0, only parsing).
Notation "!" := tt (in custom comment at level 0, only parsing).
Notation "?" := tt (in custom comment at level 0, only parsing).
Notation "-" := tt (in custom comment at level 0, only parsing).
Notation "+" := tt (in custom comment at level 0, only parsing).
Notation "#" := tt (in custom comment at level 0, only parsing).
Notation "$" := tt (in custom comment at level 0, only parsing).
Notation ":" := tt (in custom comment at level 0, only parsing).
Notation "a b" := tt
  (in custom comment at level 2,
   b custom comment at level 1,
   only parsing).

Goal True.
  pose comment:(an attempt to write a comment).
  pose comment:(let's include a comma, which should work!).
Abort.

Declare Custom Entry snippet.

Notation "*/ s /*" := s (s custom snippet at level 100).

Notation "/* c */" := SEmpty
  (in custom snippet at level 0, c custom comment at level 2, only parsing).

Ltac coerce_expr_to_assignment_rhs e :=
  lazymatch type of e with
  | expr => exact (RExpr e)
  | _ => exact e
  end.

Notation "'uintptr_t' x = r ;" := (SAssign true x ltac:(coerce_expr_to_assignment_rhs r))
  (in custom snippet at level 0,
   x custom binder_name at level 0, r custom live_expr at level 100,
   only parsing).

Notation "f () ;" := (SVoidCall f nil)
  (in custom snippet at level 0, f custom bound_name_or_literal at level 1).
Notation "f ( ) ;" := (SVoidCall f nil)
  (in custom snippet at level 0, f custom bound_name_or_literal at level 1).
Notation "f ( e1 , .. , en ) ;" := (SVoidCall f (cons e1 .. (cons en nil) ..))
  (in custom snippet at level 0,
   f custom bound_name_or_literal at level 1,
   e1 custom live_expr at level 100, en custom live_expr at level 100).

Notation "x = r ;" := (SAssign false x ltac:(coerce_expr_to_assignment_rhs r))
  (in custom snippet at level 0,
   x custom bound_name_or_literal at level 1, r custom live_expr at level 100,
   only parsing).

Notation "store8( a , v ) ;" := (SStore access_size.one a v)
  (in custom snippet at level 0,
   a custom live_expr at level 100, v custom live_expr at level 100).
Notation "store16( a , v ) ;" := (SStore access_size.two a v)
  (in custom snippet at level 0,
   a custom live_expr at level 100, v custom live_expr at level 100).
Notation "store32( a , v ) ;" := (SStore access_size.four a v)
  (in custom snippet at level 0,
   a custom live_expr at level 100, v custom live_expr at level 100).
Notation "store( a , v ) ;" := (SStore access_size.word a v)
  (in custom snippet at level 0,
   a custom live_expr at level 100, v custom live_expr at level 100).

Notation "'return' e ;" := (SRet e)
  (in custom snippet at level 0, e custom live_expr at level 100).

Notation "'if' ( e ) {" := (SIf e false)
  (in custom snippet at level 0, e custom live_expr).
Notation "'if' ( e ) /* 'split' */ {" := (SIf e true)
  (in custom snippet at level 0, e custom live_expr).
Notation "{" := SStart (in custom snippet at level 0).
Notation "}" := SEnd (in custom snippet at level 0).
Notation "} 'else' {" := (SElse true) (in custom snippet at level 0).
Notation "'else' {" := (SElse false) (in custom snippet at level 0).

Notation "'while' ( e ) /* 'initial_ghosts' g0 ; 'decreases' m0 */ {" :=
  (SWhileTailrec e g0 m0)
  (in custom snippet at level 0, e custom live_expr,
   g0 constr at level 0, m0 constr at level 0).

Notation "'while' ( e ) /* 'decreases' m */ {" :=
  (SWhile e m) (in custom snippet at level 0, e custom live_expr, m constr at level 0).

Notation "'do' /* 'decreases' m0 */ {" := (SDo m0)
  (in custom snippet at level 0, m0 constr at level 0).

Notation "'do' /* 'initial_ghosts' g0 ; 'decreases' m0 */ {" := (SDoTailrec g0 m0)
  (in custom snippet at level 0, g0 constr at level 0, m0 constr at level 0).

Notation "} 'while' ( e ) ;" := (SEndDo e)
  (in custom snippet at level 0, e custom live_expr).

Ltac exact_bitwidth :=
  let bw := constr:(_ : Bitwidth _) in
  lazymatch type of bw with
  | Bitwidth ?w => exact w
  end.

Notation bitwidth := ltac:(exact_bitwidth) (only parsing).

Ltac exact_bytes_per_word :=
  let bw := constr:(_ : Bitwidth _) in
  lazymatch type of bw with
  | Bitwidth 32 => exact 4
  | Bitwidth 64 => exact 8
  end.

Notation bytes_per_word := ltac:(exact_bytes_per_word) (only parsing).

Notation "'sizeof(uintptr_t)'" := (expr.literal bytes_per_word)
  (in custom live_expr at level 1, only parsing).

Goal forall (BW: Bitwidth 32),
    */ uintptr_t v = sizeof(uintptr_t); /* = SAssign true "v" (RExpr (expr.literal 4)).
Proof. intros. reflexivity. Succeed Qed. Abort.

Goal True.
  pose */ /* hello, world! */ /* as s.
  pose */ /* The way we implement C comments appears a bit limited:
             - We can't use full stops
             - Only a few special characters are supported, eg ?, $, #
             - We can't use parentheses
             - We can't use Coq keywords */ /*.
  pose */ S(); /*.
  pose */ S( ); /*.
  pose */ S ( ); /*.
  pose */ O(3); /*.
  pose */ O(1, 2); /*.
  pose */ O(10, s, s); /*.
  pose */ s = S(); /*.
  pose */ s = S( ); /*.
  pose */ s = S ( ); /*.
  pose */ s = O(3); /*.
  pose */ s = O(1, 2); /*.
  pose */ s = O(10, s, s); /*.
  pose */ uintptr_t s = S(); /*.
  pose */ uintptr_t s = S( ); /*.
  pose */ uintptr_t s = S ( ); /*.
  pose */ uintptr_t s = O(3); /*.
  pose */ uintptr_t s = O(1, 2); /*.
  pose */ uintptr_t s = O(10, s, s); /*.
  pose live_expr:(s << s) as x.
  pose */ store(s, 0); /*.
  pose */ if (s != 0) { /*.
  pose */ s = s; /*.
  pose */ s = 12; /*.
  pose */ s = (-12); /*.
  pose */ s = -s; /*.
  pose */ s = s + 1; /*.
  pose */ s = s + (x << 2); /*.
  pose */ s = (x + s) + (x << 2); /*.
  pose */ s = x + x + x; /*.
  pose */ s = (s << s); /*.
  pose */ s = (s + x); /*.
  pose */ s = load16(s + x); /*.
  pose */ x = (x + 1); /*.
  pose */ uintptr_t foo = x + x + x; /*.
  pose */ uintptr_t newname = -s; /*.
  pose */ uintptr_t s = (s << s); /*.
  pose */ store8(x+4, s-1); /*.
  pose */ store16(x, load16(s-1)); /*.
  pose */ store32((x + x) * 4, s-1); /*.
  pose */ store(x+4, s); /*.
Abort.
