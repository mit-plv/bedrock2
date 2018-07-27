Require Import Coq.NArith.BinNatDef.
Require Coq.Strings.String.
Definition string_eqb a b := andb (String.prefix a b) (String.prefix b a).

Module Import ImpSyntax.
  Class Parameters :=
    {
      varname : Type;
      funname : Type;
      actname : Type;
      bopname : Type;

      mword : Type;
    }.
End ImpSyntax.

Module ImpSyntaxString.
  Class Parameters :=
    {
      actname : Type;
      bopname : Type;

      mword : Type;
    }.
  Global Instance make (p : Parameters) : ImpSyntax.Parameters :=
    {|
      ImpSyntax.varname := String.string;
      ImpSyntax.funname := String.string;
      
      ImpSyntax.actname := actname;
      ImpSyntax.bopname := bopname;
      ImpSyntax.mword := mword |}.
End ImpSyntaxString.

Class BasicALU (p:ImpSyntax.Parameters) :=
  {
    mword_of_N_or_zero : N -> mword;

    bop_add : bopname;
    bop_sub : bopname;

    bop_and : bopname;
    bop_or : bopname;
    bop_xor : bopname;

    (* no information about return value of long shifts, but they are allowed *)
    bop_sru : bopname;
    bop_slu : bopname;
    bop_srs : bopname;

    bop_lts : bopname;
    bop_ltu : bopname;
    bop_eq : bopname;
  }.

(*
Class Mem (mword : Type) :=
  {
    mem : Type;
    load : mword -> mem -> option mword;
    store : mword -> mword -> mem -> option mem;
  }.

Class ImpParameters :=
  {
    ImpParameters_ImpSyntaxParameters : ImpSyntaxParameters;

    mword_nonzero : mword -> bool;
    interp_binop : bopname -> mword -> mword -> mword;

    Mem_ImpParameters : Mem mword;
  }.
Global Existing Instance Mem_ImpParameters.
*)

Module access_size.
  Inductive access_size := one | two | four | eight. (* bytes *)
  Definition to_N (s : access_size) : N :=
    match s with
    | one => 1
    | two => 2
    | four => 4
    | eight => 8
    end.
End access_size. Notation access_size := access_size.access_size.

Section ImpSyntax_.
  Goal True. let cls := constr:(ImpSyntax.Parameters) in match constr:(Set) with _ => (let none := constr:(_:cls) in idtac); fail 99 "DUPLICATE INSTANCE" | _ => idtac end. Abort.
  Context {p : ImpSyntax.Parameters}.
  Inductive expr  : Type :=
  | ELit(v: mword)
  | EVar(x: varname)
  | ELoad(s:access_size)(addr:expr)
  | EOp(op: bopname) (e1 e2: expr).


  Inductive stmt :=
  | SStore(s:access_size)(addr val: expr)
  | SSet(x: varname)(e: expr)
  | SIf(cond: expr)(bThen bElse: stmt)
  | SWhile(cond: expr)(body: stmt)
  | SSeq(s1 s2: stmt)
  | SSkip
  | SCall(binds: list varname)(f: funname)(args: list expr)
  | SIO(binds: list varname)(io : actname)(args: list expr).
End ImpSyntax_.

Require Coq.Lists.List.
Section SyntaxUtils.
  Goal True. let cls := constr:(ImpSyntax.Parameters) in match constr:(Set) with _ => (let none := constr:(_:cls) in idtac); fail 99 "DUPLICATE INSTANCE" | _ => idtac end. Abort.
  Context {p : ImpSyntax.Parameters}.
  Import List. Import ListNotations.
  Fixpoint allVars_expr(e: expr): list varname :=
    match e with
    | ELit v => []
    | EVar x => [x]
    | ELoad _ ea => allVars_expr ea
    | EOp op e1 e2 => (allVars_expr e1) ++ (allVars_expr e2)
    end.

  Fixpoint allVars_stmt(s: stmt): list varname := 
    match s with
    | SStore s a e => (allVars_expr a) ++ (allVars_expr e)
    | SSet v e => v :: allVars_expr e
    | SIf c s1 s2 => (allVars_expr c) ++ (allVars_stmt s1) ++ (allVars_stmt s2)
    | SWhile c body => (allVars_expr c) ++ (allVars_stmt body)
    | SSeq s1 s2 => (allVars_stmt s1) ++ (allVars_stmt s2)
    | SSkip => []
    | SCall binds _ args | SIO binds _ args => binds ++ List.fold_right (@List.app _) nil (List.map allVars_expr args)
    end.
End SyntaxUtils.

Module Import ImpStruct.
  Import String.
  
  Inductive struct :=
  | Struct (_ : list (string * (access_size + struct))).
  Definition type : Type := access_size + struct.
  
  Fixpoint sizeof_struct (s : struct) {struct s} : N :=
    match s with
    | (Struct ls) =>
      (fix sizeof_fields (l : list _) {struct l} : N :=
         match l with
         | nil => 0%N
         | cons (_, f) l' =>
           N.add (match f with inl s => access_size.to_N s | inr s' => sizeof_struct s' end)
                 (sizeof_fields l')
         end
      ) ls
    end.
  
  Definition sizeof (s:type) : N :=
    match s with
    | inl s => access_size.to_N s
    | inr s => sizeof_struct s
    end.
  
  Definition slookup (field : string) (s : struct) : option (N * type) :=
    match s with
    | (Struct ls) =>
      (fix llookup (l : list _) {struct l} : option (N * type) :=
         match l with
         | nil => None
         | cons (f, ftype) l' =>
           if string_eqb f field
           then Some (0, ftype)
           else match llookup l' with
                | None => None
                | Some (o, t) => Some (N.add (sizeof ftype) o, t)
                end
         end
      ) ls
    end%N.
  
  Fixpoint rlookup fieldnames (s : type) : option (N * type) :=
    match fieldnames, s with
    | nil, r => Some (0, r)
    | cons f fieldnames', inr s =>
      match slookup f s with
      | None => None
      | Some (o, s') =>
        match rlookup fieldnames' s' with
        | None => None
        | Some (o', s') => Some (N.add o o', s')
        end
      end
    | _, _ => None
    end%N.
  
  Inductive NO_SUCH_FIELD {T} (ctx:T) : Set := mk_NO_SUCH_FIELD.
  Inductive TYPE_IS_NOT_SCALAR {T} (ctx:T) : Set := mk_TYPE_IS_NOT_SCALAR.
  Definition scalar {T} (ctx : T) (r :  option (N * type)) :
    match r with
    | None => NO_SUCH_FIELD ctx
    | Some (_, inr a) => TYPE_IS_NOT_SCALAR (a, ctx)
    | Some (n, inl s) => N * access_size
    end :=
    match r with
    | None => mk_NO_SUCH_FIELD ctx
    | Some (_, inr a) => mk_TYPE_IS_NOT_SCALAR (a, ctx)
    | Some (n, inl s) => (n, s)
    end.
  
  Module __test.
    Import String.
    Open Scope string_scope.
    Import List.
    Import ListNotations.
    Import access_size.
    
    Local Open Scope N_scope.
    Goal True.
      assert (sizeof_struct (Struct []) = 0) as _ by reflexivity.
      assert (sizeof_struct (Struct [("a", inl eight); ("b", inl eight); ("c", inl two)]) = 18) as _ by reflexivity.
      assert (slookup "a" (Struct []) = None) as _ by reflexivity.
      assert (slookup "a" (Struct [("a", inl one)]) = Some (0, inl one)) as _ by reflexivity.
      assert (slookup "a" (Struct [("x", inl four); ("a", inl two)]) = Some (4, inl two)) as _ by reflexivity.
      assert (slookup "a" (Struct [("x", inr (Struct [("xx", inl one); ("yy", inl eight)])); ("a", inr (Struct [("data",inl one)]))]) = Some (9, inr (Struct [("data",inl one)]))) as _ by reflexivity.
    Abort.
  
    Section with_mword.
    Context (mword : access_size).
    Definition utcb_segment : type := inr ( Struct (
     [ ("sel", inl two); ("ar", inl two); ("limit", inl four); ("base", inl mword) ]
     ++ match mword with eight => [] | _ => [("reserved", inl mword)] end)).
  
    Definition exception_state : type := inr ( Struct (
      [ ("mtd", inl mword) ; ("intr_len", inl mword) ; ("ip", inl mword) ; ("rflags", inl mword)
      ; ("intr_state", inl four) ; ("actv_state", inl four)
      ; ("inj", inl eight)                          (* NOTE: union: uint32 intr_info, intr_error *)
      ; ("ax", inl mword) ; ("cx", inl mword) ; ("dx", inl mword) ; ("bx", inl mword)
      ; ("sp", inl mword) ; ("bp", inl mword) ; ("si", inl mword) ; ("di", inl mword)
      ] ++
      match mword with
      | eight => 
        [ ("r8", inl mword) ; ("r9", inl mword) ; ("r10", inl mword) ; ("r11", inl mword)
        ; ("r12", inl mword) ; ("r13", inl mword) ; ("r14", inl mword) ; ("r15", inl mword) ]
      | _=> []
      end ++
      [ ("qual0", inl eight); ("qual1", inl eight)                       (* NOTE: uint64 qual[2] *)
      ; ("ctrl0", inl four); ("qual1", inl four)                         (* NOTE: uint32 ctrl[2] *)
      ; ("reserved", inl eight) (* NOTE: uint32 ctrl[2] *)
      ; ("cr0", inl mword) ; ("cr2", inl mword) ; ("cr3", inl mword) ; ("cr4", inl mword)
      ] ++
      match mword with
      | eight =>  [ ("cr8", inl mword) ; ("efer", inl mword) ]
      | _ => []
      end ++
      [ ("dr7", inl mword) ; ("sysenter_cs", inl mword) ; ("sysenter_sp", inl mword) ; ("sysenter_ip", inl mword)
      ; ("es", utcb_segment); ("cs", utcb_segment); ("ss", utcb_segment); ("ds", utcb_segment); ("gs", utcb_segment); ("ldtr", utcb_segment); ("tr", utcb_segment); ("gdtr", utcb_segment); ("idtr", utcb_segment)
      ; ("tsc_val", inl eight); ("tsc_off", inl eight)
      ] ) ).
    End with_mword.
  End __test.
End ImpStruct.

Module ImpNotations.
  Import List. Import String. Open Scope string_scope. Open Scope N_scope.
  Module Export Core.
    Delimit Scope bedrock_var with bedrock_var.

    Delimit Scope bedrock_expr with bedrock_expr.
    Bind Scope bedrock_expr with expr.
    Notation "(uintptr_t) v 'ULL'" := (ELit v)
     (at level 1, no associativity, format "(uintptr_t) v 'ULL'") : bedrock_expr.

    Notation "*(uint8_t*) e" := (ELoad access_size.one e%bedrock_expr)
      (at level 10, no associativity) : bedrock_expr.
    Notation "*(uint16_t*) e" := (ELoad access_size.two e%bedrock_expr)
      (at level 10, no associativity) : bedrock_expr.
    Notation "*(uint32_t*) e" := (ELoad access_size.four e%bedrock_expr)
      (at level 10, no associativity) : bedrock_expr.
    Notation "*(uint64_t*) e" := (ELoad access_size.eight e%bedrock_expr)
      (at level 10, no associativity) : bedrock_expr.

    Delimit Scope bedrock_stmt with bedrock_stmt.
    Notation "'/*skip*/'" := SSkip
      : bedrock_stmt.
    Notation "x = e" := (SSet x%bedrock_var e%bedrock_expr)
      : bedrock_stmt.

    Notation "*(uint8_t*) ea = ev" := (SStore access_size.one ea%bedrock_var ev%bedrock_expr)
      (at level 76, ea at level 60) : bedrock_stmt.
    Notation "*(uint16_t*) ea = ev" := (SStore access_size.two ea%bedrock_var ev%bedrock_expr)
      (at level 76, ea at level 60) : bedrock_stmt.
    Notation "*(uint32_t*) ea = ev" := (SStore access_size.four ea%bedrock_var ev%bedrock_expr)
      (at level 76, ea at level 60) : bedrock_stmt.
    Notation "*(uint64_t*) ea = ev" := (SStore access_size.eight ea%bedrock_var ev%bedrock_expr)
      (at level 76, ea at level 60) : bedrock_stmt.

    Notation "c1 ; c2" := (SSeq c1%bedrock_stmt c2%bedrock_stmt)
      (at level 76, right associativity, c2 at level 76, format "'[v' c1 ; '/' c2 ']'") : bedrock_stmt.
    Notation "'if' ( e ) { { c1 } } 'else' { { c2 } }" := (SIf e%bedrock_expr c1%bedrock_stmt c2%bedrock_stmt)
     (at level 76, no associativity, c1 at level 76, c2 at level 76, format "'[v' 'if'  ( e )  { {  '/  ' c1 '/' } }  'else'  { {  '/  ' c2 '/' } } ']'") : bedrock_stmt.
    Notation "'if' ( e ) { { c } }" := (SIf e%bedrock_expr c%bedrock_stmt SSkip)
     (at level 76, no associativity, c at level 76, format "'[v' 'if'  ( e )  { {  '/  ' c '/' } } ']'") : bedrock_stmt.
    Notation "'while' ( e ) { { c } }" := (SWhile e%bedrock_expr c%bedrock_stmt)
     (at level 76, no associativity, c at level 76, format "'[v' 'while'  ( e )  { {  '/  ' c '/' } } ']'") : bedrock_stmt.

    Delimit Scope bedrock_func with bedrock_func.
    Notation "'require' ( e ) 'else' { { ce } } c" := (SIf e%bedrock_expr c%bedrock_func%bedrock_stmt ce%bedrock_stmt)
     (at level 76, right associativity, ce at level 76, c at level 76, format "'[v' 'require'  ( e )  'else'  { { '/  '  ce '/' } } '//' c ']'") : bedrock_func.
    Notation "c1 ; c2" := (SSeq c1%bedrock_stmt c2%bedrock_func%bedrock_stmt)
      (at level 76, right associativity, c2 at level 76, format "'[v' c1 ; '/' c2 ']'") : bedrock_func.
    Notation "'while' ( e ) { { c } }" := (SWhile e%bedrock_expr c%bedrock_stmt)
   (at level 76, no associativity, c at level 76, format "'[v' 'while'  ( e )  { {  '/  ' c '/' } } ']'") : bedrock_func.
    Notation "'if' ( e ) { { c1 } } 'else' { { c2 } }" := (SIf e%bedrock_expr c1%bedrock_func c2%bedrock_func)
     (at level 76, no associativity, c1 at level 76, c2 at level 76, format "'[v' 'if'  ( e )  { {  '/  ' c1 '/' } }  'else'  { {  '/  ' c2 '/' } } ']'") : bedrock_func.
    Notation "'if' ( e ) { { c } }" := (SIf e%bedrock_expr c%bedrock_func SSkip)
     (at level 76, no associativity, c at level 76, format "'[v' 'if'  ( e )  { {  '/  ' c '/' } } ']'") : bedrock_func.

    Definition bedrock_func {p} (x:@stmt p) := x.
    Arguments bedrock_func {_} _%bedrock_func.
    Undelimit Scope bedrock_func.
  End Core.

  Module Export ALU.
    (* record field access *)
    Notation "e 'as' t *> a '!' .. '!' c" := (let '(ofs, sz) := scalar (t%list%string, (cons a%string .. (cons c%string nil) .. )) (rlookup (cons a%string .. (cons c%string nil) .. ) t%list%string) in (ELoad sz (EOp bop_add e (ELit (mword_of_N_or_zero ofs)))))
      (at level 76, a at level 60, c at level 60) : bedrock_expr.
    Notation "e 'as' t *> a '!' .. '!' c = rhs" := (let '(ofs, sz) := scalar (t%list%string, (cons a%string .. (cons c%string nil) .. )) (rlookup (cons a%string .. (cons c%string nil) .. ) t%list%string) in (SStore sz (EOp bop_add e (ELit (mword_of_N_or_zero ofs))) rhs))
      (at level 76, a at level 60, c at level 60) : bedrock_stmt.

    Notation "'&field' a '!' .. '!' c 'of' t 'at' e" := (let '(ofs, _) := scalar (t%list%string, (cons a%string .. (cons c%string nil) .. )) (rlookup (cons a%string .. (cons c%string nil) .. ) t%list%string) in ((EOp bop_add e (ELit (mword_of_N_or_zero ofs)))))
      (at level 76, t at level 60, e at level 60, a at level 60, c at level 60) : bedrock_expr.
    Notation "'field' a '!' .. '!' c 'of' t 'at' e  = rhs" := (let '(ofs, sz) := scalar (t%list%string, (cons a%string .. (cons c%string nil) .. )) (rlookup (cons a%string .. (cons c%string nil) .. ) t%list%string) in (SStore sz (EOp bop_add e (ELit (mword_of_N_or_zero ofs))) rhs))
      (at level 76, t at level 60, e at level 60, a at level 60, c at level 60) : bedrock_stmt.

    (*
    Notation "s 'at' e '=' rhs" := (SStore s e%bedrock_expr rhs%bedrock_expr)
    (at level 76, e at level 60) : bedrock_stmt.
     *)

    Notation "e1 + e2" := (EOp bop_add e1%bedrock_expr e2%bedrock_expr)
      : bedrock_expr.
    Notation "e1 - e2" := (EOp bop_sub e1%bedrock_expr e2%bedrock_expr)
      : bedrock_expr.
    Notation "e1 == e2" := (EOp bop_eq e1%bedrock_expr e2%bedrock_expr)
      (at level 100, no associativity) : bedrock_expr.
    Notation "e1 < e2" := (EOp bop_ltu e1%bedrock_expr e2%bedrock_expr)
      : bedrock_expr.
    Notation "e1 <. e2" := (EOp bop_lts e1%bedrock_expr e2%bedrock_expr)
      (at level 100, no associativity) : bedrock_expr.
    Notation "e1 & e2" := (EOp bop_and e1%bedrock_expr e2%bedrock_expr)
      (at level 40, no associativity) : bedrock_expr.
    Notation "e1 >> e2" := (EOp bop_sru e1%bedrock_expr e2%bedrock_expr)
      (at level 60, no associativity) : bedrock_expr.
    Notation "e1 >>. e2" := (EOp bop_srs e1%bedrock_expr e2%bedrock_expr)
      (at level 60, no associativity) : bedrock_expr.
    Notation "e1 << e2" := (EOp bop_slu e1%bedrock_expr e2%bedrock_expr)
      (at level 60, no associativity) : bedrock_expr.
  End ALU.
End ImpNotations.

Module ImpToC. Section ImpToC.
  Class Parameters :=
    {
      ImpSyntax :> ImpSyntax.Parameters;
      c_lit : mword -> String.string;
      c_bop : String.string -> bopname -> String.string -> String.string;
      c_var : varname -> String.string;
      c_fun : funname -> String.string;
      c_act : list varname -> actname -> list String.string -> String.string;
      
      varname_eqb : varname -> varname -> bool;
      rename_away_from : varname -> list varname -> varname;
    }.
  Context {p : Parameters}.
  Import String.

  Definition LF : string := String (Coq.Strings.Ascii.Ascii false true false true false false false false) "".

  Definition c_size (s : access_size) : string :=
    match s with
    | access_size.one => "uint8_t"
    | access_size.two => "uint16_t"
    | access_size.four => "uint32_t"
    | access_size.eight => "uint64_t"
    end.

  Fixpoint c_expr (e : expr) : string :=
    match e with
    | ELit v => c_lit v 
    | EVar x => c_var x
    | ELoad s ea => "*(" ++ c_size s ++ "*)(" ++ c_expr ea ++ ")"
    | EOp op e1 e2 => c_bop ("(" ++ c_expr e1 ++ ")") op ("(" ++ c_expr e2 ++ ")")
    end.

  Fixpoint List_init {A} (l : list A) :=
    match l with
    | nil => nil
    | cons _ nil => nil
    | cons x l' => cons x (List_init l')
    end.

  Fixpoint List_uniq {A} (eqb : A -> A -> bool) (l : list A) :=
    match l with
    | nil => nil
    | cons a l' =>
      if List.existsb (eqb a ) l'
      then List_uniq eqb l'
      else cons a (List_uniq eqb l')
    end.

  Definition List_minus {A} (eqb : A -> A -> bool) (X Y : list A) :=
    List.filter (fun x => negb (List.existsb (eqb x) Y)) X.

  Fixpoint c_stmt (indent : string) (c : stmt) : string :=
    match c with
    | SStore s ea ev
      => indent ++ "*("++c_size s++"*)(" ++ c_expr ea ++ ") = " ++ c_expr ev ++ ";" ++ LF
    | SSet x ev =>
      indent ++ c_var x ++ " = " ++ c_expr ev ++ ";" ++ LF
    | SIf eb t f =>
      indent ++ "if (" ++ c_expr eb ++ ") {" ++ LF ++
        c_stmt ("  "++indent) t ++
      indent ++ "} else {" ++ LF ++
        c_stmt ("  "++indent) f ++
      indent ++ "}" ++ LF
    | SWhile eb c =>
      indent ++ "while (" ++ c_expr eb ++ ") {" ++ LF ++
        c_stmt ("  "++indent) c ++
      indent ++ "}" ++ LF
    | SSeq c1 c2 =>
      c_stmt indent c1 ++
      c_stmt indent c2
    | SSkip =>
      indent ++ "/*skip*/" ++ LF
    | SCall nil f es =>
      indent ++ c_fun f ++ "(" ++ concat ", " (List.map c_expr es) ++ ");" ++ LF
    | SCall ((x::_) as binds) f es =>
      indent ++ c_var (List.last binds x) ++ " = " ++ c_fun f ++ "(" ++ concat ", " (List.map c_expr es ++ List.map (fun x => "&"++c_var x) (List_init binds)) ++ ");" ++ LF
    | SIO binds action es =>
      c_act binds action (List.map c_expr es)
    end%string.

  Definition c_decl (rett : string) (args : list varname) (name : funname) (retptrs : list varname) : string :=
    (rett ++ " " ++ c_fun name ++ "(" ++ concat ", " (
                    List.map (fun a => "uintptr_t "++c_var a) args ++
                    List.map (fun r => "uintptr_t* "++c_var r) retptrs) ++
                  ")")%string.

  Fixpoint rename_outs (outs : list varname) (used : list varname) : list (varname*varname) * list varname :=
    match outs with
    | cons o outs' =>
      let rec := rename_outs outs' used in
      let (outrenames, used) := (fst rec, snd rec) in
      let optr := rename_away_from o used in
      (cons (o, optr) outrenames, cons o used)
    | nil => (nil, used)
    end.

  Local Open Scope string_scope.
  Definition c_func name '(args, rets, body) :=
    let decl_retvar_retrenames : string * option varname * list (varname * varname) :=
    match rets with
    | nil => (c_decl "void" args name nil, None, nil)
    | cons r0 rets' =>
      let retrenames := fst (rename_outs rets' (allVars_stmt body)) in
      (c_decl "uintptr_t" args name (List.map snd retrenames), Some r0, retrenames)
    end in
    let decl := fst (fst decl_retvar_retrenames) in
    let retvar := snd (fst decl_retvar_retrenames) in
    let retrenames := snd decl_retvar_retrenames in
    let localvars : list varname := List_uniq varname_eqb (List.app
        (match retvar with None => nil | Some v => cons v nil end)
        (List_minus varname_eqb (allVars_stmt body) args)) in
    decl ++ " {" ++ LF ++
      let indent := "  " in
      (match localvars with nil => "" | _ => indent ++ "uintptr_t " ++ concat ", " (List.map c_var localvars) ++ ";" ++ LF end) ++
      c_stmt indent body ++
      concat "" (List.map (fun '(o, optr) => indent ++ "*" ++ c_var optr ++ " = " ++ c_var o ++ LF) retrenames) ++
      indent ++ "return" ++ (match retvar with None => "" | Some rv => " "++c_var rv end) ++ ";" ++ LF ++
      "}" ++ LF.
End ImpToC. End ImpToC.

Module _test.
  Section _test.
    Context {p : ImpSyntaxString.Parameters} {bp : BasicALU _}.
    Local Coercion mword_of_N_or_zero (n:N) : mword := mword_of_N_or_zero n.
    Local Coercion ELit : mword >-> expr.
    Local Coercion EVar : varname >-> expr.
    Bind Scope string_scope with varname.
    Import ImpNotations.

    Definition item : type := inr (Struct (("a", inl access_size.one)::("b", inl access_size.two)::nil))%list.

    Let ptr : varname := "ptr".
    Let src : varname := "src".
    
    Check
      (&field "b" of item at (ptr as item *> "b" as item *> "a")) %bedrock_expr.
    Check
      (field "b" of item at (ptr as item *> "b" as item *> "a") = *(uint8_t*) src; SSkip) %bedrock_stmt.
  End _test.
End _test.


Module _example.
  Section _example.
    Context {p : ImpSyntaxString.Parameters} {bp : BasicALU _}.
    Local Coercion mword_of_N_or_zero (n:N) : mword := mword_of_N_or_zero n.
    Local Coercion ELit : mword >-> expr.
    Local Coercion EVar : varname >-> expr.
    Bind Scope string_scope with varname.
    Import ImpNotations.

    Let left : varname := "left".
    Let right : varname := "right".
    Let mid : varname := "mid".
    Let ret : varname := "ret".
    Let target : varname := "target".

    Example bsearch :=
    Eval cbv -[bopname bop_add bop_sub bop_ltu bop_slu bop_sru mword_of_N_or_zero] in
    ( (left:: right::nil)%list, (right::nil)%list, 
    (bedrock_func (

    while (left < right) {{
      mid = left + (((right-left) >> 4) << 3);
      ret = *(uint64_t*) mid;
      if (ret < target) {{
        left = mid + 8
      }} else {{
        right = mid
      }}
    }};
    ret = left

         ))).
  End _example.
End _example.

Require bbv.Word.
Require DecimalN.
Require DecimalString.

Module _example_to_c.
  Let bw := 64.
  Module Import alu.
    Inductive bop := add | sub | and | or | xor | sru | slu | srs | lts | ltu | eq.
  End alu.
  Local Instance ImpS : ImpSyntaxString.Parameters :=
    {|
      ImpSyntaxString.mword := Word.word bw;
      ImpSyntaxString.bopname := alu.bop;
      ImpSyntaxString.actname := Empty_set
    |}.
  Local Instance BasicALU : BasicALU _ :=
    Build_BasicALU _ (fun n => Word.NToWord _ n) add sub and or xor sru slu srs lts ltu eq.

  Import ImpToC String. Local Open Scope string_scope.
  Local Instance CImp : ImpToC.Parameters :=
    {|
    ImpToC.ImpSyntax := ltac:(exact _);
    c_lit w := DecimalString.NilZero.string_of_uint (BinNat.N.to_uint (Word.wordToN w)) ++ "ULL";
    c_bop := fun e1 op e2 =>
               match op with
               | add => e1++"+"++e2
               | sub => e1++"-"++e2
               | and => e1++"&"++e2
               | or => e1++"|"++e2
               | xor => e1++"^"++e2
               | sru => e1++">>"++e2
               | slu => e1++"<<"++e2
               | srs => "(intptr_t)"++e1++">>"++"(intptr_t)"++e2
               | lts => "(intptr_t)"++e1++"<"++"(intptr_t)"++e2
               | ltu => e1++"<"++e2
               | eq => e1++"=="++e2
               end%string;
       c_var := id;
       c_fun := id;
       c_act := fun _ _ _ => "#error";

       varname_eqb := string_eqb;
       rename_away_from x xs := "_" ++ x; (* FIXME *)
    |}%string.

  Compute c_func "bsearch" _example.bsearch.
End _example_to_c.