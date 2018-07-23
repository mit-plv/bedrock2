Require Coq.Strings.String.

Class Mem (mword : Type) :=
  {
    mem : Type;
    load : mword -> mem -> option mword;
    store : mword -> mword -> mem -> option mem;
  }.

Class ImpSyntaxParameters :=
  {
    varname : Type;
    funname : Type;
    actname : Type;
    bopname : Type;

    mword : Type;
  }.

(*
Class ImpParameters :=
  {
    ImpParameters_ImpSyntaxParameters : ImpSyntaxParameters;

    mword_nonzero : mword -> bool;
    interp_binop : bopname -> mword -> mword -> mword;

    Mem_ImpParameters : Mem mword;
  }.
Global Existing Instance Mem_ImpParameters.
*)

Section ImpSyntax.
  Goal True. let cls := constr:(ImpSyntaxParameters) in match constr:(Set) with _ => (let none := constr:(_:cls) in idtac); fail 99 "DUPLICATE INSTANCE" | _ => idtac end. Abort.
  Context {p : ImpSyntaxParameters}.
  Inductive expr  : Type :=
  | ELit(v: mword)
  | EVar(x: varname)
  | EOp(op: bopname) (e1 e2: expr).

  Inductive stmt :=
  | SLoad (x: varname)(addr: expr)
  | SStore(addr val: expr)
  | SSet(x: varname)(e: expr)
  | SIf(cond: expr)(bThen bElse: stmt)
  | SWhile(cond: expr)(body: stmt)
  | SSeq(s1 s2: stmt)
  | SSkip
  | SCall(binds: list varname)(f: funname)(args: list expr)
  | SIO(binds: list varname)(io : actname)(args: list expr).
End ImpSyntax.

Require Coq.Lists.List.
Section SyntaxUtils.
  Goal True. let cls := constr:(ImpSyntaxParameters) in match constr:(Set) with _ => (let none := constr:(_:cls) in idtac); fail 99 "DUPLICATE INSTANCE" | _ => idtac end. Abort.
  Context {p : ImpSyntaxParameters}.
  Import List. Import ListNotations.
  Fixpoint allVars_expr(e: expr): list varname :=
    match e with
    | ELit v => []
    | EVar x => [x]
    | EOp op e1 e2 => (allVars_expr e1) ++ (allVars_expr e2)
    end.

  Fixpoint allVars_stmt(s: stmt): list varname := 
    match s with
    | SLoad v e => v :: allVars_expr e
    | SStore a e => (allVars_expr a) ++ (allVars_expr e)
    | SSet v e => v :: allVars_expr e
    | SIf c s1 s2 => (allVars_expr c) ++ (allVars_stmt s1) ++ (allVars_stmt s2)
    | SWhile c body => (allVars_expr c) ++ (allVars_stmt body)
    | SSeq s1 s2 => (allVars_stmt s1) ++ (allVars_stmt s2)
    | SSkip => []
    | SCall binds _ args | SIO binds _ args => binds ++ List.fold_right (@List.app _) nil (List.map allVars_expr args)
    end.
End SyntaxUtils.

Class ImpCSyntaxParameters :=
  { ImpSyntaxParameters_ImpCSyntaxParameters : ImpSyntaxParameters ;
    c_lit : mword -> String.string;
    c_bop : bopname -> String.string;
    c_var : varname -> String.string;
    c_fun : funname -> String.string;
    c_act : list varname -> actname -> list String.string -> String.string;
  }.
Global Existing Instance ImpSyntaxParameters_ImpCSyntaxParameters.

Section ImpToC.
  Goal True. let cls := constr:(ImpCSyntaxParameters) in match constr:(Set) with _ => (let none := constr:(_:cls) in idtac); fail 99 "DUPLICATE INSTANCE" | _ => idtac end. Abort.
  Context {p : ImpCSyntaxParameters}.
  Import String.

  Definition LF : string := String (Coq.Strings.Ascii.Ascii false true false true false false false false) "".

  Fixpoint c_expr (e : expr) : string :=
    match e with
    | ELit v => c_lit v 
    | EVar x => c_var x
    | EOp op e1 e2 => "(" ++ c_expr e1 ++ ")" ++ c_bop op ++ "(" ++ c_expr e2 ++ ")"
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
    | SLoad x ea =>
      indent ++ c_var x ++ " = *(uintptr_t*)(" ++ c_expr ea ++ ");" ++ LF
    | SStore ea ev
      => indent ++ "*(uintptr_t*)(" ++ c_expr ea ++ ") = " ++ c_expr ev ++ ";" ++ LF
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

  Context
    (varname_eqb : varname -> varname -> bool)
    (rename_away_from : varname -> list varname -> varname).
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
  Definition c_func (args : list varname) (name : funname) (rets : list varname) (body : stmt) :=
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
End ImpToC.

Module ImpNotations.
  Delimit Scope bedrock_var with bedrock_var.

  Delimit Scope bedrock_expr with bedrock_expr.
  Notation "(uintptr_t) v 'ULL'" := (ELit v)
   (at level 1, no associativity, format "(uintptr_t) v 'ULL'") : bedrock_expr.

  Delimit Scope bedrock_stmt with bedrock_stmt.
  Notation "'/*skip*/'" := SSkip
    : bedrock_stmt.
  Notation "x = e" := (SSet x%bedrock_var e%bedrock_expr)
    : bedrock_stmt.
  Notation "x =*(uintptr_t*) e" := (SLoad x%bedrock_var e%bedrock_expr)
    (at level 76, no associativity) : bedrock_stmt.

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

  Definition bedrock_func {p} (x:@stmt p) := x.
  Arguments bedrock_func {_} _%bedrock_func.
  Undelimit Scope bedrock_func.
End ImpNotations.


Require compiler.Op.
Require compiler.Memory.
Require bbv.Word.
Require DecimalN.
Require DecimalString.

Module _example.
  Import String.
  Definition string_eqb a b := andb (prefix a b) (prefix b a).
  Definition CImp (bw : nat) : ImpCSyntaxParameters :=
    {| ImpSyntaxParameters_ImpCSyntaxParameters :=
         {|
           varname := String.string;
           funname := String.string;
           actname := String.string;
           mword := Word.word bw;
         |};
       c_lit := fun w => DecimalString.NilZero.string_of_uint (BinNat.N.to_uint (Word.wordToN w)) ++ "ULL";
       c_bop := fun op =>
                  match op with
                  | Op.OPlus => "+"
                  | Op.OMinus => "-"
                  | Op.OTimes => "*"
                  | Op.OEq => "=="
                  | Op.OLt => "<"
                  | Op.OAnd => "&"
                  end%string;
       c_var := id;
       c_fun := id;
       c_act := fun _ _ _ => "#error";
    |}%string.

  Let bw := 64.
  Local Instance CImp64 : ImpCSyntaxParameters := CImp bw.

  Import ImpNotations.

  Local Coercion mword_of_N (z:BinNums.N) : mword := Word.NToWord bw z.
  Local Coercion ELit : mword >-> expr.
  Local Coercion EVar : varname >-> expr.

  Local Notation "e1 + e2" := (EOp Op.OPlus e1%bedrock_expr e2%bedrock_expr) : bedrock_expr.
  Local Notation "e1 - e2" := (EOp Op.OMinus e1%bedrock_expr e2%bedrock_expr) : bedrock_expr.
  Local Notation "e1 * e2" := (EOp Op.OTimes e1%bedrock_expr e2%bedrock_expr) : bedrock_expr.
  Local Notation "e1 == e2" := (EOp Op.OEq e1%bedrock_expr e2%bedrock_expr)
    (at level 100, no associativity) : bedrock_expr.
  Local Notation "e1 < e2" := (EOp Op.OLt e1%bedrock_expr e2%bedrock_expr) : bedrock_expr.
  Local Notation "e1 & e2" := (EOp Op.OAnd e1%bedrock_expr e2%bedrock_expr)
    (at level 40, no associativity) : bedrock_expr.

  Local Open Scope N_scope.
  Local Open Scope string_scope.

  Let left : varname := "left"%string.
  Let right : varname := "right"%string.
  Let mid : varname := "mid"%string.
  Let ret : varname := "ret"%string.
  Let target : varname := "target"%string.

  (* FIXME *)
  Local Notation "e1 >> e2" := (EOp Op.OAnd e1%bedrock_expr e2%bedrock_expr)
    (at level 60, no associativity) : bedrock_expr.
  (* FIXME *)
  Local Notation "e1 << e2" := (EOp Op.OAnd e1%bedrock_expr e2%bedrock_expr)
    (at level 60, no associativity) : bedrock_expr.

  Compute c_decl "uintptr_t" ("a"::"b"::nil)%list "sumdiff" ("x"::"y"::nil)%list.

  Compute
    String (Coq.Strings.Ascii.Ascii false true false true false false false false) ""++
    c_func string_eqb (fun x _ => "_"++ x) (left::right::target::nil)%list "bsearch" (ret::nil)%list (bedrock_func (

    while (left < right) {{
      mid = ((left+right) >> 4) << 3;
      ret =*(uintptr_t*) mid;
      if (ret < target) {{
        left = mid + 8
      }} else {{
        right = mid
      }}
    }};
    ret = left

         )).
End _example.