Require Coq.Strings.String.
Definition string_eqb a b := andb (String.prefix a b) (String.prefix b a).

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

Module access_size.
  Inductive access_size := one | two | four | eight. (* bytes *)
  Definition to_nat (s : access_size) :=
    match s with
    | one => 1
    | two => 2
    | four => 4
    | eight => 8
    end.
End access_size. Notation access_size := access_size.access_size.

Section ImpSyntax.
  Goal True. let cls := constr:(ImpSyntaxParameters) in match constr:(Set) with _ => (let none := constr:(_:cls) in idtac); fail 99 "DUPLICATE INSTANCE" | _ => idtac end. Abort.
  Context {p : ImpSyntaxParameters}.
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
    | ELoad s ea => "(" ++ c_size s ++ "*)(" ++ c_expr ea ++ ")"
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

Import String.

Inductive struct :=
| Struct (_ : list (string * (access_size + struct))).

Fixpoint sizeof_struct (s : struct) {struct s} : nat :=
  match s with
  | (Struct ls) =>
    (fix sizeof_fields (l : list _) {struct l} : nat :=
       match l with
       | nil => O
       | cons (_, f) l' =>
         (match f with inl s => access_size.to_nat s | inr s' => sizeof_struct s' end)
         + sizeof_fields l'
       end
    ) ls
  end.

Definition sizeof (s:access_size + struct) :=
  match s with
  | inl s => access_size.to_nat s
  | inr s => sizeof_struct s
  end.

Definition slookup (field : string) (s : struct) : option (nat * (access_size + struct)) :=
  match s with
  | (Struct ls) =>
    (fix llookup (l : list _) {struct l} : option (nat * (access_size + struct)) :=
       match l with
       | nil => None
       | cons (f, ftype) l' =>
         if string_eqb f field
         then Some (O, ftype)
         else match llookup l' with
              | None => None
              | Some (o, t) => Some (sizeof ftype + o, t)
              end
       end
    ) ls
  end.

Fixpoint rlookup fieldnames (s : access_size + struct) : option (nat * (access_size + struct)) :=
  match fieldnames, s with
  | nil, inl a => Some (0, inl a)
  | nil, inr a => Some (0, inr a)
  | cons f fieldnames', inr s =>
    match slookup f s with
    | None => None
    | Some (o, s') =>
      match rlookup fieldnames' s' with
      | None => None
      | Some (o', s') => Some (o + o', s')
      end
    end
  | _, _ => None
  end.

Section __test.
  Import String.
  Open Scope string_scope.
  Import List.
  Import ListNotations.
  Import access_size.
  
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
  Definition utcb_segment := Struct (
   [ ("sel", inl two); ("ar", inl two); ("limit", inl four); ("base", inl mword) ]
   ++ match mword with eight => [] | _ => [("reserved", inl mword)] end).

  Definition exception_state := Struct (
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
    ; ("es", inr utcb_segment); ("cs", inr utcb_segment); ("ss", inr utcb_segment); ("ds", inr utcb_segment); ("gs", inr utcb_segment); ("ldtr", inr utcb_segment); ("tr", inr utcb_segment); ("gdtr", inr utcb_segment); ("idtr", inr utcb_segment)
    ; ("tsc_val", inl eight); ("tsc_off", inl eight)
    ] ).
  End with_mword.

  Compute slookup "dr7" (exception_state eight).
  Compute rlookup ("es"::nil) (inr (exception_state eight)).
  Compute rlookup ("es"::"sel"::nil) (inr (exception_state eight)).
  (* e as utcb field ["es; "sel"] *)
  (* e as utcb index 5 field ["es; "sel"] *)
  (* e index 5 as utcb field ["es; "sel"] *)
End __test.

Module ImpNotations.
  Delimit Scope bedrock_var with bedrock_var.

  Delimit Scope bedrock_expr with bedrock_expr.
  Bind Scope bedrock_expr with expr.
  Notation "(uintptr_t) v 'ULL'" := (ELit v)
   (at level 1, no associativity, format "(uintptr_t) v 'ULL'") : bedrock_expr.

  Delimit Scope bedrock_stmt with bedrock_stmt.
  Notation "'/*skip*/'" := SSkip
    : bedrock_stmt.
  Notation "x = e" := (SSet x%bedrock_var e%bedrock_expr)
    : bedrock_stmt.
  Notation "*(uint8*) e" := (ELoad access_size.one e%bedrock_expr)
    (at level 10, no associativity) : bedrock_expr.
  Notation "*(uint16*) e" := (ELoad access_size.two e%bedrock_expr)
    (at level 10, no associativity) : bedrock_expr.
  Notation "*(uint32*) e" := (ELoad access_size.four e%bedrock_expr)
    (at level 10, no associativity) : bedrock_expr.
  Notation "*(uint64_t*) e" := (ELoad access_size.eight e%bedrock_expr)
    (at level 10, no associativity) : bedrock_expr.

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


Module Op.
  Inductive binop : Set := OPlus : binop | OMinus : binop | OTimes : binop | OEq : binop | OLt : binop | OAnd : binop.
End Op.
Require bbv.Word.
(*
Module Word.
  Definition word : nat -> Type. Admitted.
  Definition wordToN {n} (_:word n) : BinNums.N. Admitted.
  Definition NToWord (n:nat) (_:BinNums.N) : word n. Admitted.
End Word.
*)
Require DecimalN.
Require DecimalString.

Module _example.
  Import String.
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
                                 (*
                  | ? => "<<"
                  | ? => ">>"

                  | ? => fun a b => (b == 0 ? a / b : 0)
                   
                  | ? => fun a b => (intptr_t)a * (intptr_t)b
                  | cmov br ? t : f  => ?

                  (* 2-output mul *)
                                  *)
                  end%string;
       c_var := id;
       c_fun := id;
       c_act := fun _ _ _ => "#error";
    |}%string.

  Let bw := 64.
  Local Instance CImp64 : ImpCSyntaxParameters := CImp bw.


  Local Coercion mword_of_N (z:BinNums.N) : mword := Word.NToWord bw z.
  Local Coercion ELit : mword >-> expr.
  Local Coercion EVar : varname >-> expr.
  Import ImpNotations.

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

  Local Notation uint64_t := access_size.eight.

  Compute
    String (Coq.Strings.Ascii.Ascii false true false true false false false false) ""++
    c_func string_eqb (fun x _ => "_"++ x) (left::right::target::nil)%list "bsearch" (ret::nil)%list (bedrock_func (
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

         )).
End _example.