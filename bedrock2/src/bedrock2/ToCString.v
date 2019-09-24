Require Import coqutil.Macros.subst coqutil.Macros.unique bedrock2.Syntax bedrock2.Variables.

Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.BinIntDef.
Require Import Coq.Strings.String.

Class parameters := {
  syntax :> Syntax.parameters;
  varname_eqb : varname -> varname -> bool;
  rename_away_from : varname -> list varname -> varname;
  c_lit : Z -> String.string;
  c_bop : string -> bopname -> string -> string;
  c_var : varname -> String.string;
  c_fun : funname -> String.string;
  c_act : list varname -> actname -> list String.string -> string;
}.

Section ToCString.
  Local Open Scope string_scope.
  Context {p : unique! parameters}.
  Definition LF : string := String (Coq.Strings.Ascii.Ascii false true false true false false false false) "".
  Local Open Scope string_scope.

  Definition c_size (s : access_size) : string :=
    match s with
    | access_size.one => "uint8_t"
    | access_size.two => "uint16_t"
    | access_size.four => "uint32_t"
    | access_size.word => "uintptr_t"
    end%Z.

  Fixpoint c_expr (e : expr) : string :=
    match e with
    | expr.literal v => c_lit v
    | expr.var x => c_var x
    | expr.load s ea => "*(" ++ c_size s ++ "*)(" ++ c_expr ea ++ ")"
    | expr.op op e1 e2 => c_bop ("(" ++ c_expr e1 ++ ")") op ("(" ++ c_expr e2 ++ ")")
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

  Definition c_call (args : list string) (f : string) (es : list string) :=
    match args with
    | nil =>
      f ++ "(" ++ concat ", " es ++ ");" ++ LF
    | ((x::_)%list as binds)  =>
      List.last binds x ++ " = " ++ f ++ "(" ++ concat ", " (es ++ List.map (fun x => "&"++x) (List.removelast binds)) ++ ");" ++ LF
    end.

  Fixpoint c_cmd (indent : string) (c : cmd) : string :=
    match c with
    | cmd.store s ea ev
      => indent ++ "*("++c_size s++"*)(" ++ c_expr ea ++ ") = " ++ c_expr ev ++ ";" ++ LF
    | cmd.set x ev =>
      indent ++ c_var x ++ " = " ++ c_expr ev ++ ";" ++ LF
    | cmd.unset x =>
      indent ++ "// unset " ++ c_var x ++ LF
    | cmd.cond eb t f =>
      indent ++ "if (" ++ c_expr eb ++ ") {" ++ LF ++
        c_cmd ("  "++indent) t ++
      indent ++ "} else {" ++ LF ++
        c_cmd ("  "++indent) f ++
      indent ++ "}" ++ LF
    | cmd.while eb c =>
      indent ++ "while (" ++ c_expr eb ++ ") {" ++ LF ++
        c_cmd ("  "++indent) c ++
      indent ++ "}" ++ LF
    | cmd.seq c1 c2 =>
      c_cmd indent c1 ++
      c_cmd indent c2
    | cmd.skip =>
      indent ++ "/*skip*/" ++ LF
    | cmd.call args f es =>
      indent ++ c_call (List.map c_var args) (c_fun f) (List.map c_expr es)
    | cmd.interact binds action es =>
      indent ++ c_act binds action (List.map c_expr es)
    end.

  Definition fmt_c_decl (rett : string) (args : list varname) (name : funname) (retptrs : list varname) : string :=
    (rett ++ " " ++ c_fun name ++ "(" ++ concat ", " (
                    List.map (fun a => "uintptr_t "++c_var a) args ++
                    List.map (fun r => "uintptr_t* "++c_var r) retptrs) ++
                  ")").

  Definition c_decl (f : funname * (list varname * list varname * cmd)) :=
    let '(name, (args, rets, body)) := f in
    match rets with
    | nil => fmt_c_decl "void" args name nil
    | cons _ _ => fmt_c_decl "uintptr_t" args name (List.removelast rets)
    end ++ ";".

  Fixpoint rename_outs (outs : list varname) (used : list varname) : list (varname*varname) * list varname :=
    match outs with
    | cons o outs' =>
      let rec := rename_outs outs' used in
      let (outrenames, used) := (fst rec, snd rec) in
      let optr := rename_away_from o used in
      (cons (o, optr) outrenames, cons o used)
    | nil => (nil, used)
    end.

  Definition c_func '(name, (args, rets, body)) :=
    let decl_retvar_retrenames : string * option varname * list (varname * varname) :=
    match rets with
    | nil => (fmt_c_decl "void" args name nil, None, nil)
    | cons r0 _ =>
      let r0 := List.last rets r0 in
      let rets' := List.removelast rets in
      let retrenames := fst (rename_outs rets' (cmd.vars body)) in
      (fmt_c_decl "uintptr_t" args name (List.map snd retrenames), Some r0, retrenames)
    end in
    let decl := fst (fst decl_retvar_retrenames) in
    let retvar := snd (fst decl_retvar_retrenames) in
    let retrenames := snd decl_retvar_retrenames in
    let localvars : list varname := List_uniq varname_eqb (
        let allvars := (List.app (match retvar with None => nil | Some v => cons v nil end) (cmd.vars body)) in
        (List_minus varname_eqb allvars args)) in
    decl ++ " {" ++ LF ++
      let indent := "  " in
      (match localvars with nil => "" | _ => indent ++ "uintptr_t " ++ concat ", " (List.map c_var localvars) ++ ";" ++ LF end) ++
      c_cmd indent body ++
      concat "" (List.map (fun '(o, optr) => indent ++ "*" ++ c_var optr ++ " = " ++ c_var o ++ ";" ++ LF) retrenames) ++
      indent ++ "return" ++ (match retvar with None => "" | Some rv => " "++c_var rv end) ++ ";" ++ LF ++
      "}" ++ LF.

  Definition c_module (fs : list (funname * (list varname * list varname * cmd))) :=
    match fs with
    | nil => "#error ""c_module nil"" "
    | cons main fs =>
      concat LF (List.map (fun f => "static " ++ c_decl f) fs) ++ LF ++ LF ++
      c_func main ++ LF ++
      concat LF (List.map (fun f => "static " ++ c_func f) fs)
    end.
End ToCString.
