Require Import bedrock2.Syntax bedrock2.Variables. Import bopname.

Require Import Coq.ZArith.BinIntDef Coq.Numbers.BinNums Coq.Numbers.DecimalString.
Require Import Coq.Strings.String. Local Open Scope string_scope.

Definition prelude := "#include <stdint.h>
#include <memory.h>

// LITTLE-ENDIAN memory access is REQUIRED
// the following two functions are required to work around -fstrict-aliasing
static inline uintptr_t _br2_load(uintptr_t a, size_t sz) {
  uintptr_t r = 0;
  memcpy(&r, (void*)a, sz);
  return r;
}

static inline void _br2_store(uintptr_t a, uintptr_t v, size_t sz) {
  memcpy((void*)a, &v, sz);
}
".

Definition LF : string := String (Coq.Strings.Ascii.Ascii false true false true false false false false) "".

Definition c_var := @id string.
Definition c_fun := @id string.

Definition c_lit w := "(uintptr_t)" ++ DecimalString.NilZero.string_of_int (BinInt.Z.to_int w) ++ "ULL".

Definition c_bop e1 op e2 :=
  match op with
  | add => e1++"+"++e2
  | sub => e1++"-"++e2
  | mul => e1++"*"++e2
  | mulhuu => "sizeof(intptr_t) == 4 ? ((uint64_t)"++e1++"*"++e2++")>>32 : ((__uint128_t)"++e1++"*"++e2++")>>64"
  | divu => e1++"/"++e2
  | remu => e1++"%"++e2
  | and => e1++"&"++e2
  | or => e1++"|"++e2
  | xor => e1++"^"++e2
  | sru => e1++">>"++e2
  | slu => e1++"<<"++e2
  | srs => "(intptr_t)"++e1++">>"++e2
  | lts => "(intptr_t)"++e1++"<"++"(intptr_t)"++e2
  | ltu => e1++"<"++e2
  | eq => e1++"=="++e2
  end%string.

Definition c_size (s : access_size) : string :=
  match s with
  | access_size.one => "1"
  | access_size.two => "2"
  | access_size.four => "4"
  | access_size.word => "sizeof(uintptr_t)"
  end.

Fixpoint c_expr (e : expr) : string :=
  match e with
  | expr.literal v => c_lit v
  | expr.var x => c_var x
  | expr.load s ea => "_br2_load(" ++ c_expr ea ++ ", " ++ c_size s++ ")"
  | expr.inlinetable s t index => "TODO_inlinetable"
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
Definition c_act := c_call.

Fixpoint c_cmd (indent : string) (c : cmd) : string :=
  match c with
  | cmd.store s ea ev
    => indent ++ "_br2_store(" ++ c_expr ea ++ ", " ++ c_expr ev ++ ", " ++ c_size s ++ ");" ++ LF
  | cmd.stackalloc x n body =>
    indent ++ c_var x ++ " = alloca(" ++ c_lit n ++ "); // TODO untested" ++ LF ++
    c_cmd indent body
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

Definition fmt_c_decl (rett : string) (args : list String.string) (name : String.string) (retptrs : list String.string) : string :=
  (rett ++ " " ++ c_fun name ++ "(" ++ concat ", " (
                  List.map (fun a => "uintptr_t "++c_var a) args ++
                  List.map (fun r => "uintptr_t* "++c_var r) retptrs) ++
                ")").

Definition c_decl (f : String.string * (list String.string * list String.string * cmd)) :=
  let '(name, (args, rets, body)) := f in
  match rets with
  | nil => fmt_c_decl "void" args name nil
  | cons _ _ => fmt_c_decl "uintptr_t" args name (List.removelast rets)
  end ++ ";".

Definition rename_away_from x xs :=
  let x' := "_" ++ x in
  if List.existsb (String.eqb x') xs
  then "#error rename_away_from '" ++ x ++"' = '" ++ x' ++"'"
  else x'.

Fixpoint rename_outs (outs : list String.string) (used : list String.string) : list (String.string*String.string) * list String.string :=
  match outs with
  | cons o outs' =>
    let rec := rename_outs outs' used in
    let (outrenames, used) := (fst rec, snd rec) in
    let optr := rename_away_from o used in
    (cons (o, optr) outrenames, cons o used)
  | nil => (nil, used)
  end.

Definition c_func '(name, (args, rets, body)) :=
  let decl_retvar_retrenames : string * option String.string * list (String.string * String.string) :=
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
  let localvars : list String.string := List_uniq String.eqb (
      let allvars := (List.app (match retvar with None => nil | Some v => cons v nil end) (cmd.vars body)) in
      (List_minus String.eqb allvars args)) in
  decl ++ " {" ++ LF ++
    let indent := "  " in
    (match localvars with nil => "" | _ => indent ++ "uintptr_t " ++ concat ", " (List.map c_var localvars) ++ ";" ++ LF end) ++
    c_cmd indent body ++
    concat "" (List.map (fun '(o, optr) => indent ++ "*" ++ c_var optr ++ " = " ++ c_var o ++ ";" ++ LF) retrenames) ++
    indent ++ "return" ++ (match retvar with None => "" | Some rv => " "++c_var rv end) ++ ";" ++ LF ++
    "}" ++ LF.

Definition c_module (fs : list (String.string * (list String.string * list String.string * cmd))) :=
  match fs with
  | nil => "#error ""c_module nil"" "
  | cons main fs =>
    concat LF (prelude :: List.map (fun f => "static " ++ c_decl f) fs) ++ LF ++ LF ++
    c_func main ++ LF ++
    concat LF (List.map (fun f => "static " ++ c_func f) fs)
  end.
