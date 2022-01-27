Require Import bedrock2.Syntax bedrock2.Variables. Import bopname.
Require Import coqutil.Datatypes.ListSet.
Require Import Coq.ZArith.BinIntDef Coq.Numbers.BinNums Coq.Numbers.DecimalString.
Require Import Coq.Strings.String. Local Open Scope string_scope.

Definition prelude := "#include <stdint.h>
#include <string.h>

// We use memcpy to work around -fstrict-aliasing.
// A plain memcpy is enough on clang 10, but not on gcc 10, which fails
// to infer the bounds on an integer loaded by memcpy.
// Adding a range mask after memcpy in turn makes slower code in clang.
// Loading individual bytes, shifting them together, and or-ing is fast
// on clang and sometimes on GCC, but other times GCC inlines individual
// byte operations without reconstructing wider accesses.
// The little-endian idiom below seems fast in gcc 9+ and clang 10.
static __attribute__((always_inline)) inline uintptr_t
_br2_load(uintptr_t a, uintptr_t sz) {
  switch (sz) {
  case 1: { uint8_t  r = 0; memcpy(&r, (void*)a, 1); return r; }
  case 2: { uint16_t r = 0; memcpy(&r, (void*)a, 2); return r; }
  case 4: { uint32_t r = 0; memcpy(&r, (void*)a, 4); return r; }
  case 8: { uint64_t r = 0; memcpy(&r, (void*)a, 8); return r; }
  default: __builtin_unreachable();
  }
}

static __attribute__((always_inline)) inline void
_br2_store(uintptr_t a, uintptr_t v, uintptr_t sz) {
  memcpy((void*)a, &v, sz);
}
".

Definition LF : string := String (Coq.Strings.Ascii.Ascii false true false true false false false false) "".

Definition c_var := @id string.
Definition c_fun := @id string.

Definition c_lit w := "(uintptr_t)" ++ DecimalString.NilZero.string_of_int (BinInt.Z.to_int w) ++ "ULL".
Definition c_byte_withoutcast b := DecimalString.NilZero.string_of_uint (BinNatDef.N.to_uint (Byte.to_N b)).

Definition c_bop e1 op e2 :=
  match op with
  | add => e1++"+"++e2
  | sub => e1++"-"++e2
  | mul => e1++"*"++e2
  | mulhuu => "(uintptr_t)(sizeof(intptr_t) == 4 ? ((uint64_t)"++e1++"*"++e2++")>>32 : ((__uint128_t)"++e1++"*"++e2++")>>64)"
  | divu => e1++"/"++e2
  | remu => e1++"%"++e2
  | and => e1++"&"++e2
  | or => e1++"|"++e2
  | xor => e1++"^"++e2
  | sru => e1++">>"++e2
  | slu => e1++"<<"++e2
  | srs => "(uintptr_t)((intptr_t)"++e1++">>"++e2++")"
  | lts => "(uintptr_t)((intptr_t)"++e1++"<"++"(intptr_t)"++e2++")"
  | ltu => "(uintptr_t)("++e1++"<"++e2++")"
  | eq => "(uintptr_t)("++e1++"=="++e2++")"
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
  | expr.inlinetable s t index => "({ static const uint8_t _inlinetable["++c_lit (Z.of_nat (List.length t))++"] = {"++concat ", " (List.map c_byte_withoutcast t)++"}; _br2_load((uintptr_t)&_inlinetable["++c_expr index++"], "++c_size s++"); })"
  | expr.op op e1 e2 => c_bop ("(" ++ c_expr e1 ++ ")") op ("(" ++ c_expr e2 ++ ")")
  | expr.lazy_and e1 e2 => "(" ++ c_expr e1 ++ ") && (" ++ c_expr e2 ++ ")"
  | expr.lazy_or e1 e2 => "(" ++ c_expr e1 ++ ") || (" ++ c_expr e2 ++ ")"
  | expr.ite c e1 e2 => "(" ++ c_expr c ++ ") ? (" ++ c_expr e1 ++ ") : (" ++ c_expr e2 ++ ")"
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
    let tmp := "_br2_stackalloc_"++x in (* might shadow if not fresh, likely type error... *)
    indent ++ "{ uint8_t "++tmp++"["++c_lit n++"]; "++x++" = (uintptr_t)&"++tmp++";"++LF++
    c_cmd indent body ++
    indent ++ "}" ++ LF
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
  let argstring : String.string :=
    (match args, retptrs with
    | nil, nil => "void"
    | _, _ => concat ", " (
        List.map (fun a => "uintptr_t "++c_var a) args ++
        List.map (fun r => "uintptr_t* "++c_var r) retptrs)
    end)
  in
  (rett ++ " " ++ c_fun name ++ "(" ++ argstring ++ ")").

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


(* `globals` is a list of varnames that should be treated as global variables,
   that is, they are removed from the list of local declarations, and it is
   checked that they don't clash with local names *)
Definition c_func_with_globals globals '(name, (args, rets, body)) :=
  let name_clashes := list_intersect String.eqb
    globals (name :: args ++ rets ++ cmd.mod_vars body) in
  match name_clashes with
  | cons _ _ => "#error ""In " ++ name ++ ", locals clash with globals (" ++
                String.concat ", " name_clashes ++ ")"" " ++ LF
  | _ =>
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
      (List_minus String.eqb allvars (List.app args globals))) in
  decl ++ " {" ++ LF ++
    let indent := "  " in
    (match localvars with nil => "" | _ => indent ++ "uintptr_t " ++ concat ", " (List.map c_var localvars) ++ ";" ++ LF end) ++
    c_cmd indent body ++
    concat "" (List.map (fun '(o, optr) => indent ++ "*" ++ c_var optr ++ " = " ++ c_var o ++ ";" ++ LF) retrenames) ++
    indent ++ "return" ++ (match retvar with None => "" | Some rv => " "++c_var rv end) ++ ";" ++ LF ++
    "}" ++ LF
  end.

Definition c_func: func -> String.string := c_func_with_globals nil.

Definition c_module_with_globals (globals: list String.string) (fs : list func) :=
  match fs with
  | nil => "#error ""c_module nil"" "
  | cons main fs =>
    concat LF (prelude :: List.map (fun f => "static " ++ c_decl f) fs) ++ LF ++ LF ++
    c_func main ++ LF ++
    concat LF (List.map (fun f => "static " ++ c_func_with_globals globals f) fs)
  end.

Definition c_module : list func -> String.string := c_module_with_globals nil.
