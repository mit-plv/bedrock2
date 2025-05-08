Require Import bedrock2.Syntax bedrock2.Variables. Import bopname.
Require Import coqutil.Datatypes.ListSet.
Require Import Coq.ZArith.BinIntDef Coq.Numbers.BinNums Coq.Numbers.DecimalString Strings.HexString.
Require Import Coq.Strings.String. Local Open Scope string_scope.

Definition prelude := "#include <stdint.h>
#include <string.h>
#include <assert.h>

typedef uintptr_t br_word_t;
#define BR_WORD_MAX UINTPTR_MAX
#if UINTPTR_MAX == UINT64_MAX
typedef int64_t br_signed_t;
#elif UINTPTR_MAX == UINT32_MAX
typedef int32_t br_signed_t;
#else
#error ""32-bit or 64-bit uintptr_t required""
#endif

static __attribute__((constructor)) void _br_preconditions(void) {
  static_assert(sizeof(br_word_t) == sizeof(br_signed_t), """");
  static_assert(UINTPTR_MAX <= BR_WORD_MAX, """");
  static_assert(~(intptr_t)0 == -(intptr_t)1, ""two's complement"");
  assert(((void)""two's complement"", ~(intptr_t)0 == -(intptr_t)1));
  br_word_t u = 1;
  assert(((void)""little-endian"", 1 == *(unsigned char *)&u));
  intptr_t i = 1;
  assert(((void)""little-endian"", 1 == *(unsigned char *)&i));
}


// Load and store

// ""An object shall have its stored value accessed only ... a character type.""
// These are prepreocessor macors so that they don't affect debug line numbers.
#define _br_load1(a) (*(uint8_t *)(a))
#define _br_store1(a, v) (*(uint8_t *)(a) = (v))

// do we have have language extensions for no-strict-aliasing load/store?
#if defined(__GNUC__) || defined(__clang__) ||                                 \
    (defined(_MSC_VER) && !defined(_M_IX86)) // __unaligned

#if defined(__GNUC__) || defined(__clang__)
typedef __attribute__((aligned(1), may_alias)) uint16_t _br_u16;
typedef __attribute__((aligned(1), may_alias)) uint32_t _br_u32;
typedef __attribute__((aligned(1), may_alias)) uint64_t _br_u64;
#else
typedef __unaligned uint16_t _br_u16;
typedef __unaligned uint32_t _br_u32;
typedef __unaligned uint64_t _br_u64;
#endif

#define _br_load2(a) (*(_br_u16 *)(a))
#define _br_load4(a) (*(_br_u32 *)(a))
#if BR_WORD_MAX == UINT32_MAX
#define _br_load(a) (*(_br_u32 *)(a))
#else
#define _br_load(a) (*(_br_u64 *)(a))
#endif

#define _br_store2(a, v) (*(_br_u16 *)(a) = (v))
#define _br_store4(a, v) (*(_br_u32 *)(a) = (v))
#if BR_WORD_MAX == UINT32_MAX
#define _br_store(a, v) (*(_br_u32 *)(a) = (v))
#else
#define _br_store(a, v) (*(_br_u64 *)(a) = (v))
#endif

#else // language extensions for no-strict-aliasing load/store

static inline br_word_t _br_load2(br_word_t a) {
  uint16_t r = 0;
  memcpy(&r, (void *)a, sizeof(r));
  return r;
}

static inline br_word_t _br_load4(br_word_t a) {
  uint32_t r = 0;
  memcpy(&r, (void *)a, sizeof(r));
  return r;
}

static inline br_word_t _br_load(br_word_t a) {
  br_word_t r = 0;
  memcpy(&r, (void *)a, sizeof(r));
  return r;
}

static inline void _br_store2(br_word_t a, uint16_t v) {
  memcpy((void *)a, &v, sizeof(v));
}

static inline void _br_store4(br_word_t a, uint32_t v) {
  memcpy((void *)a, &v, sizeof(v));
}

static inline void _br_store(br_word_t a, br_word_t v) {
  memcpy((void *)a, &v, sizeof(v));
}

#endif // language extensions for no-strict-aliasing load/store

static inline __attribute__((always_inline, unused))
br_word_t _br_mulhuu(br_word_t a, br_word_t b) {
  #if (UINTPTR_MAX == (UINTMAX_C(1)<<31) - 1 + (UINTMAX_C(1)<<31))
	  return ((uint64_t)a * b) >> 32;
  #elif (UINTPTR_MAX == (UINTMAX_C(1)<<63) - 1 + (UINTMAX_C(1)<<63))
    return ((unsigned __int128)a * b) >> 64;
  #else
    #error ""32-bit or 64-bit br_word_t required""
  #endif
}

static inline __attribute__((always_inline, unused))
br_word_t _br_divu(br_word_t a, br_word_t b) {
  if (!b) return -1;
  return a/b;
}

static inline __attribute__((always_inline, unused))
br_word_t _br_remu(br_word_t a, br_word_t b) {
  if (!b) return a;
  return a%b;
}
".

Definition LF : string := String (Coq.Strings.Ascii.Ascii false true false true false false false false) "".

Definition c_var := @id string.
Definition c_fun := @id string.

Definition c_byte_withoutcast b := HexString.of_N (Byte.to_N b).

Definition s_size (s : access_size) : string :=
  match s with
  | access_size.one => "1"
  | access_size.two => "2"
  | access_size.four => "4"
  | access_size.word => ""
  end.

Definition c_shamt e2 := "("++e2++"&(-1+8*sizeof(br_word_t))" ++ ")".

(* c_expr returns a br_word_t expressionn suitable as argument of "<" without parens *)
(* https://en.cppreference.com/w/c/language/operator_precedence *)
Fixpoint c_expr (e : expr) : string :=
  match e with
  | expr.literal v => "(br_word_t)"++HexString.of_Z v (* https://en.cppreference.com/w/cpp/language/integer_literal *)
  | expr.var x => c_var x
  | expr.load s ea => "_br_load" ++  s_size s ++ "(" ++ c_expr ea ++ ")"
  | expr.inlinetable s t index => "({ static const uint8_t _inlinetable["++HexString.of_Z (Z.of_nat (List.length t))++"] = {"++concat ", " (List.map c_byte_withoutcast t)++"}; _br_load"++s_size s++"((br_word_t)&_inlinetable["++c_expr index++"]); })"
  | expr.op1 op e1 =>
    let p1 := match e1 with expr.literal _ | expr.var _ | expr.op1 _ _ => c_expr e1 | _ => "(" ++ c_expr e1 ++ ")" end in
    match op with
    | op1.not => "~"++p1
    | op1.opp => "-"++p1
    end
  | expr.op op e1 e2 =>
    let r1 := c_expr e1 in
    let r2 := c_expr e2 in
    let p1 := match e1 with expr.literal _ | expr.var _ | expr.op1 _ _ => r1 | _ => "(" ++ r1 ++ ")" end in
    let p2 := match e2 with expr.literal _ | expr.var _ | expr.op1 _ _ => r2 | _ => "(" ++ r2 ++ ")" end in
    let a2 := match e2 with (* to be arithmetic-converted to br_word_t *)
              | expr.literal v =>
                if andb (Z.leb 0 v) (Z.ltb 0 (Z.pow 2 32))
                then HexString.of_Z v (* integer conversion rank <= br_uint *)
                else p2
              | _ => p2 end in
    let s2 := match e2 with (* shift amount 0 <= x < sizeof(br_word_t) *)
              | expr.literal v =>
                if andb (Z.leb 0 v) (Z.ltb 0 32)
                then DecimalString.NilZero.string_of_int (BinInt.Z.to_int v)
                else c_shamt p2
              | _ => p2 end in
    match op with
    | add => p1++"+"++a2
    | sub => p1++"-"++a2
    | mul => p1++"*"++a2
    | mulhuu => "_br_mulhuu(" ++ r1 ++ ", " ++ r2 ++ ")"
    | divu => "_br_divu(" ++ r1 ++ ", " ++ r2 ++ ")"
    | remu => "_br_remu(" ++ r1 ++ ", " ++ r2 ++ ")"
    | and => p1++"&"++a2
    | or  => p1++"|"++a2
    | xor => p1++"^"++a2
    | sru => p1++">>"++s2
    | slu => p1++"<<"++s2
    | srs => "(br_word_t)((br_signed_t)"++p1++">>"++s2++")"
    | lts => "(br_word_t)((br_signed_t)"++p1++"<"++"(br_signed_t)"++p2++")"
    | ltu => "(br_word_t)("++r1++"<"++r2++")"
    | eq => "(br_word_t)("++r1++"=="++r2++")"
    end
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
  | cmd.store s ea ev =>
    indent ++ "_br_store" ++ s_size s ++ "(" ++ c_expr ea ++ ", " ++ c_expr ev ++ ");" ++ LF
  | cmd.stackalloc x n body =>
    let tmp := "_br_stackalloc_"++x in (* might shadow if not fresh, likely type error... *)
    indent ++ "{ uint8_t "++tmp++"["++HexString.of_Z n++"] = {0}; "++x++" = (br_word_t)&"++tmp++";"++LF++
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

Definition fmt_c_decl (rett : string) (args : list String.string) (name : String.string) (retptrs : list String.string) : string :=
  let argstring : String.string :=
    (match args, retptrs with
    | nil, nil => "void"
    | _, _ => concat ", " (
        List.map (fun a => "br_word_t "++c_var a) args ++
        List.map (fun r => "br_word_t* "++c_var r) retptrs)
    end)
  in
  (rett ++ " " ++ c_fun name ++ "(" ++ argstring ++ ")").

Definition c_decl (f : String.string * func) :=
  let '(name, (args, rets, body)) := f in
  match rets with
  | nil => fmt_c_decl "void" args name nil
  | cons _ _ =>
    let retrenames := fst (rename_outs (List.removelast rets) (cmd.vars body)) in
     fmt_c_decl "br_word_t" args name (List.map snd retrenames)
  end ++ ";".


Definition c_func '(name, (args, rets, body)) :=
  let decl_retvar_retrenames : string * option String.string * list (String.string * String.string) :=
  match rets with
  | nil => (fmt_c_decl "void" args name nil, None, nil)
  | cons r0 _ =>
    let r0 := List.last rets r0 in
    let rets' := List.removelast rets in
    let retrenames := fst (rename_outs rets' (cmd.vars body)) in
    (fmt_c_decl "br_word_t" args name (List.map snd retrenames), Some r0, retrenames)
  end in
  let decl := fst (fst decl_retvar_retrenames) in
  let retvar := snd (fst decl_retvar_retrenames) in
  let retrenames := snd decl_retvar_retrenames in
  let localvars : list String.string := List_uniq String.eqb (
      let allvars := (List.app (match retvar with None => nil | Some v => cons v nil end) (cmd.vars body)) in
      (List_minus String.eqb allvars args)) in
  decl ++ " {" ++ LF ++
    let indent := "  " in
    (match localvars with nil => "" | _ => indent ++ "br_word_t " ++ concat ", " (List.map c_var localvars) ++ ";" ++ LF end) ++
    c_cmd indent body ++
    concat "" (List.map (fun '(o, optr) => indent ++ "*" ++ c_var optr ++ " = " ++ c_var o ++ ";" ++ LF) retrenames) ++
    indent ++ "return" ++ (match retvar with None => "" | Some rv => " "++c_var rv end) ++ ";" ++ LF ++
    "}" ++ LF.

Definition c_module (fs : list (String.string * func)) :=
  match fs with
  | nil => "#error ""c_module nil"" "
  | cons main fs =>
    concat LF (prelude :: List.map (fun f => "static " ++ c_decl f) fs) ++ LF ++ LF ++
    c_func main ++ LF ++
    concat LF (List.map (fun f => "static " ++ c_func f) fs)
  end.
