Require Import bedrock2.Syntax bedrock2.Variables. Import bopname.
Require Import coqutil.Datatypes.ListSet.
Require Import Coq.ZArith.BinIntDef Coq.Numbers.BinNums Coq.Numbers.DecimalString Strings.HexString.
Require Import Coq.Strings.String. Import Byte. Local Open Scope string_scope.

Definition prelude := "// Generated from Bedrock code. Avoid editing directly.
#include <stdint.h>
#include <string.h>
#include <assert.h>

#define BR_WORD_MAX UINTPTR_MAX
typedef uintptr_t br_word_t;
typedef intptr_t br_signed_t;

static_assert(sizeof(br_word_t) == sizeof(br_signed_t), ""signed size"");
static_assert(UINTPTR_MAX <= BR_WORD_MAX, ""pointer fits in int"");
static_assert(~(br_signed_t)0 == -(br_signed_t)1, ""two's complement"");

#if __STDC_VERSION__ >= 202311L && __has_include(<stdbit.h>)
  #include <stdbit.h>
  static_assert(__STDC_ENDIAN_NATIVE__ == __STDC_ENDIAN_LITTLE__, ""little-endian"");
#elif defined(__GNUC__) && defined(__BYTE_ORDER__) && defined(__ORDER_LITTLE_ENDIAN__)
  static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, ""little-endian"");
#elif defined(_MSC_VER) && !defined(__clang__) &&                              \
    (defined(_M_IX86) || defined(_M_X64) || defined(_M_ARM) || defined(_M_ARM64))
  // these MSVC targets are little-endian
#else
  #error ""failed to confirm that target is little-endian""
#endif

// ""An object shall have its stored value accessed only ... a character type.""
static inline br_word_t _br_load1(br_word_t a) {
  return *((uint8_t *)a);
}

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

static inline void _br_store1(br_word_t a, uint8_t v) {
  *((uint8_t *)a) = v;
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

static inline br_word_t _br_mulhuu(br_word_t a, br_word_t b) {
  #if BR_WORD_MAX == UINT32_MAX
	  return ((uint64_t)a * b) >> 32;
  #elif BR_WORD_MAX == UINT64_MAX && (defined(__GNUC__) || defined(__clang__))
    return ((unsigned __int128)a * b) >> 64;
  #elif defined(_M_X64)
    uint64_t hi;
    _umul128(a, b, &hi);
    return hi;
  #elif defined(_M_ARM64)
    return __umulh(a, b);
  #else
    // See full_mul.v
    br_word_t hh, lh, hl, low, second_halfword_w_oflow, n, ll, M;
    n = ((((0u-(br_word_t)0x1)>>27)&0x3f)+0x1)>>1;
    M = ((br_word_t)0x1<<n)-0x1;
    ll = (a&M)*(b&M);
    lh = (a&M)*(b>>n);
    hl = (a>>n)*(b&M);
    hh = (a>>n)*(b>>n);
    second_halfword_w_oflow = ((ll>>n)+(lh&M))+(hl&M);
    return ((hh+(lh>>n))+(hl>>n))+(second_halfword_w_oflow>>n);
  #endif
}

static inline br_word_t _br_divu(br_word_t a, br_word_t b) {
  if (!b) return -1;
  return a/b;
}

static inline br_word_t _br_remu(br_word_t a, br_word_t b) {
  if (!b) return a;
  return a%b;
}
".

Definition LF : string := String (Coq.Strings.Ascii.Ascii false true false true false false false false) "".

Definition c_var := @id string.
Definition c_fun := @id string.

Definition c_lit w := 
  let s := if Z.ltb (Z.abs w) 0xff
    then DecimalString.NilZero.string_of_int (BinInt.Z.to_int w)
    else HexString.of_Z w in
    let endswith_e s := Byte.eqb (List.last (list_byte_of_string s) "_"%byte) "e"%byte in
    let s := if endswith_e s then s++" " else s in (* 0xe+1 --> invalid suffix on integer constant *)
  if Z.ltb w 0
  then "#error ""C does not support negative literals (" ++ s ++ ")"""
  else s.

Definition c_op1 op e :=
  match op with
  | op1.not => "~"++e
  | op1.opp => "0u-" ++ e (* silence MSVC warning C4146 *)
  end%string.

Definition c_bop e1 op e2 :=
  match op with
  | add => e1++"+"++e2
  | sub => e1++"-"++e2
  | mul => e1++"*"++e2
  | mulhuu => "_br_mulhuu(" ++ e1 ++ ", " ++ e2 ++ ")"
  | divu => "_br_divu(" ++ e1 ++ ", " ++ e2 ++ ")"
  | remu => "_br_remu(" ++ e1 ++ ", " ++ e2 ++ ")"
  | and => e1++"&"++e2
  | or => e1++"|"++e2
  | xor => e1++"^"++e2
  | sru => e1++">>"++e2
  | slu => e1++"<<"++e2
  | srs => "(br_word_t)((br_signed_t)"++e1++">>"++e2++")"
  | lts => "(br_word_t)((br_signed_t)"++e1++"<"++"(br_signed_t)"++e2++")"
  | ltu => "(br_word_t)("++e1++"<"++e2++")"
  | eq => "(br_word_t)("++e1++"=="++e2++")"
  end%string.

(* for load1, load2, load4, load, etc *)
Definition size_suffix (s : access_size) : string :=
  match s with
  | access_size.one => "1"
  | access_size.two => "2"
  | access_size.four => "4"
  | access_size.word => ""
  end.

Definition c_inlinetable t :=
  "static const uint8_t _inlinetable["++c_lit (Z.of_nat (List.length t))++"] = {"++
      concat ", " (List.map HexString.of_N (List.map Byte.to_N t))++"};".
Definition c_loadtable s i :=
  "_br_load"++size_suffix s++"((br_word_t)&_inlinetable["++i++"])".

Fixpoint c_expr (e : expr) : string :=
  let p_expr e := match e with (* parenthesized expression *)
                  | expr.literal _ | expr.var _ => c_expr e
                  | expr.op1 _ _ (* MSVC *) | _ => "(" ++ c_expr e ++ ")"
                  end in
  let p_operand2 e := match e with (* e is passed to binary operator whose 1st*)
    (* operand is a br_word_t, so if it is a literal, we can avoid a cast per *)
    (* usual arithmetic conversions. E.g. [a+5] instead of [a+(br_word_t)5]. *)
                      | expr.literal v => c_lit v
                      | _ => p_expr e
                  end in
  let p_shamt e := match e with (* shift amount, safely truncated *)
                   | expr.literal v =>
                   if (Z.leb 0 v && Z.ltb v 32)%bool then c_lit v
                   else    "("++p_expr e++"&(sizeof(br_word_t)*8-1))"
                   | _ =>  "("++p_expr e++"&(sizeof(br_word_t)*8-1))"
                   end in
  match e with
  | expr.literal v => "(br_word_t)" ++ c_lit v
  | expr.var x => c_var x
  | expr.load s ea => "_br_load" ++ size_suffix s++ "(" ++ c_expr ea ++ ")"
  | expr.inlinetable s t index =>  (* x = tbl[i] is handled in [c_cmd]. GNUC fallback: *)
    "({ " ++ c_inlinetable t ++ c_loadtable s (c_expr index) ++ "; })"
  | expr.op1 op e1 => c_op1 op (p_expr e1)
  | expr.op op e1 e2 =>
    match op with
    | slu | sru | srs => c_bop (p_expr e1) op (p_shamt e2)
    | add | sub | mul
    | and | or  | xor => c_bop (p_expr e1) op (p_operand2 e2)
    | _  => c_bop (p_expr e1) op (p_expr e2)
    end
  | expr.lazy_and e1 e2 => p_expr e1 ++ " && " ++ p_expr e2
  | expr.lazy_or e1 e2 => p_expr e1 ++ " || " ++ p_expr e2
  | expr.ite c e1 e2 => p_expr c ++ " ? " ++ p_expr e1 ++ " : " ++ p_expr e2
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
    => indent ++ "_br_store" ++ size_suffix s ++ "(" ++ c_expr ea ++ ", " ++ c_expr ev ++ ");" ++ LF
  | cmd.stackalloc x n body =>
    (* Extend the lifetime of the allocation until the end of ambient block,
     * favoring readability over timely deallocation (which clang et al don't
     * do anyway. However, name collisions can cause compilation errors. *)
    let tmp := "_br_stackalloc_"++x in
    indent ++ "uint8_t "++tmp++"["++c_lit n++"] = {0}; "++x++" = (br_word_t)&"++tmp++";"++LF++
    c_cmd indent body
  | cmd.set x (expr.inlinetable s t ei) =>
  indent ++ "{ " ++ c_inlinetable t ++ " " ++ x ++ " = " ++ c_loadtable s (c_expr ei) ++ "; }" ++ LF
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
    (match retvar with None => "" | Some rv => indent ++ "return " ++c_var rv ++ ";" ++ LF end) ++
    "}" ++ LF.

Definition c_module (fs : list (String.string * func)) :=
  match fs with
  | nil => "#error ""c_module nil"" "
  | cons main fs =>
    concat LF (prelude :: List.map (fun f => "static " ++ c_decl f) fs) ++ LF ++ LF ++
    c_func main ++ LF ++
    concat LF (List.map (fun f => "static " ++ c_func f) fs)
  end.
