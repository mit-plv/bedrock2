From bedrock2 Require Import Syntax NotationsCustomEntry.
Local Open Scope string_scope. Local Open Scope Z_scope.

Example addsub := func! (a, b) ~> (x, y) {
  x = a + b;
  y = a - b
}.

Example addsub_test := func! () ~> ret {
  unpack! ret, ret = addsub($14, $7);
  ret = ret - $7
}.

From bedrock2 Require Import WeakestPrecondition ProgramLogic BasicC64Semantics.
Import coqutil.Word.Interface.

Local Instance spec_of_addsub : spec_of "addsub" :=
  fnspec! "addsub" a b ~> x y,
  { requires m t := True; ensures M T := m=M /\ t=T /\
    x = word.add a b /\ y = word.sub a b }.

Lemma addsub_correct : program_logic_goal_for_function! addsub.
Proof. repeat straightline. Qed.

(*
Require Import bedrock2.ToCString coqutil.Macros.WithBaseName.
Compute c_module &[,addsub_test; addsub].
*)

(*
uintptr_t addsub_test(void) {
  uintptr_t ret;
  ret = addsub((uintptr_t)(UINTMAX_C(14)), (uintptr_t)(UINTMAX_C(7)), &ret);
  ret = (ret)-((uintptr_t)(UINTMAX_C(7)));
  return ret;
}

static uintptr_t addsub(uintptr_t a, uintptr_t b, uintptr_t* _x) {
  uintptr_t x, y;
  x = (a)+(b);
  y = (a)-(b);
  *_x = x;
  return y;
}
*)
