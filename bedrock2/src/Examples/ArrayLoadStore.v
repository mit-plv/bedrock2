Require Import bedrock2.Syntax bedrock2.StringNamesSyntax.
Require Import bedrock2.NotationsCustomEntry coqutil.Z.HexNotation.
Require Import bedrock2.FE310CSemantics.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Coercion literal (z : Z) : expr := expr.literal z.
Local Coercion var (x : String.string) : expr := expr.var x.
Local Definition bedrock_func : Type := funname * (list varname * list varname * cmd).
Local Coercion name_of_func (f : bedrock_func) := fst f.

Definition tf : bedrock_func := 
    let buf : varname := "buf" in
    let len : varname := "len" in
    let i : varname := "i" in
    let j : varname := "j" in
    let r : varname := "r" in
  ("tf", ([buf; len; i; j], [], bedrock_func_body:(
    require ( i < len ) else { /*skip*/ };
    store1(buf + i, constr:(0));
    require ( j < len ) else { r = (constr:(-1)) };
    r = (load1(buf + j))
  ))).

From bedrock2 Require Import BasicC64Semantics ProgramLogic.
From bedrock2 Require Import Array Scalars Separation.
From coqutil Require Import Word.Interface Map.Interface.

Local Instance spec_of_tf : spec_of "tf" := fun functions =>
  forall t m buf len bs i j R,
    (sep (array ptsto (word.of_Z 1) buf bs) R) m ->
    word.unsigned len = Z.of_nat (List.length bs) ->
    WeakestPrecondition.call functions "tf" t m [buf; len; i; j]
    (fun T M rets => True).

From coqutil.Tactics Require Import letexists.

Goal program_logic_goal_for_function! tf.
Proof.
  repeat straightline.

  letexists. split; [solve[repeat straightline] |].
  split; [|solve [repeat straightline]]; repeat straightline.
  assert (word.unsigned i < word.unsigned len) by admit.

  SeparationLogic.seprewrite_in @array_address_inbounds H;
    change (word.unsigned (word.of_Z 1)) with 1 in *.
  1: instantiate (1 := word.add buf i).

  1: rewrite Z.mul_1_l.
  2: rewrite Z.mod_1_r.
  3: rewrite Z.div_1_r.
  2,3 : solve [trivial].
  
  1: unshelve erewrite (_ : forall x y, word.sub (word.add x y) x = y); [admit|].
  1: Omega.omega.

Abort.