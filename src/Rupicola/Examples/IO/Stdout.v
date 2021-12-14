Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.IO.Writer.

Import Writer.

Section Stdout.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Notation Writer := (Writer.M string).

  Definition write (s: string) : Writer unit :=
    {| val := tt; trace := [s] |}.

  Definition words_of_const_string (s: string) : list (word) :=
    let chars := String.list_byte_of_string s in
    List.map (fun b => word_of_byte b) chars.

  Definition literals_of_const_string (s: string) : list expr :=
    let chars := String.list_byte_of_string s in
    List.map (fun b => expr.literal (byte.unsigned b)) chars.

  Definition trace_entry_of_write (s: string) : trace_entry (mem := mem) :=
    (map.empty, "putchars", words_of_const_string s, (map.empty, [])).

  Lemma wp_literals_of_const_string:
    forall (mem : mem) (locals : locals) (s : string),
      WeakestPrecondition.dexprs
        mem locals (literals_of_const_string s) (words_of_const_string s).
  Proof.
    unfold literals_of_const_string, words_of_const_string.
    intros; induction (list_byte_of_string s); red; simpl.
    - reflexivity.
    - repeat straightline.
      eapply Proper_list_map; try apply IHl.
      eapply Proper_expr; eassumption.
      repeat (red; intros).
      subst v. congruence.
  Qed.

  Instance spec_of_putchars : spec_of "putchars" :=
    (fun functions =>
       forall args tr mem,
         True ->
         WeakestPrecondition.call
           functions "putchars" tr mem args
           (fun tr' mem' rets =>
              mem' = mem /\
              rets = [] /\
              tr' = (map.empty, "putchars", args, (map.empty, [])) :: tr)).

  Lemma compile_putchars : forall {tr mem locals functions} (s: string),
    let wr := write s in
    forall {B} {pred: B -> pure_predicate}
      {k: unit -> Writer B} {k_impl}
      var,

      spec_of_putchars functions ->

      (let tr := trace_entry_of_write s :: tr in
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       k_impl
       <{ wrspec_k trace_entry_of_write tr pred (k tt) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (* (cmd.interact [var] "stdout.write" (literals_of_const_string s)) *)
        (cmd.call [] "putchars" (literals_of_const_string s))
        k_impl
      <{ wrspec_k trace_entry_of_write tr pred (mbindn [var] wr k) }>.
  Proof.
    repeat straightline.
    eexists; (intuition eauto using wp_literals_of_const_string); [].
    straightline_call; eauto; [].
    repeat straightline; subst_lets_in_goal.
    eapply WeakestPrecondition_wrspec_k_bindn
      with (wr := {| Writer.val := tt; Writer.trace := [s] |}).
    - intros; eassumption.
  Qed.

  Definition hello_world_src (y: word) : Writer word :=
    let/n x := word.of_Z 1 in
    let/! _ := write "hello, world!" in
    let/n out := word.add x y in
    mret out.

  Instance spec_of_hello_word : spec_of "hello_world" :=
    fnspec! "hello_world" y / (R: mem -> Prop),
    { requires tr mem :=
        R mem;
      ensures tr' mem' rets :=
        wrspec trace_entry_of_write tr tr'
               (hello_world_src y) (fun val => rets = [val] /\ R mem') }.

  Hint Extern 1 => simple eapply compile_putchars; shelve : compiler.

  Derive hello_world_br2fn SuchThat
         (defn! "hello_world"("y") ~> "out"
              { hello_world_br2fn },
          implements hello_world_src using ["putchars"])
  As hello_world_br2fn_ok.
  Proof.
    compile.
  Qed.
End Stdout.

From bedrock2 Require Import BasicC64Semantics NotationsCustomEntry.
Require Import Rupicola.Lib.ToCString.
Compute hello_world_br2fn (word := word).
Compute ToCString.c_func (hello_world_br2fn (word := word)).
