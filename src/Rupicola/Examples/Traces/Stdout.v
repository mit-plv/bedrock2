Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.Traces.Trace.

Import TrMonad.

Section Stdout.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok _}.

  Definition write (s: string) : Eventful string unit :=
    {| val := tt; trace := [s] |}.

  Notation Writeful A := (Eventful string A).

  Notation trace_entry := ((fun (A: Type) (_: list A) => A) _ ([]: Semantics.trace)).

  Definition words_of_const_string (s: string) : list (Semantics.word) :=
    let chars := String.list_byte_of_string s in
    List.map (fun b => word_of_byte b) chars.

  Definition literals_of_const_string (s: string) : list expr :=
    let chars := String.list_byte_of_string s in
    List.map (fun b => expr.literal (byte.unsigned b)) chars.

  Definition trace_entry_of_write (s: string) : trace_entry := (* FIXME *)
    (map.empty, "putchars", words_of_const_string s, (map.empty, [])).


  Lemma wp_literals_of_const_string:
    forall (mem : Semantics.mem) (locals : Semantics.locals) (s : string),
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
              rets = [word.of_Z 0] /\
              tr' = (map.empty, "putchars", args, (map.empty, [])) :: tr)).

  Lemma compile_putchars {tr mem locals functions} (s: string) :
    let evf := write s in
    forall {B} {pred: Writeful B -> predicate}
      {k: unit -> Writeful B} {k_impl}
      tr0 var,

      spec_of_putchars functions ->

      (<{ Trace := (trace_entry_of_write s) :: tr;
          Memory := mem;
          Locals := map.put locals var (word.of_Z 0);
          Functions := functions }>
       k_impl
       <{ tbind (s :: tr0) pred (k tt) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (* (cmd.interact [var] "stdout.write" (literals_of_const_string s)) *)
        (cmd.call [var] "putchars" (literals_of_const_string s))
        k_impl
      <{ tbind tr0 pred (bindn [var] evf k) }>.
  Proof.
    repeat straightline.
    eexists; (intuition eauto using wp_literals_of_const_string); [].
    straightline_call; eauto; [].
    repeat straightline; subst_lets_in_goal.
    rewrite tbind_bindn; eassumption.
  Qed.

  Definition hello_world_src (y: Semantics.word) : Eventful string Semantics.word :=
    let/n x := word.of_Z 1 in
    let/! _ := write "hello, world!" in
    let/n out := word.add x y in
    ret out.

  Instance spec_of_hello_word : spec_of "hello_world" :=
    fnspec! "hello_world" y / (R: Semantics.mem -> Prop),
    { requires fns tr mem :=
        spec_of_putchars fns /\ R mem;
      ensures tr' mem' rets :=
        tracebind trace_entry_of_write
                  (hello_world_src y)
                  (fun val tr0 => tr' = tr0 ++ tr /\ (R mem' /\ rets = [val])) }.

  Hint Extern 1 => simple eapply compile_putchars; shelve : compiler.

  Derive hello_world_body SuchThat
         (defn! "hello_world"("y") ~> "out"
              { hello_world_body },
          implements hello_world_src)
  As hello_world_target_correct.
  Proof.
    compile.
  Qed.
End Stdout.

Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.NotationsInConstr.
Arguments hello_world_body /.
Eval cbv in hello_world_body.

Require Import bedrock2.ToCString.
Compute c_func ("hello_world", (["y"], ["out"], hello_world_body)).
