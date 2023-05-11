(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Class malloc_constants := {
  malloc_base: Z;
  malloc_block_size: Z;
}.

Section TODO_move.
  Context {width} {BW: Bitwidth width}
    {word: word width}{word_ok: word.ok word}
    {mem: map.map word Byte.byte}{mem_ok: map.ok mem}.

  Definition anybytes(sz: Z)(p: word): mem -> Prop :=
    ex1 (fun bs => array (uint 8) sz bs p).

End TODO_move.

Load LiveVerif.

Context {consts: malloc_constants}.

Definition fixed_size_free_list(sz: Z): nat -> word -> mem -> Prop :=
  fix rec n p :=
    match n with
    | O => emp (p = /[0])
    | S n' => ex1 (fun q => <{ * uintptr q p
                               * anybytes sz (p ^+ /[4])
                               * rec n' q }>)
    end.

Definition allocator: mem -> Prop. Admitted.
Definition freeable(sz: Z)(a: word): mem -> Prop. Admitted.

Lemma purify_allocator: purify allocator True.
Proof. unfold purify. intros. constructor. Qed.
Hint Resolve purify_allocator : purify.

Lemma purify_freeable: forall sz a, purify (freeable sz a) True.
Proof. unfold purify. intros. constructor. Qed.
Hint Resolve purify_freeable : purify.

#[export] Instance spec_of_malloc: fnspec :=                                    .**/

uintptr_t malloc (uintptr_t n) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * allocator
                     * R }> m;
  ensures t' m' p := t' = t /\
     (p = /[0] /\
      <{ * allocator
         * R }> m') \/
     (p <> /[0] /\
      <{ * allocator
         * anybytes \[n] p
         * freeable \[n] p
         * R }> m') #**/                                                   /**.
Derive malloc SuchThat (fun_correct! malloc) As malloc_ok.                      .**/
{                                                                          /**. .**/
  uintptr_t x = malloc_base + n;                                           /**. .**/
  x = 0;                                                                   /**. .**/
  return x;                                                                /**. .**/
}                                                                          /*?.
eexists. step. step. step. step. step. step. step. step. left.
steps.
Qed.

#[export] Instance spec_of_free: fnspec :=                                      .**/

void free (uintptr_t p) /**#
  ghost_args := n (R: mem -> Prop);
  requires t m := <{ * allocator
                     * anybytes \[n] p
                     * freeable \[n] p
                     * R }> m;
  ensures t' m' := t' = t /\
                   <{ * allocator
                      * R }> m' #**/                                       /**.
Derive free SuchThat (fun_correct! free) As free_ok. Abort.

End LiveVerif. Comments .**/ //.
