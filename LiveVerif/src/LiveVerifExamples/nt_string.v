(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import coqutil.Byte.
Require Import LiveVerifExamples.onesize_malloc.

Load LiveVerif.

Definition char(c: byte): word -> mem -> Prop :=
  uint 8 (byte.unsigned c).

Definition nt_str(s: list byte)(a: word): mem -> Prop :=
  sep (array char (len s + 1) (s ++ [| Byte.x00 |]) a)
      (emp (~ List.In Byte.x00 s)).

#[local] Hint Unfold nt_str : heapletwise_always_unfold.

#[export] Instance str_cmp: fnspec :=                                           .**/

uintptr_t strcmp(uintptr_t p1, uintptr_t p2) /**#
  ghost_args := (s1 s2: list byte) (R: mem -> Prop);
  requires t m := <{ * nt_str s1 p1
                     * nt_str s2 p2
                     * R }> m;
  ensures t' m' res := t' = t /\
                       List.compare byte.compare s1 s2 = Z.compare (word.signed res) 0 /\
                       <{ * nt_str s1 p1
                          * nt_str s2 p2
                          * R }> m' #**/                                   /**.
Derive strcmp SuchThat (fun_correct! strcmp) As strcmp_ok.                      .**/
{                                                                          /**. .**/
  uintptr_t c1 = 0;                                                        /**. .**/
  uintptr_t c2 = 0;                                                        /**.

  delete #(c1 = ??).
  delete #(c2 = ??).
  let h := constr:(#(len s1)) in loop invariant above h.
  unfold ready.
  lazymatch goal with
  | |- exec ?fs ?body ?t ?m ?l ?P =>
      lazymatch eval pattern s1, s2, p1, p2, R in P with
      | ?f s1 s2 p1 p2 R =>
          change (exec fs body t m l ((fun (g: list byte * list byte * word * word * (mem -> Prop)) (_: Z) =>
     (*let '(s1, s2, p1, p2, R) := g in f s1 s2 p1 p2 R) (s1, s2, p1, p2, R) (len s1)))*)
          let (g, R) := g in
          let (g, p2) := g in
          let (g, p1) := g in
          let (s1, s2) := g in
          f s1 s2 p1 p2 R) (s1, s2, p1, p2, R) (len s1)))
      end
  end.
  eapply wp_dowhile_tailrec_use_functionpost.
  { eauto with wf_of_type. }
  { (* Ltac log_packaged_context P ::= idtac P. *)
    package_heapletwise_context. }
  start_loop_body.
  steps.

unfold char in *.

  .**/


  c1 = load8(p1);                                                          /**.

(*
caller: array of char
callee: expects uint8, returns same uint8
Q: should the fact that we called a uint8 callee cast our symbolic state to uint8?
A: not really, at least here...

maybe we need "polymorphic load"?
or a load that doesn't cast/affect current state?
ie a cast-callee-state load and a don't-cast_callee-state load?
not only for loads but for any calls?


caller: P
callee pre: casted P', post Q'
caller: cast Q' back to Q or leave as Q'??, aka use callee format or keep caller format?


array of bytes
read/write uint8(Z)
-> want back array of bytes (keep caller format)

array of bytes
read as packet
-> want packet (adopt callee format)

packet
memcpy bytes of packet
-> still want packet (keep caller format)


Possible criteria:
* If part of a struct or array, cast back to original type, otherwise keep type of callee
  (that's a caller-based criterion)
* Caller's postcondition says m'=m (in which case caller context is not updated)
  or re-lists explicitly all clauses in post (in which case caller context is updated)
  Doesn't work for functions that update memory but should cast back to caller's format
  afterwards (though can this be automated?)

Interesting case:


immediate sol: use uint 8


2: {

unfold don't_know_how_to_prove.

 eapply contiguous_implies_anyval_of_fillable.
                            [ eauto with contiguous
                            | eauto with fillable] ];


                    solve [ eapply contiguous_implies_anyval_of_fillable;
                            [ eauto with contiguous
                            | eauto with fillable] ];


unfold char.

step.



reflexivity.

.**/


*)

Abort.

End LiveVerif. Comments .**/ //.
