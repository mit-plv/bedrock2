(* -*- eval: (load-file "../../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

(* Usually, we keep all adjacent memory in the same sep clause, so when canceling,
   we only need to check if a clause in the hyps is a superrange of the clause
   in the conclusion to be cancelled.
   But in tailrec while lemmas, we get a
   "post-with-small-ghostvars implies post-with-bigger-ghostvars" goal
   and the post-with-small-ghostvars typically has a bigger frame (containing some
   deliberately forgotten memory), which might be adjacent to some non-framed
   memory, but did not get merged together, so during the cancellation to prove
   post-with-bigger-ghostvars, we would need to merge in the hyps, or to split
   in the conclusion, and we chose to split in the conclusion (because currently,
   we never do a search for anything mergeable in the hyps, we only merge back
   stuff that was split before a function call). *)

Load LiveVerif.

(*



Example: We're trying to cancel in order 1-2-3, upper line is hyps,
lower line is conclusion.
Note that conclusion clause #1 is not a subrange of any hyp clause,
and no hyp clause is a subrange of a conclusion clause.
But there is a hyp clause whose beginning points into the middle of
conclusion clause 1, so we split the conclusion there, and then continue
as usual by splitting hyps that are a superrange of a conclusion clause.

|--------|-------------|
|--3--|----1--|---2----|

|--------|-------------|
|--3--|1a|-1b-|---2----|

|-----|xx|-------------|
|--3--|xx|-1b-|---2----|


Alternative (would require flexible cancellation order):

|--------|-------------|
|--3--|----1--|---2----|

delay cancellation of 1

|--------|----|xxxxxxxx|
|--3--|----1--|xxxxxxxx|

|xxxxx|--|----|xxxxxxxx|
|xxxxx|----1--|xxxxxxxx|

now we have a hyp clause that's a subrange of the conclusion clause, so split:

|xxxxx|--|----|xxxxxxxx|
|xxxxx|1a|-1b-|xxxxxxxx|


Every boundary at which we might need to split the conclusion is both the beginning
and the end of a range appearing in the hyps, so it's sufficient to only consider
range beginnings in the hyps. *)

#[export] Instance spec_of_test0: fnspec :=                                      .**/

void test0(uintptr_t p1, uintptr_t p2, uintptr_t n1, uintptr_t n2, uintptr_t p3) /**#
  ghost_args := (R: mem -> Prop) (vs1 vs2: list Z);
  requires t m := <{ * array (uint 32) \[n1] vs1 p1
                     * array (uint 32) \[n2] vs2 p2
                     * R }> m;
  ensures t' m' := exists vs, t' = t /\
            <{ * array (uint 32) (\[n1] + \[n2]) vs p3
               * R }> m' #**/                                              /**.
Derive test0 SuchThat (fun_correct! test0) As test0_ok.                         .**/
{                                                                          /**. .**/
}                                                                          /**.
  test_error Error:("Exactly one of the following claims should hold:"
          [| subrange p3 ((\[n1] + \[n2]) * 4) p1 (\[n1] * 4);
             inrange p1 p3 ((\[n1] + \[n2]) * 4);
             subrange p3 ((\[n1] + \[n2]) * 4) p2 (\[n2] * 4);
             inrange p2 p3 ((\[n1] + \[n2]) * 4)|]).
Abort.

#[export] Instance spec_of_test: fnspec :=                                      .**/

void test(uintptr_t p1, uintptr_t p2, uintptr_t n1, uintptr_t n2) /**#
  ghost_args := (R: mem -> Prop) (vs1 vs2: list Z);
  requires t m := p1 ^+ /[4] ^* n1 = p2 /\ 4 * \[n1] < 2 ^ 32 /\
                  <{ * array (uint 32) \[n1] vs1 p1
                     * array (uint 32) \[n2] vs2 p2
                     * R }> m;
  ensures t' m' := exists vs, t' = t /\
            <{ * array (uint 32) (\[n1] + \[n2]) vs p1
               * R }> m' #**/                                              /**.
Derive test SuchThat (fun_correct! test) As test_ok.                            .**/
{                                                                          /**. .**/
}                                                                          /**.
  lazymatch goal with
  | |- split_concl_at ?s ?g =>
      change g;
      lazymatch g with
      | canceling (cons ?P ?Ps) ?om ?Rest =>
          lazymatch P with
          | array ?elem ?size ?vs ?start =>
              eapply cancel_rew_head;
              [ eapply (split_array_at_bw _ s);
                [ reflexivity | word_lia_hook_for_split_merge ]
              | ]
          end
      end
  end.

  step. step. step. step. step. step. step. step.

  step. step. step. step.
  (* TODO in the goal

  impl1 (array (uint 32) \[n2] vs2 p2)
        (array (uint 32) (\[n1] + \[n2] - \[p2 ^- p1] / 4) ?vs2 p2)

   careful_reflexivity_step does not dare to instantiate ?vs2.
   On the other hand, in HeapletwiseHyps, hyp_clause_matches_goal_clause does,
   and that's why this problem hasn't appeared up to now. *)
  {
    replace (\[n1] + \[n2] - \[p2 ^- p1] / 4) with \[n2].
    1: reflexivity.
    word_lia_hook_for_split_merge.
  }
Abort.

End LiveVerif. Comments .**/ //.
