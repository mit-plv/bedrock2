(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import LiveVerifExamples.memcpy.

Load LiveVerif.

(* TODO this (or something similar) should be in the library *)
Ltac step_hook ::=
  lazymatch goal with
  | |- ?A \/ ?B =>
      tryif (assert_succeeds (assert (~ A) by (zify_goal; xlia zchecker)))
      then right else
      tryif (assert_succeeds (assert (~ B) by (zify_goal; xlia zchecker)))
      then left else fail
  end.

#[export] Instance spec_of_safeCopySlice: fnspec :=                                .**/

uintptr_t safeCopySlice(
  uintptr_t src, uintptr_t srcOfs, uintptr_t srcLen,
  uintptr_t unsafeN,
  uintptr_t dst, uintptr_t dstOfs, uintptr_t dstLen
) /**#
  ghost_args := srcData dstData dstUninit (R: mem -> Prop);
  requires t m :=
    <{ * array (uint 8) \[srcLen] srcData src
       * array (uint 8) \[dstLen] (dstData ++ dstUninit) dst
       * R }> m /\
    \[srcOfs] <= \[srcLen] /\
    len dstData = \[dstOfs];
  ensures t' m' r := t' = t /\
   ((r = /[0] /\
     <{ * array (uint 8) \[srcLen] srcData src
        * array (uint 8) \[dstLen] (dstData ++ dstUninit) dst
        * R }> m') \/
    (r = /[1] /\
     <{ * array (uint 8) \[srcLen] srcData src
        * array (uint 8) \[dstLen] (dstData ++
                                    srcData[\[srcOfs]:][:\[unsafeN]] ++
                                    dstUninit[\[unsafeN]:]) dst
        * R }> m')) #**/                                                      /**.
Derive safeCopySlice SuchThat (fun_correct! safeCopySlice) As safeCopySlice_ok.    .**/
{                                                                             /**. .**/
  if (srcOfs + unsafeN <= srcLen && dstOfs + unsafeN <= dstLen) /*split*/ {   /**. .**/
    Memcpy(dstOfs, srcOfs, unsafeN);                                          /**.

assert (subrange dstOfs (\[unsafeN] * 1) dst (\[dstLen] * 1)). {
  unfold subrange. clear Error.
  bottom_up_simpl_in_goal.
  (* Wait, `dstOfs ^- dst` makes no sense, because that subtracts an address from
     an offset and could underflow, something must be wrong here, ahaa it should
     be dst+dstOfs and src+srcOfs!
     This bug is really stupid, but the author actually inadvertently wrote this bug
     while developing this program with the deliberately inserted bug that follows next. *)
Abort.

Derive safeCopySlice SuchThat (fun_correct! safeCopySlice) As safeCopySlice_ok.    .**/
{                                                                             /**. .**/
  if (srcOfs + unsafeN <= srcLen && dstOfs + unsafeN <= dstLen) /*split*/ {   /**. .**/
    Memcpy(dst + dstOfs, src + srcOfs, unsafeN);                              /**.

assert (subrange (dst ^+ dstOfs) (\[unsafeN] * 1) dst (\[dstLen] * 1)). {
  unfold subrange. clear Error.
  bottom_up_simpl_in_goal.
(* need to show:         \[dstOfs] + \[unsafeN] <= \[dstLen]
   but we only have H1 : \[dstOfs ^+ unsafeN] <= \[dstLen]
   So why did the system not simplify H1 into \[dstOfs ^+ unsafeN]? *)
(* Search \[_ ^+ _]. *)
(* Lists the two hypotheses containing this pattern, followed by word.unsigned_add,
   which shows that \[x ^+ y] = word.wrap (\[x] + \[y]), and word.unsigned_add_nowrap,
   which shows that if \[x] + \[y] < 2 ^ width, then \[x ^+ y] = \[x] + \[y].
   So I need to show \[dstOfs] + \[unsafeN] < 2 ^ width, but wait, that might not hold,
   --> serious bug found!! *)
Abort.

Derive safeCopySlice SuchThat (fun_correct! safeCopySlice) As safeCopySlice_ok.    .**/
{                                                                             /**. .**/
  if (unsafeN <= srcLen - srcOfs && unsafeN <= dstLen - dstOfs) /*split*/ {   /**. .**/
    Memcpy(dst + dstOfs, src + srcOfs, unsafeN);                              /**. .**/
    return 1;                                                                 /**. .**/
  }                                                                           /**. .**/
  else {                                                                      /**. .**/
    return 0;                                                                 /**. .**/
  }                                                                           /**. .**/
}                                                                             /**.
Qed.

#[export] Instance spec_of_parse_chunk_of_type_or_skip: fnspec :=                .**/

uintptr_t parse_chunk_of_type_or_skip(
  uintptr_t src, uintptr_t pSrcOfs, uintptr_t srcLen,
  uintptr_t expected_typ,
  uintptr_t dst, uintptr_t pDstOfs, uintptr_t dstLen
) /**#
  ghost_args := srcOfs dstOfs srcData dstData dstUninit (R: mem -> Prop);
  requires t m :=
    <{ * uintptr srcOfs pSrcOfs
       * uintptr dstOfs pDstOfs
       * array (uint 32) \[srcLen] srcData src
       * array (uint 32) \[dstLen] (dstData ++ dstUninit) dst
       * R }> m /\
    \[srcOfs] + 2 <= \[srcLen] /\
    len dstData = \[dstOfs];
  ensures t' m' r := t' = t /\ exists newSrcOfs newDstOfs newData,
    <{ * uintptr newSrcOfs pSrcOfs
       * uintptr newDstOfs pDstOfs
       * array (uint 32) \[srcLen] srcData src
       * array (uint 32) \[dstLen] (dstData ++ newData ++ dstUninit[len newData :]) dst
       * R }> m' /\
    \[newSrcOfs] = \[srcOfs] + len newData /\
    \[newDstOfs] = \[dstOfs] + len newData /\
    ((r = /[0] /\ newData = nil) \/
     (r = /[1] /\ newData = srcData[\[srcOfs]+2:][:len newData])) #**/     /**.
Derive parse_chunk_of_type_or_skip SuchThat (fun_correct! parse_chunk_of_type_or_skip)
  As parse_chunk_of_type_or_skip_ok.                                            .**/
{                                                                          /**. .**/
  uintptr_t srcOfs = deref(pSrcOfs);                                       /**. .**/
  uintptr_t dstOfs = deref(pDstOfs);                                       /**. .**/
  uintptr_t actual_typ = deref32(src + srcOfs * 4 + 4);                    /**. .**/
  if (actual_typ == expected_typ) /* split */ {                            /**. .**/
    uintptr_t n = deref32(src + srcOfs * 4);                               /**. .**/
    if (srcOfs + n <= srcLen && dstOfs + n <= dstLen) /* split */ {        /**. .**/

(* use bytes and more-parsed src? *)
(* memcpy or uint32arrayCpy? *)

    }                                                                      /**.

Abort.


(* TODO would be more interesting with byte arrays: *)

#[export] Instance spec_of_parse_chunk_of_type_bytearr: fnspec :=                .**/

uintptr_t parse_chunk_of_type_bytearr(
  uintptr_t src, uintptr_t pSrcOfs, uintptr_t srcLen,
  uintptr_t expected_typ,
  uintptr_t dst, uintptr_t pDstOfs, uintptr_t dstLen
) /**#
  ghost_args := srcOfs dstOfs srcData dstData dstUninit (R: mem -> Prop);
  requires t m :=
    <{ * uintptr srcOfs pSrcOfs
       * uintptr dstOfs pDstOfs
       * array (uint 8) \[srcLen] srcData src
       * array (uint 8) \[dstLen] (dstData ++ dstUninit) dst
       * R }> m /\
    \[srcOfs] + 8 <= \[srcLen] /\
    len dstData = \[dstOfs];
  ensures t' m' r := t' = t /\ exists newSrcOfs newDstOfs newData,
    <{ * uintptr newSrcOfs pSrcOfs
       * uintptr newDstOfs pDstOfs
       * array (uint 8) \[srcLen] srcData src
       * array (uint 8) \[dstLen] (dstData ++ newData ++ dstUninit[len newData :]) dst
       * R }> m' /\
    \[newSrcOfs] = \[srcOfs] + len newData /\
    \[newDstOfs] = \[dstOfs] + len newData /\
    ((r = /[0] /\ newData = nil) \/
     (r = /[1] /\ newData = srcData[\[srcOfs]+8:][:len newData])) #**/        /**.
Derive parse_chunk_of_type_bytearr SuchThat (fun_correct! parse_chunk_of_type_bytearr)
  As parse_chunk_of_type_bytearr_ok.                                            .**/
{                                                                          /**. .**/
  uintptr_t srcOfs = load(pSrcOfs);                                        /**. .**/
  uintptr_t dstOfs = load(pDstOfs);                                        /**. .**/
  uintptr_t actual_typ = load32(src + srcOfs + 4);                         /**.

Abort.

End LiveVerif. Comments .**/ //.
