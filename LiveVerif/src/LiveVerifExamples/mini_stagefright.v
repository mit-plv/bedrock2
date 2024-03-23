(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Load LiveVerif.

(* src consists of length-type-value chunks:
struct TLV { uint32_t length; uint32_t typ; uint32_t data[length]; }; *)

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
     (r = /[1] /\ newData = srcData[\[srcOfs]+2:][:len newData])) #**/        /**.
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

  2: {
Abort.

End LiveVerif. Comments .**/ //.
