(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib. Load LiveVerif.

#[export] Instance spec_of_u_min: fnspec :=                                     .**/

uintptr_t u_min (uintptr_t a, uintptr_t b) /**#
  requires t m := True;
  ensures t' m' retv := t' = t /\ m' = m /\
      (\[a] < \[b] /\ retv = a \/ \[b] <= \[a] /\ retv = b) #**/           /**.
Derive u_min SuchThat (fun_correct! u_min) As u_min_ok.                         .**/
{                                                                          /**. .**/
  uintptr_t r = 0;                                                         /**. .**/
  if (a < b) {                                                             /**. .**/
    r = a;                                                                 /**. .**/
  } else {                                                                 /**. .**/
    r = b;                                                                 /**. .**/
  }                                                                        /**. .**/
  return r;                                                                /**. .**/
}                                                                          /**.
Qed.

#[export] Instance spec_of_u_min3: fnspec :=                                    .**/

uintptr_t u_min3 (uintptr_t a, uintptr_t b, uintptr_t c) /**#
  requires t m := True;
  ensures t' m' retv := t' = t /\ m' = m /\
      \[retv] = Z.min \[a] (Z.min \[b] \[c]) #**/                          /**.
Derive u_min3 SuchThat (fun_correct! u_min3) As u_min3_ok.                      .**/
{                                                                          /**. .**/
  uintptr_t r = u_min(a, b);                                               /**. .**/
  uintptr_t s = u_min(r, c);                                               /**. .**/
  return s;                                                                /**. .**/
}                                                                          /**.
Qed.

#[export] Instance spec_of_u_min3_alt: fnspec :=                                 .**/

uintptr_t u_min3_alt (uintptr_t a, uintptr_t b, uintptr_t c) /**#
  requires t m := True;
  ensures t' m' retv := t' = t /\ m' = m /\
      \[retv] = Z.min \[a] (Z.min \[b] \[c]) #**/                          /**.
Derive u_min3_alt SuchThat (fun_correct! u_min3_alt) As u_min3_alt_ok.          .**/
{                                                                          /**. .**/
  if (a < b) /* split */ {                                                 /**. .**/
    if (a < c) /* split */ {                                               /**. .**/
      return a;                                                            /**. .**/
    }                                                                      /**. .**/
    else {                                                                 /**. .**/
      return c;                                                            /**. .**/
    }                                                                      /**. .**/
  }                                                                        /**. .**/
  else {                                                                   /**. .**/
    if (c < b) /* split */ {                                               /**. .**/
      return c;                                                            /**. .**/
    }                                                                      /**. .**/
    else {                                                                 /**. .**/
      return b;                                                            /**. .**/
    }                                                                      /**. .**/
  }                                                                        /**. .**/
}                                                                          /**.
Qed.

End LiveVerif. Comments .**/ //.
