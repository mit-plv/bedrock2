(*
SYNOPSIS
       #include <string.h>

       void *memmove(void *dest, const void *src, size_t n);

DESCRIPTION
       The  memmove()  function copies n bytes from memory
       area src to memory area dest.  The memory areas may
       overlap: copying takes place as though the bytes in
       src are first copied into a  temporary  array  that
       does  not  overlap  src  or dest, and the bytes are
       then copied from the temporary array to dest.
*)

(* In current bedrock2, a spec for this function might look like this: *)
Instance spec_of_memmove : spec_of "memmove" := fun functions =>
  forall dst src n ds Rd ss Rs t m,
    (bytes ds dst * Rd) m /\ (bytes ss src * Rs) m /\ 
    Z.of_nat (length ss) = word.unsigned n /\
    Z.of_nat (length ss) = word.unsigned n /\
    word.unsigned n <= 2^(width-1)
    -> WeakestPrecondition.call functions "memmove" t m [dst; src; n]
      (fun t' m' rets => t=t' /\ (bytes ss dst * Rd) m' /\ rets = [dst]).

(* Aspects of the abstract syntax above that I like:
   - arguments bound before ghost arguments
   - ghost arguments bound before semantics arguments (t, m)
   - preconditions are joined with /\ instead of ->
   - preconditions ordered to drive unification of ghost arguments
   - the length precondition is not baked into the byte arrays
     (although maybe the opposite can make sense for some types, idk)
   - t,m and arguments are all available for writing the precondition
   - t',m' and rets are all available for writing the postcondition
   - the return value is not needlessly existentially quantified
  As for concrete syntax... it seems that you all think we should do
  better. So here go some suggestions, from "probably we can do it" to
  pipe dreams. I know there are other forms out there, by me and by
  others, and if there is anything in particular about them that you
  like, please point it out (even if it is just a concrete syntax /
  keyword difference). One preference I have there is not to turn valid
  identifiers into keywords, but other than that I think I don't care
  what the concrete syntax is as long as the abstract syntax is
  satisfying.
*)

(* (1) Coercions and notations, I am already using something like this *)
Infix "$@" := bytes.
Instance spec_of_memmove : spec_of "memmove" := fun functions =>
  forall dst src n ds Rd ss Rs t m,
    (ds$@dst * Rd) m /\ (ss$@src * Rs) m /\
    length ss = n :> Z /\ length ss = n :> Z /\ n <= 2^(width-1)
    -> WeakestPrecondition.call functions "memmove" t m [dst; src; n]
      (fun t' m' rets => t=t' /\ (bytes ss dst * Rd) m' /\ rets = [dst]).

(* (2) maybe shorten some names? *)
Instance spec_of_memmove : spec_of "memmove" := fun _fs =>
  forall dst src n ds Rd ss Rs t m,
    (ds$@dst * Rd) m /\ (ss$@src * Rs) m /\
    length ss = n :> Z /\ length ss = n :> Z /\ n <= 2^(width-1)
    -> WP.call _fs "memmove" t m [dst; src; n]
      (fun t' m' rets => t=t' /\ (ss$@dst * Rd) m' /\ rets = [dst]).

(* (3) the initial lambda is boilerplate, let's hide it by making a recursive notation for all the binders *)
Instance spec_of_memmove : spec_of "memmove" :=
  wpcall! forall dst src n ds Rd ss Rs t m,
    (ds$@dst * Rd) m /\ (ss$@src * Rs) m /\
    length ss = n :> Z /\ length ss = n :> Z /\ n <= 2^(width-1)
    for "memmove" t m [dst; src; n]
    return fun t' m' rets => t=t' /\ (ss$@dst * Rd) m' /\ rets = [dst].

(* (4) more concise concrete syntax that does not duplicate arguments,
* requires recursive binders and applications in a notation (which I am not sure how to do) *)
Instance spec_of_memmove : spec_of "memmove" :=
  wpcall! "memmove" dst src n, forall ds Rd ss Rs where t m,
  (ds$@dst * Rd) m /\ (ss$@src * Rs) m /\
  length ss = n :> Z /\ length ss = n :> Z /\ n <= 2^(width-1)
  return fun t' m' rets => t=t' /\ (ss$@dst * Rd) m' /\ rets = [dst].

(* (5) we could deduplicate the string by ltac if the type is given *)
Instance spec_of_memmove : spec_of "memmove" :=
  wpcall! dst src n, forall ds Rd ss Rs where t m,
  (ds$@dst * Rd) m /\ (ss$@src * Rs) m /\
  length ss = n :> Z /\ length ss = n :> Z /\ n <= 2^(width-1)
  return fun t' m' rets => t=t' /\ (ss$@dst * Rd) m' /\ rets = [dst].

(* (6) if we are willing to bake in existential quantifiers for each return value *)
Instance spec_of_memmove : spec_of "memmove" :=
  wpcall! dst src n, forall ds Rd ss Rs where t m,
  (ds$@dst * Rd) m /\ (ss$@src * Rs) m /\
  length ss = n :> Z /\ length ss = n :> Z /\ n <= 2^(width-1)
  return r then fun t' m' => r = dst /\ t=t' /\ (ss$@dst * Rd) m'.

(* (7) I don't think there is a way to capitalize binders before parsing the last clause *)
Instance spec_of_memmove : spec_of "memmove" :=
  wpcall! dst src n, forall ds Rd ss Rs where t m,
  (ds$@dst * Rd) m /\ (ss$@src * Rs) m /\
  length ss = n :> Z /\ length ss = n :> Z /\ n <= 2^(width-1)
  return r then r = dst /\ t=T /\ (ss$@dst * Rd) M.
