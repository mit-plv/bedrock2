Require Import bedrock2.Syntax.
Require Import compiler.RegAlloc.

Export bopname.

Notation "a ; b" := (ASSeq a b) (only printing, right associativity,
      at level 50, format "a ; '//' b") : regalloc_scope.
Notation "a '($r' b ')' = c" := (ASLit a b c) (only printing,
      at level 40, format "a '($r' b ')'  =  c") : regalloc_scope.
Notation "a '($r' b ')' = c" := (ASSet a b c) (only printing,
      at level 40, format "a '($r' b ')'  =  c") : regalloc_scope.
Notation "a '($r' b ')' = op c d" := (ASOp a b op c d) (only printing,
      at level 40, format "a '($r' b ')'  =  op  c  d") : regalloc_scope.
Notation "'loop' a 'breakUnless' cond b" := (ASLoop a cond b)
      (only printing, at level 50, a at level 40,
       format "'loop' '[v ' '//' a '//' 'breakUnless'  cond '//' b ']'") : regalloc_scope.
Notation "'skip'" := ASSkip (only printing) : regalloc_scope.


(* TODO
       ASLoad(x: srcvar)(x': impvar)(a: srcvar)
       ASStore(a: srcvar)(v: srcvar)
       ASIf(cond: srcvar)(bThen bElse: astmt)
       ASSkip
       ASCall(binds: list (srcvar * impvar))(f: func)(args: list srcvar). *)
