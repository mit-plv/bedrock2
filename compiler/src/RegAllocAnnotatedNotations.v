Require Import bedrock2.Syntax.
Require Import compiler.RegAlloc.

Export bopname.

Notation "a ; b" := (ASSeq _ _ _ a b) (only printing, right associativity,
      at level 50, format "a ; '//' b") : regalloc_scope.
Notation "'$x' a '($r' b ')' = c" := (ASLit _ _ _ a b c) (only printing,
      at level 40, format "'$x' a '($r' b ')'  =  c") : regalloc_scope.
Notation "'$x' a '($r' b ')' = '$x' c" := (ASSet _ _ _ a b c) (only printing,
      at level 40, format "'$x' a '($r' b ')'  =  '$x' c") : regalloc_scope.
Notation "'$x' a '($r' b ')' = op '$x' c '$x' d" := (ASOp _ _ _ a b op c d) (only printing,
      at level 40, format "'$x' a '($r' b ')'  =  op  '$x' c  '$x' d") : regalloc_scope.
Notation "'loop' a 'breakUnless' '$x' cond b" := (ASLoop _ _ _ a cond b)
      (only printing, at level 50, a at level 40,
       format "'loop' '[v ' '//' a '//' 'breakUnless'  '$x' cond '//' b ']'") : regalloc_scope.
Notation "'skip'" := (ASSkip _ _ _) (only printing) : regalloc_scope.


(* TODO
       ASLoad(x: srcvar)(x': impvar)(a: srcvar)
       ASStore(a: srcvar)(v: srcvar)
       ASIf(cond: srcvar)(bThen bElse: astmt)
       ASSkip
       ASCall(binds: list (srcvar * impvar))(f: func)(args: list srcvar). *)
