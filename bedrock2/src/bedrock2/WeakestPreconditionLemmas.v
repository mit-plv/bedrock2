Require bedrock2.WeakestPrecondition.
Import Syntax Semantics Map.Interface Word.Interface.

Require bedrock2.WeakestPreconditionProperties.

Section WithParameters.
  Context {p:Semantics.parameters}.
  Implicit Type (post : trace -> mem -> locals -> Prop).
  Lemma set_without_dexpr call x e t m l post
    ( H : WeakestPrecondition.expr m l e (fun v => 
      dlet.dlet (map.put l x v) (fun l : locals => post t m l)))
    : WeakestPrecondition.cmd(p:=p) call (cmd.set x e) t m l post.
  Proof.
  Admitted.
End WithParameters.
