Require Import Coq.Lists.List.
Require Import coqutil.Datatypes.PropSet.

Class NameGen(var st: Type) := mkNameGen {
  (* Return a state which generates vars not contained in the given list.
     We use list instead of set to guarantee that it's finite. *)
  freshNameGenState: list var -> st;

  (* Generate fresh var, and return new state *)
  genFresh: st -> (var * st);

  (* Set of all vars which will be generated in the future *)
  allFreshVars: st -> (var -> Prop);

  genFresh_spec: forall (s s': st) (x: var),
    genFresh s = (x, s') ->
    x \in allFreshVars s /\
    ~ x \in allFreshVars s' /\
    subset (allFreshVars s') (allFreshVars s);
  (* could also say
     allFreshVars s' = diff (allFreshVars s) (singleton_set x)
     but that's unnecessarily strong and requires set equality *)

  freshNameGenState_spec: forall l v, In v l -> ~ v \in (allFreshVars (freshNameGenState l));
}.
