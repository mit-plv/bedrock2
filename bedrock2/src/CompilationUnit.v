Require Import Coq.Strings.String.
Require Import Coq.ZArith.BinIntDef.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Fin.
Require Import ExtLib.Data.Map.FMapAList.
Require Import bedrock2.Macros bedrock2.Notations bedrock2.Map.
Require Import bedrock2.Syntax.
Require Import bedrock2.Semantics.

(* Compilation units should be fairly simple
 * - the basic idea is that you have "externals", "internals", and "exports"
 * - definitions can call externals and internals
 * - exports must be a subset of external and internal
 * - in the module-level semantics, one type of interaction needs to be
 *   external call.
 * - note(gmm): we don't have to support recursive linking if we want to keep
 *   the terminating semantics.
 *)

Module module.
Section with_parameters.
  Context {p : Syntax.parameters}.

  Variant data : Set :=
  | Data (_ : list Z).

  Variant definition : Type :=
  | X (_ : list data)
  | Function (_ : list varname * list varname * Syntax.cmd).


  (* note(gmm): this could be made more uniform with the rest of the development
   * if we used `map`.
   *)
  Record module : Type :=
  { imports     : list globname
  ; internal    : list globname
  ; exports     : list globname
  ; definitions : list (globname * definition)
  }.

End with_parameters.
End module.

(* the meaning of a module is a function of the meaning of the imports to the
 * meaning of the outputs.
 * note(gmm): an alternative way to represent this to treat calls to imports
 * as actions.
 *)

Require Import bedrock2.WeakestPrecondition.

Section module_semantics.
  Variable p : Semantics.parameters.
  Variable resolver : globname -> option word.

  Definition func_meaning : Type :=
    (trace -> Prop) ->
    (trace -> Prop) ->
    (trace -> trace -> Prop) ->
    trace ->
    mem ->
    list word ->
    (trace -> mem -> list word -> Prop) -> Prop.

  Variables (mod : module.module)
            (denoteImports : globname -> func_meaning).

  Definition functions : list _ :=
    (fix functions ls :=
       match ls with
       | nil => nil
       | cons (a, module.Function b) ls =>
         match resolver a with
         | Some a => cons (a,b) (functions ls)
         | None => functions ls
         end
       | cons _ ls => functions ls
       end) mod.(module.definitions).

  Definition module_definitions
             (g : globname)
  : func_meaning.
  refine (fun rely guarantee progress t mem args post =>
            exists body, List.In (g, body) mod.(module.definitions) /\
            match body with
            | module.Function body =>
              exists n,
              WeakestPrecondition.func rely guarantee progress resolver
                 (fun w t mem args post =>
                    exists g, resolver g = Some w /\
                           (List.In g mod.(module.imports) /\
                            denoteImports g rely guarantee progress t mem args post)
                         \/ call_rec rely guarantee progress resolver
                                    functions n w t mem args post)
                 body
                 t mem args post
            | _ => False
            end).
  Defined.

End module_semantics.