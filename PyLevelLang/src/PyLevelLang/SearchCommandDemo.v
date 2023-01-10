(* The `Search` command can be helpful to discover useful definitions and lemmas.
   For instance, suppose you want to ensure that the keys of a record are all
   unique, but you don't know if there's already a function to do that.
   You suspect that its name could contain something like "duplicate" or "dup",
   because it's about absence of duplicates. Moreover, it should take a list.
   So you can run the following Search command: *)

Search list "dup".

(* (Note that list is not in quotes, because we mean 'the type list', whereas
   "dup" is in quotes, because we mean 'any name containing "dup" as a substring').
   The above command is supposed to return all definitions and lemmas whose
   type mentions list and whose name contains "dup".
   Unfortunately, it doesn't return any results, because Search only looks
   at the files that have been `Require`d (as well as all transitively
   `Require`d files).
   So let's import some random bedrock2 file that has a lot of dependencies: *)

Require Import bedrock2.ProgramLogic.

Search list "dup".

(* Now it lists (among others) two interesting definitions:

List.dedup: forall {A : Type}, (A -> A -> bool) -> list A -> list A
List.nodup: forall [A : Type], (forall x y : A, {x = y} + {x <> y}) -> list A -> list A

They both take a list and return it with its duplicates removed.

As the following commands show, List.nodup is in Coq's standard library, and List.dedup
is in our own coqutil library.
*)
Locate List.nodup. Locate List.dedup.

(* Both take an element comparison function, but for List.dedup, the element comparison
   function has to return a bool, whereas in List.nodup, it has to return a sumbool.
   Since sumbools contain proofs that can cause problems when evaluated within Coq
   (using eg cbv), we implemented our own List.dedup that takes a bool-returning
   element comparison function.

   A list of record field names contains no duplicates if List.dedup of that list
   returns the same list. So we need to compare two lists, so let's search for
   a list comparison function.
   We can use a pattern to search for it by its type: *)

Search (list ?A -> list ?A -> bool).

(* And it returns just the function we want:

List.list_eqb: forall {A : Type}, (A -> A -> bool) -> list A -> list A -> bool

In summary: The command

Search cond_1 ... cond_N.

lists all definitions/lemmas whose types mention all conditions cond_1 ... cond_N.
A condition can be a reference to a definition that has to appear in the type,
a pattern that has to appear in the type, or a quoted string that has to appear in the name.

In fact, the Search command has even more options, which are described here:
https://coq.inria.fr/refman/proof-engine/vernacular-commands.html#coq:cmd.Search
But to get started, the few explained above should be sufficient. *)
