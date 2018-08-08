Require Import bedrock2.Macros bedrock2.Map.
Require Coq.Lists.List.

Class parameters := {
  key : Type;
  value : Type;
  key_eqb : key -> key -> bool
}.

Section UnorderedList.
  Context {p : unique! parameters}.
  Instance map : map key value := {|
    map.rep := list (key * value);
    map.empty := nil;
    map.get m k := match List.find (fun p => key_eqb k (fst p)) m with
                   | Some (_, v) => Some v
                   | None => None
                   end;
    map.put m k v := (cons (k, v) (List.filter (fun p => negb (key_eqb k (fst p))) m))
  |}.
End UnorderedList.
Arguments map : clear implicits.

(* test of putmany *)
Goal False.
  assert (Map.map.putmany (0::0::nil)%list (4::7::nil)%list (@map.empty nat nat (map (Build_parameters nat nat Nat.eqb))) = Some ((0, 7) :: nil)%list) by reflexivity.
Abort.