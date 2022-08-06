Require bedrock2.BasicC64Semantics bedrock2.NotationsCustomEntry.
Import BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Require Import coqutil.Macros.ident_to_string.

Section chacha20.
  Import bedrock2.Syntax Syntax.Coercions NotationsCustomEntry.

  Local Notation "x <<<= n" := (cmd.set (ident_to_string! x) (expr.op bopname.slu (ident_to_string! x) n)) (in custom bedrock_cmd at level 0, x ident, n bigint).
  Local Notation "x ^= e" := (cmd.set (ident_to_string! x) (expr.op bopname.xor (ident_to_string! x) e)) (in custom bedrock_cmd at level 0, x ident, e custom bedrock_expr).
  Local Notation "x += e" := (cmd.set (ident_to_string! x) (expr.op bopname.add (ident_to_string! x) e)) (in custom bedrock_cmd at level 0, x ident, e custom bedrock_expr).

  Definition chacha20_quarter : func :=
    ("chacha20_quarter", (["a";"b";"c";"d"], ["a";"b";"c";"d"], bedrock_func_body:(
      a += b; d ^= a; d <<<= 16;
      c += d; b ^= c; b <<<= 12;
      a += b; d ^= a; d <<<= 8;
      c += d; b ^= c; b <<<= 7
    ))).

  Definition QUARTERROUND (a b c d : String.string) : cmd
    := ltac:(let body := (eval cbv [chacha20_quarter] in (let '(_, (_, _, body)) := chacha20_quarter in body)) in
             lazymatch (eval pattern "a", "b", "c", "d" in body) with
             | ?x "a" "b" "c" "d"
               => let y := (eval cbv beta in (x a b c d)) in
                  exact y
             end).

  Local Notation "'xorout' o x" := (
      let addr := bedrock_expr:(out+coq:(expr.literal(4*o))) in
      bedrock_cmd:(store4($addr, load4($addr)^$(expr.var (ident_to_string! x)))))
      (in custom bedrock_cmd at level 0, o bigint, x ident).

  Definition chacha20_block_separate : func :=
    (* NOTE: I (andreser) don't understand why xorout needs these *)
    let x0  := "x0" in let x1  := "x1" in let x2  := "x2" in let x3  := "x3" in
    let x4  := "x4" in let x5  := "x5" in let x6  := "x6" in let x7  := "x7" in
    let x8  := "x8" in let x9  := "x9" in let x10 := "x10" in let x11 := "x11" in
    let x12 := "x12" in let x13 := "x13" in let x14 := "x14" in let x15 := "x15" in
    ("chacha20_block", (["out"; "key"; "nonce"; "countervalue"], [], bedrock_func_body:(
      x0 = $0x61707865;   x1 = $0x3320646e;   x2 = $0x79622d32;    x3 = $0x6b206574;
      x4 = load4(key);           x5 = load4(key+$4);   x6 = load4(key+$8);    x7 = load4(key+$12);
      x8 = load4(key+$16);  x9 = load4(key+$20); x10 = load4(key+$24);  x11 = load4(key+$28);
      x12 = countervalue;       x13 = load4(nonce);        x14 = load4(nonce+$4); x15 = load4(nonce+$8);
      i = $0; while (i < $10) { i += $1;
        (x0, x4,  x8, x12) = chacha20_quarter( x0, x4, x8,  x12);
        (x1, x5,  x9, x13) = chacha20_quarter( x1, x5, x9,  x13);
        (x2, x6, x10, x14) = chacha20_quarter( x2, x6, x10, x14);
        (x3, x7, x11, x15) = chacha20_quarter( x3, x7, x11, x15);
        (x0, x5, x10, x15) = chacha20_quarter( x0, x5, x10, x15);
        (x1, x6, x11, x12) = chacha20_quarter( x1, x6, x11, x12);
        (x2, x7,  x8, x13) = chacha20_quarter( x2, x7, x8,  x13);
        (x3, x4,  x9, x14) = chacha20_quarter( x3, x4, x9,  x14)
      };
      x0 += $0x61707865;  x1 += $0x3320646e;   x2 += $0x79622d32;    x3 += $0x6b206574;
      x4 += load4(key);          x5 += load4(key+$4);   x6 += load4(key+$8);    x7 += load4(key+$12);
      x8 += load4(key+$16); x9 += load4(key+$20); x10 += load4(key+$24);  x11 += load4(key+$28);
      x12 += countervalue;      x13 += load4(nonce);        x14 += load4(nonce+$4); x15 += load4(nonce+$8);
      xorout  0  x0;   xorout 1 x1; xorout 2   x2;  xorout 3  x3;
      xorout  4  x4;   xorout 5 x5; xorout 6   x6;  xorout 7  x7;
      xorout  8  x8;   xorout 9 x9; xorout 10 x10; xorout 11 x11;
      xorout 12 x12; xorout 13 x13; xorout 14 x14; xorout 15 x15
  ))).

  Local Ltac repquarterround body :=
    lazymatch body with
    | context body[cmd.call [?x1; ?x2; ?x3; ?x4] "chacha20_quarter" [expr.var ?x1; expr.var ?x2; expr.var ?x3; expr.var ?x4] ]
      => let body := context body[QUARTERROUND x1 x2 x3 x4] in
         repquarterround body
    | context body[cmd.call ?ls "chacha20_quarter" ?ls' ]
      => let v := constr:(cmd.call ls "chacha20_quarter" ls') in
         fail 0 "could not replace ""chacha20_quarter"" in" v
    | context["chacha20_quarter"]
      => fail 0 "could not replace ""chacha20_quarter"" in" body
    | _ => body
    end.
  Definition chacha20_block : func :=
    ltac:(let body := (eval cbv delta [chacha20_block_separate] in chacha20_block_separate) in
          let body := repquarterround body in
          exact body).
End chacha20.

(*
Require bedrock2.ToCString.
Example chacha20_block_c_string := Eval vm_compute in
  ToCString.c_module [chacha20_quarter; chacha20_block_separate].
Print chacha20_block_c_string.
*)

From Coq Require Import String.
From Coq Require Import ZArith.ZArith.
From coqutil Require Import Word.Interface Word.Properties Map.Interface.
From coqutil.Word Require Import Naive.
From coqutil.Tactics Require Import letexists eabstract.
From bedrock2 Require Import FE310CSemantics Semantics WeakestPrecondition ProgramLogic Array Scalars Loops.
From bedrock2.Map Require Import Separation SeparationLogic.
From coqutil.Z Require Import Lia.

Local Infix "*" := sep.
Local Infix "*" := sep : type_scope.

Local Existing Instance coqutil.Word.Naive.word.

Instance spec_of_chacha20 : spec_of "chacha20_block" := fun functions =>
  forall outAddr out keyAddr key nonceAddr nonce cval R m t,
    (array scalar32 (word.of_Z 4) outAddr out *
     array scalar32 (word.of_Z 4) keyAddr key *
     array scalar32 (word.of_Z 4) nonceAddr nonce *
     R) m ->
    16 = Z.of_nat (List.length out) ->
    8 = Z.of_nat (List.length key) ->
    3 = Z.of_nat (List.length nonce) ->
    WeakestPrecondition.call functions "chacha20_block" t m [outAddr; keyAddr; nonceAddr; cval]
                             (fun t' m' rets => exists out',
                                  t' = t /\ (array scalar32 (word.of_Z 4) outAddr out' *
                                            array scalar32 (word.of_Z 4) keyAddr key *
                                            array scalar32 (word.of_Z 4) nonceAddr nonce *
                                            R) m' /\ rets = []).

Hint Rewrite
     word.unsigned_of_Z word.signed_of_Z word.of_Z_unsigned word.unsigned_add word.unsigned_sub word.unsigned_opp word.unsigned_or word.unsigned_and word.unsigned_xor word.unsigned_not word.unsigned_ndn word.unsigned_mul word.signed_mulhss word.signed_mulhsu word.unsigned_mulhuu word.unsigned_divu word.signed_divs word.unsigned_modu word.signed_mods word.unsigned_slu word.unsigned_sru word.signed_srs word.unsigned_eqb word.unsigned_ltu word.signed_lts
     using trivial
  : word_laws.

Import BasicC64Semantics. (* for ring *)

Axiom admit : forall {T}, T.
Lemma chacha20_ok : program_logic_goal_for_function! chacha20_block.
Proof.
  straightline.
  repeat (destruct out; [cbn in H0; congruence |]).
  repeat (destruct key; [cbn in H1; congruence |]).
  repeat (destruct nonce; [cbn in H2; congruence |]).
  cbn [array word.add word.of_Z] in H.
  Local Ltac word_add_trans_one addr :=
    match goal with
    | [ H : context[@word.add _ ?w (word.add addr ?x) ?y] |- _ ] =>
      replace (@word.add _ w (word.add addr x) y) with (@word.add _ w addr (word.add x y)) in H by ring
    end.
  Local Ltac word_add_trans addr :=
    repeat word_add_trans_one addr.
  word_add_trans outAddr.
  word_add_trans keyAddr.
  word_add_trans nonceAddr.
  repeat match goal with
         | [ H : context[@word.add _ ?w (word.of_Z ?x) (word.of_Z ?y)] |- _ ] =>
           let z := eval cbv in (x + y) in
               change (@word.add _ w (word.of_Z x) (word.of_Z y)) with (@word.of_Z _ w z) in H
         end.
  repeat straightline.
  subst c95.
  match type of H with
  | ?f m => set (Hsep := f)
  end.
  refine (tailrec (HList.polymorphic_list.nil) ("i"::"out"::"key"::"nonce"::"countervalue"::"x0"::"x1"::"x2"::"x3"::"x4"::"x5"::"x6"::"x7"::"x8"::"x9"::"x10"::"x11"::"x12"::"x13"::"x14"::"x15"::nil)%list%string (fun l t m i out key nonce cval _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => PrimitivePair.pair.mk (Hsep m /\ word.unsigned i = 10 - Z.of_nat l /\ (l <= 10)%nat) (fun T M I OUT KEY NONCE CVAL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => T = t /\ OUT = out /\ KEY = key /\ NONCE = nonce /\ CVAL = cval /\ Hsep M)) lt _ _ _ _ _);
    cbn [reconstruct map.putmany_of_list HList.tuple.to_list
         HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *.

  { repeat straightline. }
  { exact lt_wf. }
  { split; [| split].
    { subst Hsep.
      ecancel_assumption. }
    { subst i.
      rewrite word.unsigned_of_Z.
      cbv [word.wrap].
      rewrite Zmod_0_l.
      match goal with
      | [ |- _ = _ - Z.of_nat ?n ] =>
        unify n (10%nat)
      end.
      reflexivity.
    }
    { blia. }
  }
  { Notation "( x , y , .. , z )" := (PrimitivePair.pair.mk .. (PrimitivePair.pair.mk x y) .. z) : core_scope.
    Notation "'dlet' x .. y := v 'in' f" := (dlet.dlet v (fun x => .. (fun y => f) .. ))
                                              (at level 200, x binder, y binder, f at level 200, format "'dlet'  x .. y  :=  v  'in' '//' f").
    Set Printing Depth 1000000.
    repeat match goal with |- forall _, _ => straightline end.
    Time repeat (straightline; []).
    straightline; [ | solve [ intuition ] ].
    straightline.
    Import NotationsCustomEntry.
    Ltac straightline_cleanup_clear ::= fail.
    Ltac cbn_interp_binop ::= fail.
    Ltac straightline_cleanup_subst ::= fail.
    Ltac straightline_side_condition_solver ::= idtac.
    Ltac straightline_side_condition_solver_inline ::= solve [ repeat straightline ].
    Ltac find_hyp_for body :=
      match goal with
      | [ H := ?x |- _ ]
        => let __ := match goal with _ => constr_eq body x end in
           H
      end.
    Ltac subst_after H :=
      repeat match goal with
             | [ H' := _ |- _ ] => tryif constr_eq H H' then fail 1 else subst H'
             end.
    Ltac instantiate_evar ev body :=
      idtac;
      let H := fresh in
      let __ := constr:(match ev return True with
                        | H => ltac:(instantiate (1:=body) in (value of H);
                                     exact I)
                        end) in
      idtac.
    Ltac subst_var x :=
      tryif is_var x
      then try (let x' := (eval cbv delta [x] in x) in
                tryif is_var x' then subst x; subst_var x' else idtac)
      else idtac.
    Ltac refine_eq_refl_v T v ::=
      match goal with
      | [ |- _ = @Some ?T ?x ]
        => subst_var x;
           let x := lazymatch goal with |- _ = Some ?x => x end in
           try clearbody x;
           vm_compute; refine (@eq_refl (option T) (@Some T x))
      | _ => assert_succeeds refine (@eq_refl T v); shelve
      end.
    Ltac refine_eq_refl ::=
      idtac;
      match goal with
      | [ |- ?x = ?v :> ?T ]
        => is_evar x;
           let H := find_hyp_for x in
           subst_after H;
           cbn [interp_binop];
           let v := lazymatch goal with |- _ = ?v => v end in
           instantiate_evar x v;
           refine (@eq_refl T v)
      | _ => assert_succeeds refine eq_refl; shelve
      end.
    Ltac straightline_set ::=
      idtac;
      (let s :=
         match goal with
         | |- @cmd _ _ _ _ _ _ _ (Syntax.cmd.set ?s ?e) _ _ _ ?post => s
         end
       in
       let e :=
         match goal with
         | |- @cmd _ _ _ _ _ _ _ (Syntax.cmd.set ?s ?e) _ _ _ ?post => e
         end
       in
       let post :=
         match goal with
         | |- @cmd _ _ _ _ _ _ _ (Syntax.cmd.set ?s ?e) _ _ _ ?post => post
         end
       in
       unfold1_cmd_goal; (cbv beta match delta [cmd_body]);
       (let x := ident_of_string.ident_of_string s in
        ensure_free x;
        lazymatch goal with
        | [ |- ex ?T ]
          => lazymatch T with
             | (fun y : ?A => ?P /\ ?Q)
               => refine (let x : A := _ in @ex_intro A T x (@conj match x return Prop with y => P end match x return Prop with y => Q end _ _))
             end
        end;[ straightline_side_condition_solver |  ])).
    cbv [reconstruct HList.tuple.of_list map.putmany_of_tuple List.length] in localsmap.
    Set Ltac Profiling. Reset Ltac Profile.
    Time repeat match goal with H : Syntax.cmd.cmd |- _ => subst H end.
    Time unshelve (repeat lazymatch goal with
                          | [ |- cmd _ ?c _ _ _ _ ] => (idtac c; time "cmd straightline" straightline)
                          | [ |- dlet x := _ in _ ] => straightline
                          end); shelve_unifiable.
    Show Ltac Profile.
    HERE
    Set Printing All.
    Print Ltac straightline_set.
    Ltac subst_var x :=
      tryif is_var x
      then try (let x' := (eval cbv delta [x] in x) in
                tryif is_var x' then subst x; subst_var x' else idtac)
      else idtac.
    Time all: [ > match goal with
                  | [ |- _ = Some ?x ]
                    => subst_var x
                  end .. | ].
    Time all: [ > match goal with
                  | [ |- _ = Some ?x ]
                    => try clearbody x
                  end .. | ].
    Time all: [ > match goal with
                  | [ |- _ = Some ?x ]
                    => vm_compute; reflexivity
                  end .. | ].
    Time 1: vm_compute; reflexivity.
    Time 1: vm_compute; reflexivity.
    Time 1: vm_compute; reflexivity.
    Time 1: vm_compute; reflexivity.
    Time 1: vm_compute; reflexivity.
    1: move x19 at bottom.

    Time all: [ > vm_compute .. | ].
    { vm_compute.
    { match goal with
      | [ |- ?x = ?v :> ?T ]
        => is_evar x;
           let H := find_hyp_for x in
           subst_after H;
           cbn [interp_binop];
           let v := lazymatch goal with |- _ = ?v => v end in
           instantiate_evar x v
      end.
      move x at bottom.
      instantiate_evar x v;
           reflexivity

    end.
    all: match goal with
         | [ |- ?x = ?v :> ?T ]
           => is_evar x; idtac
         | _ => shelve
         end; let n := numgoals in idtac "Num goals:" n.
    { Time let x := lazymatch goal with |- ?x = _ => x end in
           is_evar x;
      let v := match goal with H := ?x' |- _ => let __ := match goal with _ => constr_eq x' x end in H end in
      idtac v;
      repeat match goal with
             | [ H := _ |- _ ] => tryif constr_eq H v then fail 1 else subst H
             end;
      cbn [interp_binop].
      Time lazymatch goal with
           | [ |- ?x = ?y ]
             => let x' := fresh in
                do 10 assert_succeeds (idtac; let __ := constr:(match x return True with x' => ltac:(instantiate (1:=y) in (value of x'); exact I) end) in
                reflexivity)
           end.

           instantiate (1:=y).
           do 10 assert_succeeds (instantiate (1:=y); reflexivity).
      Time do 10 assert_succeeds reflexivity.
      end
           | [

      2: {
      2:lazymatch goal with
        | [ |- ?x = ?y ]
          => instantiate(1:=y); reflexivity
        end.
    1: idtac "reflexivity".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; reflexivity)
                    | _ => idtac
                    end. (* Finished transaction in 14.835 secs (14.794u,0.04s) (su
    {
      Info  straightline.
    Show Ltac Profile.

    Ltac straightline_subst :=
      idtac;
      lazymatch goal with
      | [ |- @cmd _ _ _ _ _ _ _ (Syntax.cmd.set ?s ?e) _ _ _ ?post ]
        => fail
      | [ |- @cmd _ _ _ _ _ _ _ ?c _ _ _ ?post ]
        => time "unfold"
                (idtac;
                 let c := eval hnf in c in
                   lazymatch c with
                   | Syntax.cmd.while _ _ => fail
                   | Syntax.cmd.cond _ _ _ => fail
                   | Syntax.cmd.interact _ _ _ => fail
                   | _ => idtac
                   end; unfold1_cmd_goal; cbv beta match delta [cmd_body])
      end.
    Ltac straightline_set' :=
      idtac;
      lazymatch goal with
      | [ |- @cmd _ _ _ _ _ _ _ (Syntax.cmd.set ?s ?e) _ _ _ ?post ]
        => time "handle set"
                (unfold1_cmd_goal; (cbv beta match delta [cmd_body]);
                 (let x := ident_of_string.ident_of_string s in
                  let x' := fresh x in
                  try (rename x into x');
                  time "letexists" letexists _ as x;
                  time "split" split))
      end.
    Ltac straightline_unfold_expr :=
      lazymatch goal with
      | |- @dexpr _ _ _ _ _ _ _ _ => idtac
      | |- @expr _ _ _ _ _ _ _ _ => idtac
      end;
      time "unfold" repeat
           match goal with
           | |- @dexpr _ _ _ _ _ _ _ _ => cbv beta delta [dexpr]
           | |- @expr _ _ _ _ _ _ _ _ => unfold1_expr_goal; (cbv beta match delta [expr_body])
           | |- @get _ _ _ _ _ _ => (cbv beta delta [get])
           | |- @literal _ _ _ _ => (cbv beta delta [literal])
           end.
    Ltac straightline_eexists_intro_split :=
      lazymatch goal with
      | [ |- @ex _ (fun x => and ?P ?Q) ]
        => let x' := fresh x in
           time "refine let_ex_intro_split" refine (let x' := _ in @ex_intro _ (fun x => and P Q) x' (@conj (match x' with x => P end) (match x' with x => Q end) _ _))
      end.
    Ltac intro_let :=
      idtac;
      lazymatch goal with
      | [ |- dlet x := ?v in ?P ]
        => time "intro let" (change (let x := v in P); intros)
      end.
    Ltac print_context_size' base :=
      lazymatch goal with
      | [ H : _ |- _ ] => revert H; print_context_size' (S base)
      | _ => idtac "Context size:" base
      end.
    Ltac print_context_size := assert_succeeds (idtac; print_context_size' O).
    Ltac do_refl_slow :=
      lazymatch goal with
      | |- @eq ?T1 (@map.get string (@word.rep _ _) _ _ _) (@Some ?T ?v) =>
          time "refl"
               (idtac;
                let v' := rdelta.rdelta v in
                is_evar v'; change v with v'; exact (@eq_refl T1 (@Some T v')))
      | |- @eq ?T ?x ?y
        => time "refl"
                (idtac;
                 let x := rdelta.rdelta x in
                 is_evar x; change (@eq T x y);
                 exact (@eq_refl T y))
      end.
    Ltac do_refl :=
      lazymatch goal with
      | |- @eq ?T1 ?y (@Some ?T ?v) =>
          time "refl"
               (idtac;
                let v' := rdelta.rdelta v in
                is_evar v'; change v with v';
                exact (@eq_refl T1 (@Some T v')))
      | |- @eq ?T ?x ?y
        => time "refl"
                (idtac;
                 let x := rdelta.rdelta x in
                 is_evar x; change (@eq T x y);
                 instantiate(1:=y); reflexivity)
      end.
    Ltac prof_refl :=
      print_context_size; match goal with
      | |- @eq ?T1 (@map.get string (@word.rep _ _) _ _ _) (@Some ?T ?v) =>
          let v' := rdelta.rdelta v in
          is_evar v'; change v with v'; do 100 assert_succeeds (once time "slow" exact (@eq_refl _ _)); do 100 assert_succeeds (once time "fast" exact (@eq_refl T1 (@Some T v'))); exact (@eq_refl T1 (@Some T v')) end.
    Ltac step :=
      repeat lazymatch goal with
             | [ |- cmd _ ?c _ _ _ _ ]
               => is_var c;
                  straightline_subst
             end; [];
      straightline_set';
      [ straightline_unfold_expr; [];
        straightline_eexists_intro_split;
        [ do_refl
        | straightline_unfold_expr;
          repeat intro_let;
          try do_refl ]
      | intro_let ].
    (*Ltac straightline_set ::= match goal with |- WeakestPrecondition.cmd _ (Syntax.cmd.set ?s ?e) _ _ _ ?post => shelve end.*)
    (*Ltac straightline_split ::=
      match goal with
      | |- exists l', Interface.map.of_list_zip ?ks ?vs = Some l' /\ _ => idtac
      | |- exists l', Interface.map.putmany_of_list_zip ?ks ?vs ?l = Some l' /\ _ => idtac
      | |- exists x, ?P /\ ?Q => idtac
      | |- exists x, Markers.split (?P /\ ?Q) => idtac
      | |- Markers.unique (exists x, Markers.split (?P /\ ?Q)) => idtac
      | |- Markers.unique (Markers.left ?G) => idtac
      | |- Markers.split ?G => idtac
      end;
      shelve.*)
    (* Ltac straightline_refl :=
  first
  [ match goal with
    | |- @eq (@map.rep string (@word.rep _ _) _) _ _ => idtac
    end; eapply (@SortedList.eq_value _ _ _); refine (@eq_refl _ _)
  | match goal with
    | |- @eq _ (@map.get string (@word.rep _ _) ?M ?m ?k) (@Some _ ?e') =>
          let e := rdelta.rdelta e' in
          is_evar e;
           once
            (let v :=
              multimatch goal with
              | x:=context [ @map.put _ _ M _ k ?v ]:_ |- _ => v
              end
             in
             unify e v; refine (@eq_refl _ (@Some _ v)))
    end
  | let v :=
     match goal with
     | |- @eq _ (@map.get string (@word.rep _ _) _ _ _) (@Some _ ?v) => v
     end
    in
    let v' := rdelta.rdelta v in
    is_evar v'; change v with v'; refine (@eq_refl _ _)
  | let x := match goal with
             | |- @eq _ ?x ?y => x
             end in
    let y := match goal with
             | |- @eq _ ?x ?y => y
             end in
    first
    [ let y := rdelta.rdelta y in
      is_evar y; change (@eq _ x y); refine (@eq_refl _ _)
    | let x := rdelta.rdelta x in
      is_evar x; change (@eq _ x y); refine (@eq_refl _ _)
    | let x := rdelta.rdelta x in
      let y := rdelta.rdelta y in
      constr_eq x y; refine (@eq_refl _ _) ] ]
     *)
    (*Ltac straightline_refl ::= first
                                 [ match goal with
    | |- @eq (@map.rep string (@word.rep _ _) _) _ _ => idtac
    end; eapply (@SortedList.eq_value _ _ _); assert_succeeds refine (@eq_refl _ _); shelve
  | match goal with
    | |- @eq _ (@map.get string (@word.rep _ _) ?M ?m ?k) (@Some _ ?e') =>
          let e := rdelta.rdelta e' in
          is_evar e;
           once
            (let v :=
              multimatch goal with
              | x:=context [ @map.put _ _ M _ k ?v ] |- _ => v
              end
             in
             unify e v; assert_succeeds refine (@eq_refl _ (@Some _ v))); shelve
    end
  | let v :=
     match goal with
     | |- @eq _ (@map.get string (@word.rep _ _) _ _ _) (@Some _ ?v) => v
     end
    in
    let v' := rdelta.rdelta v in
    is_evar v'; change v with v'; assert_succeeds refine (@eq_refl _ _); shelve
  | let x := match goal with
             | |- @eq _ ?x ?y => x
             end in
    let y := match goal with
             | |- @eq _ ?x ?y => y
             end in
    first
    [ let y := rdelta.rdelta y in
      is_evar y; change (@eq _ x y); assert_succeeds refine (@eq_refl _ _); shelve
    | let x := rdelta.rdelta x in
      is_evar x; change (@eq _ x y); assert_succeeds refine (@eq_refl _ _); shelve
    | let x := rdelta.rdelta x in
      let y := rdelta.rdelta y in
      constr_eq x y; assert_succeeds refine (@eq_refl _ _); shelve ] ].*)
    (*Time lazymatch goal with |- cmd _ _ _ _ _ ?postc => set (post := postc) end. (* Finished transaction in 0.001 secs (0.001u,0.s) (successful) *)*)
    (*Ltac refine_eq_refl ::= lazymatch goal with
                            | [ |- ?x = ?y :> ?T ]
                              => tryif is_evar x
                                then (instantiate(1:=y); reflexivity)
                                else
                                  (idtac x "=" y ":>" T; refine eq_refl)
                            end.*)
    Set Ltac Profiling. Reset Ltac Profile.
    Time unshelve (repeat lazymatch goal with
                          | [ |- cmd _ ?c _ _ _ _ ] => (idtac c; time "cmd straightline" straightline)
                          | [ |- dlet x := _ in _ ] => straightline
                          end); shelve_unifiable.
    Show Ltac Profile.
    (* without set post: total time:     30.933s

 tactic                                   local  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─straightline --------------------------   0.0%  98.9%    1324    0.706s
─straightline_side_condition_solver_inli  78.2%  78.2%      97    0.616s
─refine (uconstr) ----------------------  77.9%  77.9%     516    0.161s
─straightline_refl ---------------------   1.0%  54.9%     419    0.196s
─refine_eq_refl ------------------------   0.0%  20.2%     118    0.119s
─straightline_set ----------------------   0.1%  18.6%    1194    0.100s
─straightline_split --------------------   0.1%  18.6%     161    0.076s
─letexists_as --------------------------   0.3%  12.8%      97    0.075s
─straightline_cleanup ------------------   0.4%   5.7%    1324    0.008s
─straightline_cleanup_destruct ---------   4.2%   4.2%    1194    0.007s
─unify (constr) (constr) ---------------   3.8%   3.8%     140    0.021s
─split ---------------------------------   3.6%   3.6%     258    0.019s
─change (x = y) ------------------------   2.6%   2.6%      97    0.016s
─unfold1_cmd_goal ----------------------   0.1%   2.1%     193    0.007s

 tactic                                   local  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─straightline --------------------------   0.0%  98.9%    1324    0.706s
 ├─straightline_side_condition_solver_in  78.2%  78.2%      97    0.616s
 ├─straightline_refl -------------------   1.0%  54.9%     419    0.196s
 │ ├─refine (uconstr) ------------------  27.2%  27.2%     140    0.161s
 │ ├─refine_eq_refl --------------------   0.0%  20.2%     118    0.119s
 │ │└refine (uconstr) ------------------  20.1%  20.1%     118    0.119s
 │ ├─unify (constr) (constr) -----------   3.8%   3.8%     140    0.021s
 │ └─change (x = y) --------------------   2.6%   2.6%      97    0.016s
 ├─straightline_set --------------------   0.1%  18.6%    1194    0.100s
 │ ├─letexists_as ----------------------   0.3%  12.8%      97    0.075s
 │ │└refine (uconstr) ------------------  12.2%  12.2%      97    0.073s
 │ └─split -----------------------------   3.4%   3.4%      97    0.019s
 ├─straightline_split ------------------   0.1%  18.6%     161    0.076s
 │└refine (uconstr) --------------------  18.3%  18.3%     161    0.076s
 └─straightline_cleanup ----------------   0.3%   4.6%    1227    0.008s
  └straightline_cleanup_destruct -------   4.2%   4.2%    1194    0.007s

*)
    (* with set post: total time:     29.652s

 tactic                                   local  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─straightline --------------------------   0.1%  99.9%    1324    0.682s
─straightline_side_condition_solver_inli  84.4%  84.4%      97    0.603s
─refine (uconstr) ----------------------  83.7%  83.7%     516    0.156s
─straightline_refl ---------------------   1.2%  59.0%     419    0.171s
─refine_eq_refl ------------------------   0.0%  22.2%     118    0.126s
─straightline_split --------------------   0.1%  20.3%     161    0.071s
─straightline_set ----------------------   0.1%  14.3%    1194    0.087s
─letexists_as --------------------------   0.0%  13.0%      97    0.080s
─straightline_cleanup ------------------   0.4%   5.1%    1324    0.004s
─straightline_cleanup_destruct ---------   4.5%   4.5%    1194    0.004s
─unify (constr) (constr) ---------------   4.1%   4.1%     140    0.019s
─change (x = y) ------------------------   2.8%   2.8%      97    0.018s

 tactic                                   local  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─straightline --------------------------   0.1%  99.9%    1324    0.682s
 ├─straightline_side_condition_solver_in  84.4%  84.4%      97    0.603s
 ├─straightline_refl -------------------   1.2%  59.0%     419    0.171s
 │ ├─refine (uconstr) ------------------  28.4%  28.4%     140    0.156s
 │ ├─refine_eq_refl --------------------   0.0%  22.2%     118    0.126s
 │ │└refine (uconstr) ------------------  22.2%  22.2%     118    0.126s
 │ ├─unify (constr) (constr) -----------   4.1%   4.1%     140    0.019s
 │ └─change (x = y) --------------------   2.8%   2.8%      97    0.018s
 ├─straightline_split ------------------   0.1%  20.3%     161    0.071s
 │└refine (uconstr) --------------------  20.1%  20.1%     161    0.070s
 ├─straightline_set --------------------   0.1%  14.3%    1194    0.087s
 │└letexists_as ------------------------   0.0%  13.0%      97    0.080s
 │└refine (uconstr) --------------------  13.0%  13.0%      97    0.080s
 └─straightline_cleanup ----------------   0.4%   5.0%    1227    0.004s
  └straightline_cleanup_destruct -------   4.5%   4.5%    1194    0.004s

     *)
    (* after adjust refine refl
total time:     26.750s

 tactic                                   local  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─straightline --------------------------   0.1%  98.7%    1324    0.639s
─straightline_side_condition_solver_inli  73.7%  73.7%      97    0.570s
─refine (uconstr) ----------------------  71.3%  71.3%     419    0.133s
─straightline_refl ---------------------   1.2%  45.4%     419    0.146s
─straightline_set ----------------------   0.1%  22.5%    1194    0.103s
─straightline_split --------------------   0.1%  21.5%     161    0.066s
─letexists_as --------------------------   0.4%  15.8%      97    0.083s
─straightline_cleanup ------------------   0.4%   7.9%    1324    0.335s
─straightline_cleanup_destruct ---------   6.1%   6.1%    1194    0.334s
─refine_eq_refl ------------------------   5.3%   5.3%     118    0.098s
─unify (constr) (constr) ---------------   4.3%   4.3%     140    0.015s
─split ---------------------------------   4.0%   4.0%     258    0.019s
─change (x = y) ------------------------   2.9%   2.9%      97    0.016s
─unfold1_cmd_goal ----------------------   0.1%   2.5%     193    0.008s
─change G ------------------------------   2.2%   2.2%     484    0.008s
─straightline_unfold -------------------   0.2%   2.1%    1097    0.007s

 tactic                                   local  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─straightline --------------------------   0.1%  98.7%    1324    0.639s
 ├─straightline_side_condition_solver_in  73.7%  73.7%      97    0.570s
 ├─straightline_refl -------------------   1.2%  45.4%     419    0.146s
 │ ├─refine (uconstr) ------------------  31.4%  31.4%     140    0.133s
 │ ├─refine_eq_refl --------------------   5.3%   5.3%     118    0.098s
 │ │└refine (uconstr) ------------------   3.6%   3.6%      21    0.098s
 │ ├─unify (constr) (constr) -----------   4.3%   4.3%     140    0.015s
 │ └─change (x = y) --------------------   2.9%   2.9%      97    0.016s
 ├─straightline_set --------------------   0.1%  22.5%    1194    0.103s
 │ ├─letexists_as ----------------------   0.4%  15.8%      97    0.083s
 │ │└refine (uconstr) ------------------  15.1%  15.1%      97    0.079s
 │ └─split -----------------------------   3.9%   3.9%      97    0.019s
 ├─straightline_split ------------------   0.1%  21.5%     161    0.066s
 │└refine (uconstr) --------------------  21.2%  21.2%     161    0.065s
 ├─straightline_cleanup ----------------   0.4%   6.6%    1227    0.335s
 │└straightline_cleanup_destruct -------   6.1%   6.1%    1194    0.334s
 └─straightline_unfold -----------------   0.2%   2.1%    1097    0.007s

     *)
    cbv beta.
    (* prove [enforce] *)
    match goal with |- Markers.unique (Markers.left (exists x131 x132 x133 x134 x135 x136 x137 x138 x139 x140 x141 x142 x143 x144 x145 x146 x147 x148 x149 x150 x151, _)) => idtac end.

    repeat letexists. split.
    {
      cbv [enforce gather].
      Time repeat match goal with
                  | [ H : ?T |- _ ]
                    => lazymatch T with
                       | word.rep
                         => (let v := (eval cbv delta [H] in H) in
                             (tryif is_evar v then fail else clearbody H))
                       end
                  end.
      Time cbv.
      split; reflexivity. }
    repeat straightline_cleanup.

    letexists. split.
    2:split.
    1: split.
    2: split.

    all : repeat straightline.
    all : try typeclasses eauto with core.
    all: repeat match goal with
                | [ |- context[?x] ] => subst x
                end.
    all: match goal with
         | [ |- ?x = ?y - Z.of_nat ?ev ]
           => is_evar ev; unify ev (Z.to_nat (y - x))
         | _ => idtac
         end.
    all: match goal with
         | [ H := if ?b then _ else _ |- _ ] => destruct b eqn:?
         end.
    all: match goal with
         | [ H : ?x <> 0 |- _ ] => try (change (0 <> 0) in H; exfalso; apply H; reflexivity)
         end.
    all: match goal with
         | [ H : context[word.ltu] |- _ ] => rewrite word.unsigned_ltu, Z.ltb_lt in H
         end.
    all: rewrite ?word.unsigned_add, ?word.unsigned_of_Z.
    all: repeat match goal with
                | [ H : word.unsigned ?x = _ |- context[word.unsigned ?x] ]
                  => generalize (word.unsigned_range x); move x at bottom; rewrite H in *
                end.
    all: match goal with
         | [ H : context[word.unsigned (word.of_Z ?x)] |- _ ]
           => change (word.unsigned (word.of_Z x)) with x in H
         end.
    all: change (word.wrap 1) with 1.
    all: cbv [word.wrap].
    all: repeat match goal with
                | [ |- context[?x mod ?m] ]
                  => assert (0 <= x < m) by (Z.to_euclidean_division_equations; Lia.nia);
                     replace (x mod m) with x in * by (Z.to_euclidean_division_equations; Lia.nia)
                end.
    all: intros.
    all: try Lia.lia. }

  subst Hsep.
  repeat straightline.
  letexists _.
  split.
  1: repeat straightline.
  2: repeat straightline.
  all: exact admit. Unshelve. exact admit. Time Qed.
  eexists; split.
  replace (scalar32 x47 r) with (scalar32 (word.add x47 (word.of_Z 0)) r) in H8.
  2: {
    f_equal.
    1: {
      intros.
      rewrite H9.
      reflexivity.
    }
    ring.
  }
  repeat straightline.
  intuition.
  destruct out; cbn in H0; [| blia].
  cbn [array] in H19.
  let x := open_constr:(@cons word32 _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ nil)))))))))))))))) in
  unify out' x.
  subst out'.
  cbn [array].
  repeat match goal with
  | [ |- context[@word.add _ ?w (word.add x47 ?x) ?y] ] =>
    replace (@word.add _ w (word.add x47 x) y) with (@word.add _ w x47 (word.add x y)) by ring
  end.
  repeat match goal with
  | [ |- context[@word.add _ ?w (word.add x16 ?x) ?y] ] =>
    replace (@word.add _ w (word.add x16 x) y) with (@word.add _ w x16 (word.add x y)) by ring
  end.
  repeat match goal with
  | [ |- context[@word.add _ ?w (word.add x17 ?x) ?y] ] =>
    replace (@word.add _ w (word.add x17 x) y) with (@word.add _ w x17 (word.add x y)) by ring
  end.
  repeat match goal with
         | [ |- context[@word.add _ ?w (word.of_Z ?x) (word.of_Z ?y)] ] =>
           let z := eval cbv in (x + y) in
               change (@word.add _ w (word.of_Z x) (word.of_Z y)) with (@word.of_Z _ w z)
         end.
  rewrite !word.of_Z_unsigned in H19.
  repeat match type of H19 with
         | context[scalar32 ?a _] =>
           subst a
         end.
  replace (word.add x47 (word.of_Z 0)) with x47 in H19 by ring.
  ecancel_assumption.



    all: lazymatch goal with
         | [ |- ?x = ?y - Z.of_nat ?ev ]
           => is_evar ev; unify ev (Z.to_nat (y - x))
         | _ => idtac
         end.
    all: try Lia.lia.
    2: {
    all: change (1 mod _) with 1.
    all: lazymatch goal with
         | [ |- ?x = ?y - Z.of_nat ?z ]
           => let z' := rdelta.rdelta z in
              is_evar z';
              unify z' (Z.to_nat (y - x))
         | _ => idtac
         end.
    all: repeat match goal with
                | [ |- context[?x] ] => subst x
                end.
    all: rewrite ?word.unsigned_add, ?word.unsigned_of_Z.
    all: cbv [word.wrap].
    all: repeat match goal with
                | [ H : word.unsigned ?x = _ |- context[word.unsigned ?x] ]
                  => generalize (word.unsigned_range x); rewrite H
                end.
    all: intros.
    all: repeat match goal with
                | [ |- context[?x mod ?m] ]
                  => assert (0 <= x < m) by (Z.to_euclidean_division_equations; Lia.nia);
                     replace (x mod m) with x in * by (Z.to_euclidean_division_equations; Lia.nia)
                end.
    all: try Lia.lia.
    { move v at bottom.
      clear -H5.
      zify.
      repeat match goal with H : and _ _ |- _ => destruct H | H : or _ _ |- _ => destruct H end; subst.
      all: try Lia.lia.
      assert (Z.of_nat v <= 1) by Lia.lia.
      assert ((v = 1 \/ v = 0)%nat) by Lia.lia.
      destruct H1; subst; try Lia.lia.
      cbn.
    all: zify.
    all: match goal with
         | [ |- ?x = ?y ] => cut (x - y = 0); [ Lia.lia | ring_simplify ]
         end.
    { move v at bottom.
      revert H5.
      clear.
      change (1 mod 2^64) with 1.

      zify.
      all: assert (0 < 2^64) by Lia.lia.
      assert (0 < 2) by Lia.lia.
      assert (2^64 <> 0) by Lia.lia.
      Z.to_euclidean_division_equations.
      zify.
    all: repeat match goal with
                | [ |- context[word.unsigned ?x] ]
                  => is_var x;
                     generalize (word.unsigned x)
                end.
    {
      clear; intros.
      all: assert (0 < 2^64) by Lia.lia.
      assert (0 < 2) by Lia.lia.
      assert (2^64 <> 0) by Lia.lia.
      Z.to_euclidean_division_equations.
      zify.

    Search word.unsigned Z.le.
    1: zify; Z.to_euclidean_division_equations.
    1: Lia.nia.
    Search word.wrap.
    2: { clear.
         set (k:=word.unsigned _).
         clearbody k.
         zify.
         repeat match goal with H : and _ _ |- _ => destruct H | H : or _ _ |- _ => destruct H end; subst.
         all: try Lia.lia.
         destruct_head'
         Lia.lia.

    Search Z.to_nat Z.sub.

      match goal with
      | [ |- word.unsigned ?i = _ ] => subst i
      end.
      rewrite word.unsigned_add.
      match goal with
      | [ H : word.unsigned ?x = _ |- context[word.unsigned ?x] ]
        => rewrite H
      end.

              .
    { move i at bottom.
      move x at bottom.
      match goal with
      | [ H : word.unsigned ?x = ?n - Z.of_nat ?v |- word.unsigned
    all: lazymatch goal with
         | [ |- ?x = ?y - Z.of_nat ?z ]
           => let z' := rdelta.rdelta z in
              is_evar z';
              cut (y - x = z)
         | _ => idtac
         end.
    Search (_ = _ - _).

    {
      lazymatch goal with
      | [ H : word.unsigned br <> 0 |- _ ] =>
        subst br;
          rewrite word.unsigned_ltu in H;
          lazymatch type of H with
          | word.unsigned (if ?x <? ?y then _ else _) <> _ =>
            destruct (Z.ltb_spec0 x y) as [Hv |];
              rewrite word.unsigned_of_Z in H;
              cbv in H;
              [| congruence]
          end
      end.
      move i at bottom.

      subst x131.
      subst v'.
      match goal with
      | [ |- word.unsigned ?w = _ ] =>
        change w with (word.add x (word.of_Z 1))
      end.
      rewrite word.unsigned_add, word.unsigned_of_Z.
      match goal with
      | [ H : word.unsigned _ = 10 - _ |- _ ] =>
        rewrite H in *
      end.
      rewrite word.unsigned_of_Z in Hv.
      change (word.wrap 10) with 10 in Hv.
      instantiate (1 := Nat.pred v).
      rewrite Nat2Z.inj_pred; [| blia].
      change (word.wrap 1) with 1.
      cbv [word.wrap].
      rewrite Z.mod_small; [blia |].
      split; [blia |].
      match goal with
      | [ H : (_ <= _)%nat |- _ ] =>
        let H' := fresh "H" in
        pose proof (inj_le _ _ H) as H'; cbn in H'
      end.
      match goal with
      | [ |- _ < 2^?w ] =>
          let w' := eval cbv in w in
          change w with w'
      end.
      blia.
    }
    { subst v'. blia. }
    { subst v'.
      lazymatch goal with
      | [ H : word.unsigned br <> 0 |- _ ] =>
        subst br;
          rewrite word.unsigned_ltu in H;
          lazymatch type of H with
          | word.unsigned (if ?x <? ?y then _ else _) <> _ =>
            destruct (Z.ltb_spec0 x y) as [Hv |];
              rewrite word.unsigned_of_Z in H;
              cbv in H;
              [| congruence]
          end
      end.
      match goal with
      | [ H : word.unsigned _ = 10 - _ |- _ ] =>
        rewrite H in *
      end.
      rewrite word.unsigned_of_Z in Hv.
      change (word.wrap 10) with 10 in Hv.
      apply lt_pred_n_n.
      apply Nat2Z.inj_lt.
      blia.
    }
  }

  subst Hsep.
  repeat straightline.
  replace (scalar32 x47 r) with (scalar32 (word.add x47 (word.of_Z 0)) r) in H8.
  2: {
    f_equal.
    1: {
      intros.
      rewrite H9.
      reflexivity.
    }
    ring.
  }
  repeat straightline.
  intuition.
  destruct out; cbn in H0; [| blia].
  cbn [array] in H19.
  let x := open_constr:(@cons word32 _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ nil)))))))))))))))) in
  unify out' x.
  subst out'.
  cbn [array].
  repeat match goal with
  | [ |- context[@word.add _ ?w (word.add x47 ?x) ?y] ] =>
    replace (@word.add _ w (word.add x47 x) y) with (@word.add _ w x47 (word.add x y)) by ring
  end.
  repeat match goal with
  | [ |- context[@word.add _ ?w (word.add x16 ?x) ?y] ] =>
    replace (@word.add _ w (word.add x16 x) y) with (@word.add _ w x16 (word.add x y)) by ring
  end.
  repeat match goal with
  | [ |- context[@word.add _ ?w (word.add x17 ?x) ?y] ] =>
    replace (@word.add _ w (word.add x17 x) y) with (@word.add _ w x17 (word.add x y)) by ring
  end.
  repeat match goal with
         | [ |- context[@word.add _ ?w (word.of_Z ?x) (word.of_Z ?y)] ] =>
           let z := eval cbv in (x + y) in
               change (@word.add _ w (word.of_Z x) (word.of_Z y)) with (@word.of_Z _ w z)
         end.
  rewrite !word.of_Z_unsigned in H19.
  repeat match type of H19 with
         | context[scalar32 ?a _] =>
           subst a
         end.
  replace (word.add x47 (word.of_Z 0)) with x47 in H19 by ring.
  ecancel_assumption.


    Time unshelve (do 100 straightline); shelve_unifiable.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    Show Ltac Profile.
    Time lazymatch goal with |- cmd _ _ _ _ _ ?postc => set (post := postc) end. (* Finished transaction in 0.001 secs (0.001u,0.s) (successful) *)
    (*Time repeat match goal with H : Syntax.cmd.cmd |- _ => subst H end. (* Finished transaction in 0.648 secs (0.638u,0.01s) (successful) *)*)
    Time unshelve (repeat (repeat straightline_subst; straightline_set'; [ shelve | intro_let ])); shelve_unifiable; [ .. | shelve ]. (* Finished transaction in 3.912 secs (3.807u,0.104s) (successful) *)
    Time all: clear post. (* Finished transaction in 0.577 secs (0.577u,0.s) (successful) *)
    Time all: repeat match goal with H : map.rep -> Prop |- _ => clear H | H : map.rep |- _ => clear H end. (* Finished transaction in 1.009 secs (0.968u,0.041s) (successful) *)
    Time all: straightline_unfold_expr. (* Finished transaction in 0.117 secs (0.117u,0.s) (successful) *)
    Time all: straightline_eexists_intro_split. (* Finished transaction in 0.407 secs (0.407u,0.s) (successful) *)
    Time all: try straightline_unfold_expr. (* Finished transaction in 0.084 secs (0.074u,0.01s) (successful) *)
    Time all: try straightline_eexists_intro_split. (* Finished transaction in 0.319 secs (0.319u,0.s) (successful) *)
    Time all: try intro_let. (* Finished transaction in 0.019 secs (0.019u,0.s) (successful) *)
    Time all: do_refl. (* Finished transaction in 15.81 secs (15.792u,0.017s) (successful) *)
    Show Ltac Profile.
    HERE
(*
total time:     22.532s

 tactic                                   local  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─do_refl -------------------------------  70.2%  70.2%     258   15.810s
─unshelve (tactic1) --------------------   0.4%  17.1%       1    3.844s
─straightline_set' ---------------------   0.5%  12.1%      98    0.066s
─refine (uconstr) ----------------------   6.1%   6.1%     258    0.030s
─clear (hyp_list) ----------------------   5.9%   5.9%    5238    0.021s
─unfold1_cmd_goal ----------------------   0.2%   4.0%     193    0.024s
─letexists_as --------------------------   0.3%   4.0%      97    0.031s
─split ---------------------------------   3.8%   3.8%      97    0.045s
─straightline_eexists_intro_split ------   3.2%   3.2%     483    0.404s
─change G ------------------------------   3.1%   3.1%     484    0.024s
─straightline_subst --------------------   0.3%   2.6%     194    0.024s
─subst (ne_hyp_list) -------------------   2.5%   2.5%      96    0.053s

 tactic                                   local  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─do_refl -------------------------------  70.2%  70.2%     258   15.810s
─unshelve (tactic1) --------------------   0.4%  17.1%       1    3.844s
 ├─straightline_set' -------------------   0.5%  12.1%      98    0.066s
 │ ├─letexists_as ----------------------   0.3%   4.0%      97    0.031s
 │ │└refine (uconstr) ------------------   3.1%   3.1%      97    0.030s
 │ ├─split -----------------------------   3.8%   3.8%      97    0.045s
 │ └─unfold1_cmd_goal ------------------   0.1%   2.0%      97    0.024s
 └─straightline_subst ------------------   0.3%   2.6%     194    0.024s
─clear (hyp_list) ----------------------   5.9%   5.9%    5238    0.021s
─straightline_eexists_intro_split ------   3.2%   3.2%     483    0.404s
└refine (uconstr) ----------------------   3.0%   3.0%     161    0.010s
─subst (ne_hyp_list) -------------------   2.5%   2.5%      96    0.053s

*)
    Unshelve.
    subst post.
    cbv beta.
    HERE
    repeat match goal with H : Syntax.cmd.cmd |- _ => subst H end.
    Time straightline_subst; straightline_set'; [ shelve | intro_let ].
    Time unshelve (repeat (repeat straightline_subst; straightline_set; [ shelve | intro_let ])); shelve_unifiable; [ .. | shelve ].
    Time all: straightline_unfold_expr.
    Time all: straightline_eexists_intro_split.
    Time all: try straightline_unfold_expr.
    Time all: try straightline_eexists_intro_split.
    Time all: try intro_let.
    Time all: do_refl.
    Time unshelve (do 100 straightline); shelve_unifiable.
    Reset Ltac Profile.
    all: let n := numgoals in idtac "Full num goals:" n.
    all: match goal with
         | [ |- ?x = ?v :> ?T ]
           => is_evar x; idtac
         | _ => shelve
         end; let n := numgoals in idtac "Num goals:" n.
    1: idtac "reflexivity".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; reflexivity)
                    | _ => idtac
                    end. (* Finished transaction in 14.835 secs (14.794u,0.04s) (successful) *)
    1: idtac "refine eq_refl".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; refine eq_refl)
                    | _ => idtac
                    end. (* Finished transaction in 26.682 secs (26.652u,0.029s) (successful) *)
    1: idtac "exact eq_refl".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; exact eq_refl)
                    | _ => idtac
                    end. (* Finished transaction in 26.085 secs (26.024u,0.059s) (successful) *)
    1: idtac "refine (@eq_refl T x)".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; refine (@eq_refl T x))
                    | _ => idtac
                    end. (* Finished transaction in 13.641 secs (13.631u,0.009s) (successful) *)
    1: idtac "refine (@eq_refl T v)".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; refine (@eq_refl T v))
                    | _ => idtac
                    end. (* Finished transaction in 13.725 secs (13.694u,0.03s) (successful) *)
    1: idtac "instantiate (1:=v); reflexivity".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; instantiate (1:=v); reflexivity)
                    | _ => idtac
                    end. (* Finished transaction in 1.576 secs (1.526u,0.05s) (successful) *)
    1: idtac "instantiate (1:=v); refine eq_refl".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; instantiate (1:=v); refine eq_refl)
                    | _ => idtac
                    end. (*Finished transaction in 1.915 secs (1.884u,0.03s) (successful)*)
    1: idtac "instantiate (1:=v); refine (@eq_refl T v)".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; instantiate (1:=v); refine (@eq_refl T v))
                    | _ => idtac
                    end. (* Finished transaction in 1.588 secs (1.548u,0.04s) (successful) *)
    1: idtac "unify x v; reflexivity".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; unify x v; reflexivity)
                    | _ => idtac
                    end.
    1: idtac "unify x v; refine eq_refl".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; unify x v; refine eq_refl)
                    | _ => idtac
                    end.
    1: idtac "unify x v; refine (@eq_refl T v)".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; unify x v; refine (@eq_refl T v))
                    | _ => idtac
                    end.
    1: idtac "unify v x; reflexivity".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; unify v x; reflexivity)
                    | _ => idtac
                    end.
    1: idtac "unify v x; refine eq_refl".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; unify v x; refine eq_refl)
                    | _ => idtac
                    end.
    1: idtac "unify v x; refine (@eq_refl T v)".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; unify v x; refine (@eq_refl T v))
                    | _ => idtac
                    end.
    all: print_context_size.
    (*Context size: 186%nat
Context size: 187%nat
Context size: 188%nat
Context size: 189%nat
Context size: 189%nat
Context size: 190%nat
Context size: 191%nat
Context size: 191%nat
Context size: 192%nat
Context size: 193%nat
Context size: 194%nat
Context size: 195%nat
Context size: 195%nat
Context size: 196%nat
Context size: 197%nat
Context size: 197%nat
Context size: 198%nat
Context size: 199%nat
Context size: 200%nat
Context size: 201%nat
Context size: 201%nat
Context size: 202%nat
Context size: 203%nat
Context size: 203%nat
Context size: 204%nat
Context size: 205%nat
Context size: 206%nat
Context size: 207%nat
Context size: 207%nat
Context size: 208%nat
Context size: 209%nat
Context size: 209%nat
Context size: 210%nat
Context size: 211%nat
Context size: 212%nat
Context size: 213%nat
Context size: 213%nat
Context size: 214%nat
Context size: 215%nat
Context size: 215%nat
Context size: 216%nat
Context size: 217%nat
Context size: 218%nat
Context size: 219%nat
Context size: 219%nat
Context size: 220%nat
Context size: 221%nat
Context size: 221%nat
Context size: 222%nat
Context size: 223%nat
Context size: 224%nat
Context size: 225%nat
Context size: 225%nat
Context size: 226%nat
Context size: 227%nat
Context size: 227%nat
Context size: 228%nat
Context size: 229%nat
Context size: 230%nat
Context size: 231%nat
Context size: 231%nat
Context size: 232%nat
Context size: 233%nat
Context size: 233%nat
Context size: 234%nat
Context size: 235%nat
Context size: 236%nat
Context size: 237%nat
Context size: 237%nat
Context size: 238%nat
Context size: 239%nat
Context size: 239%nat
Context size: 240%nat
Context size: 241%nat
Context size: 242%nat
Context size: 243%nat
Context size: 243%nat
Context size: 244%nat
Context size: 245%nat
Context size: 245%nat
Context size: 246%nat
Context size: 247%nat
Context size: 248%nat
Context size: 249%nat
Context size: 249%nat
Context size: 250%nat
Context size: 251%nat
Context size: 251%nat
Context size: 250%nat
     *)
    1: idtac "clear subst".
    Time all: [ > match goal with
                  | [ |- ?x = interp_binop _ _ _ ]
                    => is_evar x;
                repeat match goal with H := ?v |- _ => is_evar v; clear H end
              | _ => idtac
                  end .. | ]. (* Finished transaction in 1.24 secs (1.24u,0.s) (successful) *)
    1: idtac "clear- in evar".
    Time all: [ > match goal with
                  | [ |- ?ev = interp_binop _ ?x ?y ]
                    => is_evar ev;
                try (instantiate(1:=ltac:(clear)) in (value of x));
                try (instantiate(1:=ltac:(clear)) in (value of y));
                instantiate(1:=ltac:(clear -x y)); clear -x y
              | _ => idtac
                end .. | ]. (* Finished transaction in 0.299 secs (0.299u,0.s) (successful) *)
    Time all: [ > match goal with
                  | [ |- ?ev = interp_binop _ ?x ?y ]
                    => is_evar ev;
                print_context_size
              | _ => idtac
                end .. | ]. (* Context size: 2%nat
Context size: 2%nat
Context size: 3%nat
Context size: 3%nat
Context size: 3%nat
Context size: 3%nat
Context size: 3%nat
Context size: 4%nat
Context size: 4%nat
Context size: 3%nat
Context size: 4%nat
Context size: 4%nat
Context size: 3%nat
Context size: 2%nat
Context size: 3%nat
Context size: 3%nat
Context size: 3%nat
Context size: 3%nat
Context size: 3%nat
Context size: 4%nat
Context size: 4%nat
Context size: 3%nat
Context size: 4%nat
Context size: 4%nat
Context size: 3%nat
Context size: 2%nat
Context size: 3%nat
Context size: 3%nat
Context size: 3%nat
Context size: 3%nat
Context size: 3%nat
Context size: 4%nat
Context size: 4%nat

Finished transaction in 0.022 secs (0.022u,0.s) (successful)
*)
    1: idtac "reflexivity".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; reflexivity)
                    | _ => idtac
                    end. (* Finished transaction in 14.835 secs (14.794u,0.04s) (successful) *)
    1: idtac "refine eq_refl".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; refine eq_refl)
                    | _ => idtac
                    end. (* Finished transaction in 26.682 secs (26.652u,0.029s) (successful) *)
    1: idtac "exact eq_refl".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; exact eq_refl)
                    | _ => idtac
                    end. (* Finished transaction in 26.085 secs (26.024u,0.059s) (successful) *)
    1: idtac "refine (@eq_refl T x)".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; refine (@eq_refl T x))
                    | _ => idtac
                    end. (* Finished transaction in 13.641 secs (13.631u,0.009s) (successful) *)
    1: idtac "refine (@eq_refl T v)".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; refine (@eq_refl T v))
                    | _ => idtac
                    end. (* Finished transaction in 13.725 secs (13.694u,0.03s) (successful) *)
    1: idtac "instantiate (1:=v); reflexivity".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; instantiate (1:=v); reflexivity)
                    | _ => idtac
                    end. (* Finished transaction in 1.576 secs (1.526u,0.05s) (successful) *)
    1: idtac "instantiate (1:=v); refine eq_refl".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; instantiate (1:=v); refine eq_refl)
                    | _ => idtac
                    end. (*Finished transaction in 1.915 secs (1.884u,0.03s) (successful)*)
    1: idtac "instantiate (1:=v); refine (@eq_refl T v)".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; instantiate (1:=v); refine (@eq_refl T v))
                    | _ => idtac
                    end. (* Finished transaction in 1.588 secs (1.548u,0.04s) (successful) *)
    1: idtac "unify x v; reflexivity".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; unify x v; reflexivity)
                    | _ => idtac
                    end.
    1: idtac "unify x v; refine eq_refl".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; unify x v; refine eq_refl)
                    | _ => idtac
                    end.
    1: idtac "unify x v; refine (@eq_refl T v)".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; unify x v; refine (@eq_refl T v))
                    | _ => idtac
                    end.
    1: idtac "unify v x; reflexivity".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; unify v x; reflexivity)
                    | _ => idtac
                    end.
    1: idtac "unify v x; refine eq_refl".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; unify v x; refine eq_refl)
                    | _ => idtac
                    end.
    1: idtac "unify v x; refine (@eq_refl T v)".
    Time all: do 10 match goal with
                    | [ |- ?x = ?v :> ?T ]
                      => assert_succeeds (is_evar x; unify v x; refine (@eq_refl T v))
                    | _ => idtac
                    end.
HERE




                    time "refl" do 100 assert_succeeds reflexivity
    Time all: [ > refine eq_refl
                         .. | ].
    Show Ltac Profile.
    HERE
    (*Time unshelve (do 100 straightline); shelve_unifiable.*)
    Optimize Proof.

    repeat match goal with
           | [ H : Syntax.cmd.cmd |- _ ] => subst H
           end.
    Optimize Proof.
    Time idtac;  let s := match goal with |- WeakestPrecondition.cmd _ (Syntax.cmd.set ?s ?e) _ _ _ ?post => s end in
           unfold1_cmd_goal; (cbv beta match delta [cmd_body]);
                               let x := ident_of_string.ident_of_string s in
                               ensure_free x;
    lazymatch goal with
    | [ |- ex ?T ]
      => lazymatch T with
         | (fun y : ?A => and ?P ?Q)
           => notypeclasses refine (let x : A := _ in let P' : Prop := match x return Prop with y => P end in let Q' : Prop := match x return Prop with y => Q end in @ex_intro A (fun y : A => and P' Q') x (@conj P' Q' _ _))
         end
    end.
    letexists _ as x; split.
    (* NOTE: keep this consistent with the [exists _, _ /\ _] case far below *)
    letexists _ as x; split; [solve [repeat straightline]|].
    Show Ltac Profile.
    HERE
    Time repeat straightline_subst.
    HERE
    Time repeat straightline.
    Time unshelve (repeat (repeat straightline_subst; straightline_set'; [ shelve | intro_let ])); shelve_unifiable; [ .. | shelve ].
    Time all: straightline_unfold_expr.
    Time all: straightline_eexists_intro_split.
    Time all: try straightline_unfold_expr.
    Time all: try straightline_eexists_intro_split.
    Time all: try intro_let.
    Time all: do_refl.
    Unshelve.
    lazymatch goal with |- cmd _ _ _ _ _ ?postc => set (post := postc) end.
    repeat match goal with H : Syntax.cmd.cmd |- _ => subst H end.
    Time straightline_subst; straightline_set'; [ shelve | intro_let ].
    Time unshelve (repeat (repeat straightline_subst; straightline_set; [ shelve | intro_let ])); shelve_unifiable; [ .. | shelve ].
    Time all: straightline_unfold_expr.
    Time all: straightline_eexists_intro_split.
    Time all: try straightline_unfold_expr.
    Time all: try straightline_eexists_intro_split.
    Time all: try intro_let.
    Time all: do_refl.
    Unshelve.
    all: shelve_unifiable.
    1: straightline_unfold_expr; straightline_eexists_intro_split.
    1: do_refl.
    1: straightline_unfold_expr; intro_let.
    1: do_refl.
    subst post.

    cbv beta.
    (* prove [enforce] *)
    match goal with |- Markers.unique (Markers.left (exists x131 x132 x133 x134 x135 x136 x137 x138 x139 x140 x141 x142 x143 x144 x145 x146 x147 x148 x149 x150 x151, _)) => idtac end.

    repeat letexists. split.
    {
      cbv [enforce gather].
      Time repeat match goal with
                  | [ H : ?T |- _ ]
                    => lazymatch T with
                       | word.rep
                         => (let v := (eval cbv delta [H] in H) in
                             (tryif is_evar v then fail else clearbody H))
                       end
                  end.
      Time cbv.
      split; reflexivity. }

                             (*try revert H)
                       | _ => first [ clear H | revert H ]
                       end
                  end.

      Time intros.
      let e := open_constr:(_) in
      cut e.
      { Time repeat match goal with
                    | [ H : ?T |- _ ]
                      => lazymatch T with
                         | word.rep => clearbody H
                         end
                    end.
        intro H'.
        Time vm_compute.

      | _ => first [ clear H | revert H ]
        end
        end.
        Time intros.

        Time repeat match goal with H : word.rep |- _ => clearbody H end.
        repeat match goal with H : _ |- _ => clear H end.
        Time vm_compute.
        exact H'. }

      split; reflexivity.
      repeat match goal with
      | |- context G [@map.get ?K ?V ?M ?m ?k] =>
        time "all" (idtac; let v := match goal with H := context [map.put _ k ?v] |- _ => v end in
        let goal := context G [Some v] in
        time "change" change goal)
      end.
    cbv beta iota.
    split; refine eq_refl.
    }



    Time all: try do_refl.
    Unshelve.
    allg

    Time repeat straightline_subst; straightline_set; [ shelve | intro_let ].
    Time repeat straightline_subst; straightline_set; [ shelve | intro_let ].
    Time repeat straightline_subst; straightline_set; [ shelve | intro_let ].
    1:straightline_unfold_expr.
    1: straightline_eexists_intro_split.
    1: do_refl.
    1: straightline_unfold_expr.
    1: repeat intro_let.
    1: do_refl.₂
    repeat lazymatch goal with
             | [ |- cmd _ ?c _ _ _ _ ]
               => is_var c;
                  straightline_subst
             end; [].

    straightline_set; [ | intro_let ].
    step.
    1: straightline_eexists_intro_split.
    straightline_subst; [].
      straightline_set;
      [ | intro_let ].
    step.
    straightline_set.
    1: straightline_unfold_expr.
    1: straightline_eexists_intro_split.
    1: do_refl.
    1: straightline_unfold_expr.
    1: intro_let.
    1: do_refl.
    1: intro_let.

    1: intro_let.
      end.

    Set Ltac Profiling. Reset Ltac Profile.
    Time straightline_set. Show Ltac Profile.
    { match goal with
    | |- @dexpr _ _ _ _ _ _ _ _ => idtac
      end; cbv beta delta [dexpr].
      match goal with
      | |- @expr _ _ _ _ _ _ _ _ => idtac
      end; unfold1_expr_goal; (cbv beta match delta [expr_body]).
      match goal with
      | |- @expr _ _ _ _ _ _ _ _ => idtac
      end; unfold1_expr_goal; (cbv beta match delta [expr_body]).
      match goal with
      | |- @get _ _ _ _ _ _ => idtac
      end; (cbv beta delta [get]).
      (*repeat match goal with H : _ |- _ => clear H end.*)
      Time match goal with
           | |- @ex _ (fun x => and ?P ?Q) =>
               let x := fresh x in
               refine (let x := _ in @ex_intro _ (fun x => and P Q) x _); split
      end.
      Ltac print_context_size' base :=
        lazymatch goal with
        | [ H : _ |- _ ] => revert H; print_context_size' (S base)
        | _ => idtac "Context size:" base
        end.
      Ltac print_context_size := assert_succeeds (idtac; print_context_size' O).
      1: print_context_size; match goal with
      | |- @eq ?T1 (@map.get string (@word.rep _ _) _ _ _) (@Some ?T ?v) =>
          let v' := rdelta.rdelta v in
          is_evar v'; change v with v'; do 100 assert_succeeds (once time "slow" exact (@eq_refl _ _)); do 100 assert_succeeds (once time "fast" exact (@eq_refl T1 (@Some T v'))); exact (@eq_refl T1 (@Some T v')) end.
      match goal with
      | |- @expr _ _ _ _ _ _ _ _ => idtac
      end; unfold1_expr_goal; (cbv beta match delta [expr_body]).
      match goal with
      | |- @literal _ _ _ _ => idtac
      end; cbv beta delta [literal].
      Time match goal with
           | |- dlet x := ?v in
               ?P => change (let x := v in P)
           end; intros.
    match goal with
    | |- @eq ?T ?x ?y
      => let x := rdelta.rdelta x in
         is_evar x; change (@eq T x y);
         time exact (@eq_refl T y)
    end. }
    Time match goal with
           | |- dlet x := ?v in
               ?P => change (let x := v in P)
         end; intros.


    first
    [ (*let y := rdelta.rdelta y in
      is_evar y; change (@eq _ x y); exact (@eq_refl _ _)
    | *)let x := rdelta.rdelta x in
      is_evar x; change (@eq _ x y); exact (@eq_refl _ _) ].
    | let x := rdelta.rdelta x in
      let y := rdelta.rdelta y in
      constr_eq x y; exact (@eq_refl _ _) ].
      Print Ltac straightline_cleanup.
      Time match goal with
    | |- @dlet.dlet _ _ ?v (fun x => ?P) => change (let x := v in P)
    end; intros.
      repeat (straightline; match goal with |- dlet v := _ in _ => idtac end).
      Set Printing All.
      Print Ltac straightline_cleanup.
      Info 1 straightline.
      Info 1 straightline.
      Info 1 straightline.
          [ solve [ repeat straightline ] |  ]

    Time 1: solve [ repeat straightline ].
    all: [ >

    repeat match goal with
           | [ H : Syntax.cmd.cm

  |
  | let c := match goal with
             | |- @cmd _ _ _ _ _ _ _ ?c _ _ _ ?post => c
             end in
    let post := match goal with
                | |- @cmd _ _ _ _ _ _ _ ?c _ _ _ ?post => post
                end in
    let c := eval hnf in c in
    lazymatch c with
    | Syntax.cmd.while _ _ => fail
    | Syntax.cmd.cond _ _ _ => fail
    | Syntax.cmd.interact _ _ _ => fail
    | _ => idtac
    end; unfold1_cmd_goal; cbv beta match delta [cmd_body]
  | match goal with
    | |- @list_map _ _ (@get _ _ _ _) _ _ => idtac
    end; unfold1_list_map_goal; cbv beta match delta [list_map_body]
  | match goal with
    | |- @list_map _ _ (@expr _ _ _ _ _ _) _ _ => idtac
    end; unfold1_list_map_goal; cbv beta match delta [list_map_body]
  | match goal with
    | |- @list_map _ _ _ (@nil _) _ => idtac
    end; cbv beta match fix delta [list_map list_map_body]
  | match goal with
    | |- @expr _ _ _ _ _ _ _ _ => idtac
    end; unfold1_expr_goal; cbv beta match delta [expr_body]
  | match goal with
    | |- @dexpr _ _ _ _ _ _ _ _ => idtac
    end; cbv beta delta [dexpr]
  | match goal with
    | |- @dexprs _ _ _ _ _ _ _ _ => idtac
    end; cbv beta delta [dexprs]
  | match goal with
    | |- @literal _ _ _ _ => idtac
    end; cbv beta delta [literal]
  | match goal with
    | |- @get _ _ _ _ _ _ => idtac
    end; cbv beta delta [get]
  | match goal with
    | |- @load _ _ _ _ _ _ _ => idtac
    end; cbv beta delta [load]
  | match goal with
    | |- @enforce ?width ?word ?locals ?names ?values ?map =>
          let values := eval compute in values in
          change (@enforce width word locals names values map); exact
           (@conj _ _ (@eq_refl _ values) (@eq_refl _ _))
    end
  | match goal with
    | |- @eq (@map.rep string (@word.rep _ _) _) _ _ => idtac
    end; eapply (@SortedList.eq_value _ _ _); exact (@eq_refl _ _)
  | match goal with
    | |- @eq _ (@map.get string (@word.rep _ _) ?M ?m ?k) (@Some _ ?e') =>
          let e := rdelta.rdelta e' in
          is_evar e;
           once
            (let v :=
              multimatch goal with
              | x:=context [ @map.put _ _ M _ k ?v ]:_ (* XXX TODO Report Print Ltac bug *) |- _ => v
              end
             in
             unify e v; exact (@eq_refl _ (@Some _ v)))
    end
  | let v :=
     match goal with
     | |- @eq _ (@map.get string (@word.rep _ _) _ _ _) (@Some _ ?v) => v
     end
    in
    let v' := rdelta.rdelta v in
    is_evar v'; change v with v'; exact (@eq_refl _ _)
  | let x := match goal with
             | |- @eq _ ?x ?y => x
             end in
    let y := match goal with
             | |- @eq _ ?x ?y => y
             end in
    first
    [ let y := rdelta.rdelta y in
      is_evar y; change (@eq _ x y); exact (@eq_refl _ _)
    | let x := rdelta.rdelta x in
      is_evar x; change (@eq _ x y); exact (@eq_refl _ _)
    | let x := rdelta.rdelta x in
      let y := rdelta.rdelta y in
      constr_eq x y; exact (@eq_refl _ _) ]
  | match goal with
    | |- @store _ _ _ Syntax.access_size.one _ _ _ _ => idtac
    end; eapply (@store_one_of_sep _ _ _ _ _); [ solve [ ecancel_assumption ] |  ]
  | match goal with
    | |- @store _ _ _ Syntax.access_size.two _ _ _ _ => idtac
    end; eapply (@store_two_of_sep _ _ _ _ _); [ solve [ ecancel_assumption ] |  ]
  | match goal with
    | |- @store _ _ _ Syntax.access_size.four _ _ _ _ => idtac
    end; eapply (@store_four_of_sep _ _ _ _ _); [ solve [ ecancel_assumption ] |  ]
  | match goal with
    | |- @store _ _ _ Syntax.access_size.word _ _ _ _ => idtac
    end; eapply (@store_word_of_sep _ _ _ _ _); [ solve [ ecancel_assumption ] |  ]
  | let ev :=
     match goal with
     | |- @eq _ (@Memory.load _ _ _ Syntax.access_size.one ?m ?a) (@Some _ ?ev) =>
           ev
     end
    in
    try subst ev; refine (@load_one_of_sep _ _ _ _ _ _ _ _ _ _); ecancel_assumption
  | match goal with
    | |-
      @eq _ (@Memory.load _ ?word ?mem Syntax.access_size.two ?m ?a) (@Some _ ?ev)
      =>
          try subst ev; refine (@load_two_of_sep _ word _ mem _ a _ _ m _);
           ecancel_assumption
    end
  | match goal with
    | |-
      @eq _ (@Memory.load _ ?word ?mem Syntax.access_size.four ?m ?a) (@Some _ ?ev)
      =>
          try subst ev; refine
           (@load_four_of_sep_32bit _ word _ mem _ (@eq_refl _ _) a _ _ m _);
           ecancel_assumption
    end
  | match goal with
    | |-
      @eq _ (@Memory.load _ ?word ?mem Syntax.access_size.four ?m ?a) (@Some _ ?ev)
      =>
          try subst ev; refine (@load_four_of_sep _ word _ mem _ a _ _ m _);
           ecancel_assumption
    end
  | match goal with
    | |-
      @eq _ (@Memory.load _ ?word ?mem Syntax.access_size.word ?m ?a) (@Some _ ?ev)
      =>
          try subst ev; refine (@load_word_of_sep _ word _ mem _ a _ _ m _);
           ecancel_assumption
    end
  | match goal with
    | |-
      @ex _ (fun l' => and (@eq _ (@map.of_list_zip _ _ _ ?ks ?vs) (@Some _ l')) _)
      => idtac
    end; letexists; split; [ exact (@eq_refl _ _) |  ]
  | match goal with
    | |-
      @ex _
        (fun l' =>
         and (@eq _ (@map.putmany_of_list_zip _ _ _ ?ks ?vs ?l) (@Some _ l')) _) =>
          idtac
    end; letexists; split; [ exact (@eq_refl _ _) |  ]
  | match goal with
    | |- @ex _ (fun x => and ?P ?Q) =>
          let x := fresh x in
          refine (let x := _ in @ex_intro _ (fun x => and P Q) x _); split;
           [ solve [ repeat straightline ] |  ]
    | |- @ex _ (fun x => @Markers.split _ (and ?P ?Q)) =>
          let x := fresh x in
          refine (let x := _ in @ex_intro _ (fun x => and P Q) x _); split;
           [ solve [ repeat straightline ] |  ]
    | |- @Markers.unique _ (@ex _ (fun x => @Markers.split _ (and ?P ?Q))) =>
          let x := fresh x in
          refine (let x := _ in @ex_intro _ (fun x => and P Q) x _); split;
           [ solve [ repeat straightline ] |  ]
    end
  | let G := match goal with
             | |- @Markers.unique _ (@Markers.left _ ?G) => G
             end in
    change G; unshelve
     (idtac;
       repeat
        match goal with
        | |- @Markers.split _ (and ?P (@Markers.right _ ?Q)) =>
              split; [ eabstract repeat straightline | change Q ]
        | |- @ex _ (fun _ => _) => letexists
        end); [  ]
  | let G := match goal with
             | |- @Markers.split _ ?G => G
             end in
    change G; split
  | match goal with
    | |- True => idtac
    end; exact I
  | match goal with
    | |- or False _ => idtac
    end; right
  | match goal with
    | |- or _ False => idtac
    end; left
  | let z :=
     match goal with
     | |- and (@eq _ (Z.modulo ?z (bytes_per_word _)) Z0) _ => z
     end
    in
    lazymatch isZcst z with
    | true => idtac
    end; split; [ exact (@eq_refl _ _) |  ]
  | straightline_stackalloc
  | straightline_stackdealloc ].

    Set Printing All.
    Print Ltac straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    repeat (straightline; []).
    straightline.
    do 5 straightline.
    straightline.
    straightline.
    do 100 straightline.
    2: solve [intuition].
    straightline.
    straightline.
    straightline.
    straightline.
    do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.
    Time straightline.

    (* prove [enforce] *)
    match goal with |- Markers.unique (Markers.left (exists x131 x132 x133 x134 x135 x136 x137 x138 x139 x140 x141 x142 x143 x144 x145 x146 x147 x148 x149 x150 x151, _)) => idtac end.

    repeat letexists. split.
    {
      cbv [enforce gather].
      repeat match goal with
      | |- context G [@map.get ?K ?V ?M ?m ?k] =>
        let v := match goal with H := context [map.put _ k ?v] |- _ => v end in
        let goal := context G [Some v] in
        change goal
      end.
    cbv beta iota.
    split; refine eq_refl.
    }

    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time do 10 straightline.
    Time straightline.
    Time straightline.
    Time straightline.

    letexists. split.
    2:split.
    1: split.
    2: split.

    all : repeat straightline.
    all : try typeclasses eauto with core.

    {
      lazymatch goal with
      | [ H : word.unsigned br <> 0 |- _ ] =>
        subst br;
          rewrite word.unsigned_ltu in H;
          lazymatch type of H with
          | word.unsigned (if ?x <? ?y then _ else _) <> _ =>
            destruct (Z.ltb_spec0 x y) as [Hv |];
              rewrite word.unsigned_of_Z in H;
              cbv in H;
              [| congruence]
          end
      end.
      subst x131.
      subst v'.
      match goal with
      | [ |- word.unsigned ?w = _ ] =>
        change w with (word.add x (word.of_Z 1))
      end.
      rewrite word.unsigned_add, word.unsigned_of_Z.
      match goal with
      | [ H : word.unsigned _ = 10 - _ |- _ ] =>
        rewrite H in *
      end.
      rewrite word.unsigned_of_Z in Hv.
      change (word.wrap 10) with 10 in Hv.
      instantiate (1 := Nat.pred v).
      rewrite Nat2Z.inj_pred; [| blia].
      change (word.wrap 1) with 1.
      cbv [word.wrap].
      rewrite Z.mod_small; [blia |].
      split; [blia |].
      match goal with
      | [ H : (_ <= _)%nat |- _ ] =>
        let H' := fresh "H" in
        pose proof (inj_le _ _ H) as H'; cbn in H'
      end.
      match goal with
      | [ |- _ < 2^?w ] =>
          let w' := eval cbv in w in
          change w with w'
      end.
      blia.
    }
    { subst v'. blia. }
    { subst v'.
      lazymatch goal with
      | [ H : word.unsigned br <> 0 |- _ ] =>
        subst br;
          rewrite word.unsigned_ltu in H;
          lazymatch type of H with
          | word.unsigned (if ?x <? ?y then _ else _) <> _ =>
            destruct (Z.ltb_spec0 x y) as [Hv |];
              rewrite word.unsigned_of_Z in H;
              cbv in H;
              [| congruence]
          end
      end.
      match goal with
      | [ H : word.unsigned _ = 10 - _ |- _ ] =>
        rewrite H in *
      end.
      rewrite word.unsigned_of_Z in Hv.
      change (word.wrap 10) with 10 in Hv.
      apply lt_pred_n_n.
      apply Nat2Z.inj_lt.
      blia.
    }
  }

  subst Hsep.
  repeat straightline.
  replace (scalar32 x47 r) with (scalar32 (word.add x47 (word.of_Z 0)) r) in H8.
  2: {
    f_equal.
    1: {
      intros.
      rewrite H9.
      reflexivity.
    }
    ring.
  }
  repeat straightline.
  intuition.
  destruct out; cbn in H0; [| blia].
  cbn [array] in H19.
  let x := open_constr:(@cons word32 _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ (cons _ nil)))))))))))))))) in
  unify out' x.
  subst out'.
  cbn [array].
  repeat match goal with
  | [ |- context[@word.add _ ?w (word.add x47 ?x) ?y] ] =>
    replace (@word.add _ w (word.add x47 x) y) with (@word.add _ w x47 (word.add x y)) by ring
  end.
  repeat match goal with
  | [ |- context[@word.add _ ?w (word.add x16 ?x) ?y] ] =>
    replace (@word.add _ w (word.add x16 x) y) with (@word.add _ w x16 (word.add x y)) by ring
  end.
  repeat match goal with
  | [ |- context[@word.add _ ?w (word.add x17 ?x) ?y] ] =>
    replace (@word.add _ w (word.add x17 x) y) with (@word.add _ w x17 (word.add x y)) by ring
  end.
  repeat match goal with
         | [ |- context[@word.add _ ?w (word.of_Z ?x) (word.of_Z ?y)] ] =>
           let z := eval cbv in (x + y) in
               change (@word.add _ w (word.of_Z x) (word.of_Z y)) with (@word.of_Z _ w z)
         end.
  rewrite !word.of_Z_unsigned in H19.
  repeat match type of H19 with
         | context[scalar32 ?a _] =>
           subst a
         end.
  replace (word.add x47 (word.of_Z 0)) with x47 in H19 by ring.
  ecancel_assumption.
Defined.
