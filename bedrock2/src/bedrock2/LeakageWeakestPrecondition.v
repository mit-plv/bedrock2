Require Import coqutil.Macros.subst coqutil.Macros.unique coqutil.Map.Interface coqutil.Map.OfListWord.
Require Import Coq.ZArith.BinIntDef coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.dlet bedrock2.Syntax bedrock2.Semantics bedrock2.LeakageSemantics.
Require Import Coq.Lists.List.

Section WeakestPrecondition.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec} {pick_sp: PickSp}.
  Implicit Types (k : leakage) (t : trace) (m : mem) (l : locals).

  Definition literal v (post : word -> Prop) : Prop :=
    dlet! v := word.of_Z v in post v.
  Definition get (l : locals) (x : String.string) (post : word -> Prop) : Prop :=
    exists v, map.get l x = Some v /\ post v.
  Definition load s m a (post : _ -> Prop) : Prop :=
    exists v, load s m a = Some v /\ post v.
  Definition store sz m a v post :=
    exists m', store sz m a v = Some m' /\ post m'.

  Section WithMemAndLocals.
    Context (m : mem) (l : locals).
    Definition expr_body rec (k : leakage) (e : Syntax.expr) (post : leakage -> word -> Prop) : Prop :=
      match e with
      | expr.literal v =>
        literal v (post k)
      | expr.var x =>
        get l x (post k)
      | expr.op op e1 e2 =>
        rec k e1 (fun k' v1 =>
        rec k' e2 (fun k'' v2 =>
        post (leak_binop op v1 v2 ++ k'') (interp_binop op v1 v2)))
      | expr.load s e =>
        rec k e (fun k' a =>
        load s m a (post (leak_word a :: k')))
      | expr.inlinetable s t e =>
        rec k e (fun k' a =>
        load s (map.of_list_word t) a (post (leak_word a :: k')))
      | expr.ite c e1 e2 =>
        rec k c (fun k' b =>
        let b := word.eqb b (word.of_Z 0) in
        rec (leak_bool (negb b) :: k') (if b then e2 else e1) post)
    end.
    Fixpoint expr k e := expr_body expr k e.
  End WithMemAndLocals.

  Section WithF.
    Context {A B} (f: A -> (B -> Prop) -> Prop).
    Definition list_map_body rec (xs : list A) (post : list B -> Prop) : Prop :=
      match xs with
      | nil => post nil
      | cons x xs' =>
        f x (fun y =>
        rec xs' (fun ys' =>
        post (cons y ys')))
      end.
    Fixpoint list_map xs := list_map_body list_map xs.
  End WithF.

  Section WithF'.
    Context {A B T} (f: T -> A -> (T -> B -> Prop) -> Prop).
    Definition list_map'_body rec (acc : T) (xs : list A) (post : T -> list B -> Prop) : Prop :=
      match xs with
      | nil => post acc nil
      | cons x xs' =>
        f acc x (fun acc' y =>
        rec acc' xs' (fun acc'' ys' =>
        post acc'' (cons y ys')))
      end.
    Fixpoint list_map' acc xs := list_map'_body list_map' acc xs.
  End WithF'.

  Section WithFunctions.
    Context (e: env).
    Definition dexpr m l k e v k' := expr m l k e (fun k'2 v2 => eq k' k'2 /\ eq v v2).
    Definition dexprs m l k es vs k' := list_map' (expr m l) k es (fun k'2 vs2 => eq k' k'2 /\ eq vs vs2).
    (* All cases except cmd.while and cmd.call can be denoted by structural recursion
       over the syntax.
       For cmd.while and cmd.call, we fall back to the operational semantics *)
    Definition cmd_body (rec:_->_->_->_->_->_->Prop) (c : cmd) (k : leakage) (t : trace) (m : mem) (l : locals)
             (post : leakage -> trace -> mem -> locals -> Prop) : Prop :=
      (* give value of each pure expression when stating its subproof *)
      match c with
      | cmd.skip => post k t m l
      | cmd.set x ev =>
        exists v k', dexpr m l k ev v k' /\
        dlet! l := map.put l x v in
        post k' t m l
      | cmd.unset x =>
        dlet! l := map.remove l x in
        post k t m l
      | cmd.store sz ea ev =>
        exists a k', dexpr m l k ea a k' /\
        exists v k'', dexpr m l k' ev v k'' /\
        store sz m a v (fun m =>
        post (leak_word a :: k'') t m l)
      | cmd.stackalloc x n c =>
        Z.modulo n (bytes_per_word width) = 0 /\
        forall mStack mCombined,
          let a := pick_sp k in
          anybytes a n mStack -> map.split mCombined m mStack ->
          dlet! l := map.put l x a in
          rec c (leak_unit :: k) t mCombined l (fun k' t' mCombined' l' =>
          exists m' mStack',
          anybytes a n mStack' /\ map.split mCombined' m' mStack' /\
          post k' t' m' l')
      | cmd.cond br ct cf =>
        exists v k', dexpr m l k br v k' /\
        (word.unsigned v <> 0%Z -> rec ct (leak_bool true :: k') t m l post) /\
        (word.unsigned v = 0%Z -> rec cf (leak_bool false :: k') t m l post)
      | cmd.seq c1 c2 =>
        rec c1 k t m l (fun k t m l => rec c2 k t m l post)
      | cmd.while _ _ => LeakageSemantics.exec e c k t m l post
      | cmd.call binds fname arges =>
        exists args k', dexprs m l k arges args k' /\
        LeakageSemantics.call e fname (leak_unit :: k') t m args (fun k'' t m rets =>
          exists l', map.putmany_of_list_zip binds rets l = Some l' /\
          post k'' t m l')
      | cmd.interact binds action arges =>
        exists args k', dexprs m l k arges args k' /\
        exists mKeep mGive, map.split m mKeep mGive /\
        ext_spec t mGive action args (fun mReceive rets klist =>
          exists l', map.putmany_of_list_zip binds rets l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post (leak_list klist :: k') (cons ((mGive, action, args), (mReceive, rets)) t) m' l')
      end.
    Fixpoint cmd c := cmd_body cmd c.
  End WithFunctions.

  Definition func call '(innames, outnames, c) (k : leakage) (t : trace) (m : mem) (args : list word) (post : leakage -> trace -> mem -> list word -> Prop) :=
      exists l, map.of_list_zip innames args = Some l /\
      cmd call c k t m l (fun k t m l =>
        list_map (get l) outnames (fun rets =>
        post k t m rets)).

  Definition program := cmd.
End WeakestPrecondition.
Notation call := LeakageSemantics.call (only parsing).

Ltac unfold1_cmd e :=
  lazymatch e with
    @cmd ?width ?BW ?word ?mem ?locals ?ext_spec ?pick_sp ?CA ?c ?k ?t ?m ?l ?post =>
    let c := eval hnf in c in
    constr:(@cmd_body width BW word mem locals ext_spec pick_sp CA
                      (@cmd width BW word mem locals ext_spec pick_sp CA) c k t m l post)
  end.
Ltac unfold1_cmd_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_cmd G in
  change G.

Ltac unfold1_expr e :=
  lazymatch e with
    @expr ?width ?BW ?word ?mem ?locals ?m ?l ?k ?arg ?post =>
    let arg := eval hnf in arg in
    constr:(@expr_body width BW word mem locals m l (@expr width BW word mem locals m l) k arg post)
  end.
Ltac unfold1_expr_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_expr G in
  change G.

Ltac unfold1_list_map e :=
  lazymatch e with
    @list_map ?A ?B ?P ?arg ?post =>
    let arg := eval hnf in arg in
    constr:(@list_map_body A B P (@list_map A B P) arg post)
  end.
Ltac unfold1_list_map_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_list_map G in
  change G.

Ltac unfold1_list_map' e :=
  lazymatch e with
    @list_map' ?A ?B ?T ?P ?t ?arg ?post =>
    let arg := eval hnf in arg in
    constr:(@list_map'_body A B T P (@list_map' A B T P) t arg post)
  end.
Ltac unfold1_list_map'_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_list_map' G in
  change G.

Import Coq.ZArith.ZArith.

Notation "'fnspec!' name a0 .. an '/' g0 .. gn '~>' r0 .. rn ',' '{' 'requires' k tr mem := pre ';' 'ensures' k' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
              (forall g0,
                  .. (forall gn,
                         (forall k tr mem,
                             pre ->
                             LeakageWeakestPrecondition.call
                               functions name k tr mem (cons a0 .. (cons an nil) ..)
                               (fun k' tr' mem' rets =>
                                  (exists r0,
                                      .. (exists rn,
                                             rets = (cons r0 .. (cons rn nil) ..) /\
                                             post) ..)))) ..)) ..))
    (at level 200,
     name at level 0,
     a0 binder, an binder,
     g0 binder, gn binder,
     r0 closed binder, rn closed binder,
     k name, k' name, tr name, tr' name, mem name, mem' name,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name a0 .. an '/' g0 .. gn ',' '{' 'requires' k tr mem := pre ';' 'ensures' k' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
              (forall g0,
                  .. (forall gn,
                         (forall k tr mem,
                             pre ->
                             LeakageWeakestPrecondition.call
                               functions name k tr mem (cons a0 .. (cons an nil) ..)
                               (fun k' tr' mem' rets =>
                                  rets = nil /\ post))) ..)) ..))
    (at level 200,
     name at level 0,
     a0 binder, an binder,
     g0 binder, gn binder,
     k name, k' name, tr name, tr' name, mem name, mem' name,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name a0 .. an '~>' r0 .. rn ',' '{' 'requires' k tr mem := pre ';' 'ensures' k' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
               (forall k tr mem,
                   pre ->
                   LeakageWeakestPrecondition.call
                     functions name k tr mem (cons a0 .. (cons an nil) ..)
                     (fun k' tr' mem' rets =>
                        (exists r0,
                            .. (exists rn,
                                   rets = (cons r0 .. (cons rn nil) ..) /\
                                   post) ..)))) ..))
    (at level 200,
     name at level 0,
     a0 binder, an binder,
     r0 closed binder, rn closed binder,
     k name, k' name, tr name, tr' name, mem name, mem' name,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name '/' g0 .. gn '~>' r0 .. rn ',' '{' 'requires' k tr mem := pre ';' 'ensures' k' tr' mem' ':=' post '}'" :=
  (fun functions =>
        (forall an,
              (forall g0,
                  .. (forall gn,
                         (forall k tr mem,
                             pre ->
                             LeakageWeakestPrecondition.call
                               functions name k tr mem nil
                               (fun k' tr' mem' rets =>
                                  (exists r0,
                                      .. (exists rn,
                                             rets = (cons r0 .. (cons rn nil) ..) /\
                                             post) ..)))) ..)))
    (at level 200,
     name at level 0,
     g0 binder, gn binder,
     r0 closed binder, rn closed binder,
     k name, k' name, tr name, tr' name, mem name, mem' name,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name a0 .. an ',' '{' 'requires' k tr mem := pre ';' 'ensures' k' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
               (forall k tr mem,
                   pre ->
                   LeakageWeakestPrecondition.call
                     functions name k tr mem (cons a0 .. (cons an nil) ..)
                     (fun k' tr' mem' rets =>
                        rets = nil /\ post))) ..))
    (at level 200,
     name at level 0,
     a0 binder, an binder,
     k name, k' name, tr name, tr' name, mem name, mem' name,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name '/' g0 .. gn ',' '{' 'requires' k tr mem := pre ';' 'ensures' k' tr' mem' ':=' post '}'" :=
  (fun functions =>
              (forall g0,
                  .. (forall gn,
                         (forall k tr mem,
                             pre ->
                             LeakageWeakestPrecondition.call
                               functions name k tr mem nil
                               (fun k' tr' mem' rets =>
                                  rets = nil /\ post))) ..))
    (at level 200,
     name at level 0,
     g0 binder, gn binder,
     k name, k' name, tr name, tr' name, mem name, mem' name,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name '~>' r0 .. rn ',' '{' 'requires' k tr mem := pre ';' 'ensures' k' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall k tr mem,
         pre ->
         LeakageWeakestPrecondition.call
           functions name k tr mem nil
           (fun k' tr' mem' rets =>
              (exists r0,
                  .. (exists rn,
                         rets = (cons r0 .. (cons rn nil) ..) /\
                         post) ..))))
    (at level 200,
     name at level 0,
     r0 closed binder, rn closed binder,
     k name, k' name, tr name, tr' name, mem name, mem' name,
     pre at level 200,
     post at level 200).

(*with existent function(s)*)

Notation "'fnspec!' 'exists' f0 .. fn ',' name a0 .. an '/' g0 .. gn '~>' r0 .. rn ',' '{' 'requires' k tr mem := pre ';' 'ensures' k' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (exists f0,
         .. (exists fn,
               (forall a0,
                   .. (forall an,
                         (forall g0,
                             .. (forall gn,
                                   (forall k tr mem,
                                       pre ->
                                       LeakageWeakestPrecondition.call
                                         functions name k tr mem (cons a0 .. (cons an nil) ..)
                                         (fun k' tr' mem' rets =>
                                            (exists r0,
                                                .. (exists rn,
                                                      rets = (cons r0 .. (cons rn nil) ..) /\
                                                        post) ..)))) ..)) ..)) ..))
    (at level 200,
      name at level 0,
      f0 binder, fn binder,
      a0 binder, an binder,
      g0 binder, gn binder,
      r0 closed binder, rn closed binder,
      k name, k' name, tr name, tr' name, mem name, mem' name,
      pre at level 200,
      post at level 200).

Notation "'fnspec!' 'exists' f0 .. fn ',' name a0 .. an '/' g0 .. gn ',' '{' 'requires' k tr mem := pre ';' 'ensures' k' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (exists f0,
         .. (exists fn,
               (forall a0,
                   .. (forall an,
                         (forall g0,
                             .. (forall gn,
                                   (forall k tr mem,
                                       pre ->
                                       LeakageWeakestPrecondition.call
                                         functions name k tr mem (cons a0 .. (cons an nil) ..)
                                         (fun k' tr' mem' rets =>
                                            rets = nil /\ post))) ..)) ..)) ..))
    (at level 200,
      name at level 0,
      f0 binder, fn binder,
      a0 binder, an binder,
      g0 binder, gn binder,
      k name, k' name, tr name, tr' name, mem name, mem' name,
      pre at level 200,
      post at level 200).

Notation "'fnspec!' 'exists' f0 .. fn ',' name a0 .. an '~>' r0 .. rn ',' '{' 'requires' k tr mem := pre ';' 'ensures' k' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (exists f0,
         .. (exists fn,
               (forall a0,
                   .. (forall an,
                         (forall k tr mem,
                             pre ->
                             LeakageWeakestPrecondition.call
                               functions name k tr mem (cons a0 .. (cons an nil) ..)
                               (fun k' tr' mem' rets =>
                                  (exists r0,
                                      .. (exists rn,
                                            rets = (cons r0 .. (cons rn nil) ..) /\
                                              post) ..)))) ..)) ..))
    (at level 200,
      name at level 0,
      f0 binder, fn binder,
      a0 binder, an binder,
      r0 closed binder, rn closed binder,
      k name, k' name, tr name, tr' name, mem name, mem' name,
      pre at level 200,
      post at level 200).

Notation "'fnspec!' 'exists' f0 .. fn ',' name '/' g0 .. gn '~>' r0 .. rn ',' '{' 'requires' k tr mem := pre ';' 'ensures' k' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (exists f0,
         .. (exists fn,
               (forall an,
                   (forall g0,
                       .. (forall gn,
                             (forall k tr mem,
                                 pre ->
                                 LeakageWeakestPrecondition.call
                                   functions name k tr mem nil
                                   (fun k' tr' mem' rets =>
                                      (exists r0,
                                          .. (exists rn,
                                                rets = (cons r0 .. (cons rn nil) ..) /\
                                                  post) ..)))) ..))) ..))
    (at level 200,
      name at level 0,
      f0 binder, fn binder,
      g0 binder, gn binder,
      r0 closed binder, rn closed binder,
      k name, k' name, tr name, tr' name, mem name, mem' name,
      pre at level 200,
      post at level 200).

Notation "'fnspec!' 'exists' f0 .. fn ',' name a0 .. an ',' '{' 'requires' k tr mem := pre ';' 'ensures' k' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (exists f0,
         .. (exists fn,
               (forall a0,
                   .. (forall an,
                         (forall k tr mem,
                             pre ->
                             LeakageWeakestPrecondition.call
                               functions name k tr mem (cons a0 .. (cons an nil) ..)
                               (fun k' tr' mem' rets =>
                                  rets = nil /\ post))) ..)) ..))
    (at level 200,
      name at level 0,
      f0 binder, fn binder,
      a0 binder, an binder,
      k name, k' name, tr name, tr' name, mem name, mem' name,
      pre at level 200,
      post at level 200).

Notation "'fnspec!' 'exists' f0 .. fn ',' name '/' g0 .. gn ',' '{' 'requires' k tr mem := pre ';' 'ensures' k' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (exists f0,
         .. (exists fn,
               (forall g0,
                   .. (forall gn,
                         (forall k tr mem,
                             pre ->
                             LeakageWeakestPrecondition.call
                               functions name k tr mem nil
                               (fun k' tr' mem' rets =>
                                  rets = nil /\ post))) ..)) ..))
    (at level 200,
      name at level 0,
      f0 binder, fn binder,
      g0 binder, gn binder,
      k name, k' name, tr name, tr' name, mem name, mem' name,
      pre at level 200,
      post at level 200).

Notation "'fnspec!' 'exists' f0 .. fn ',' name '~>' r0 .. rn ',' '{' 'requires' k tr mem := pre ';' 'ensures' k' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (exists f0,
         .. (exists fn,
               (forall k tr mem,
                   pre ->
                   LeakageWeakestPrecondition.call
                     functions name k tr mem nil
                     (fun k' tr' mem' rets =>
                        (exists r0,
                            .. (exists rn,
                                  rets = (cons r0 .. (cons rn nil) ..) /\
                                    post) ..)))) ..))
    (at level 200,
      name at level 0,
      f0 binder, fn binder,
      r0 closed binder, rn closed binder,
      k name, k' name, tr name, tr' name, mem name, mem' name,
      pre at level 200,
      post at level 200).
