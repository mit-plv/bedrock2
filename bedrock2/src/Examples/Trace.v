Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Z.HexNotation.
Require Import bedrock2.ListPred. Import ListPredNotations.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsInConstr.

(* TODO distribute contents of this file into the right places *)

Module IOMacros.

  Class Interface := {
    semantics_params :> Semantics.parameters;

    (* macros to be inlined to read or write a word
       TODO it's not so nice that we need to foresee the number of temp vars
       each implementation might need *)
    read_word_code(x tmp: varname): cmd;
    write_word_code(x tmp: varname): cmd;

    (* means "this trace does nothing else than reading the given word", could require
       several events if we're polling until a word is available *)
    read_word_trace: word -> trace -> Prop;
    (* means "this trace does nothing else than outputting the given word", could require
       several events if we have to poll a "ready to accept next word" flag before writing *)
    write_word_trace: word -> trace -> Prop;

    (* the IOMacros module is allowed to reserve part of the address space,
       eg for MMIO, or to communicate with the kernel *)
    is_reserved_addr: word -> Prop;

    read_word_correct: forall t m l x tmp,
        (forall a, is_reserved_addr a -> map.get m a = None) ->
        exec map.empty (read_word_code x tmp) t m l (fun t' m' l' =>
          m = m' /\ exists t'' v, t' = t ++ t'' /\ read_word_trace v t'' /\ l' = map.put l x v);

    write_word_correct: forall t m l x tmp v,
        (forall a, is_reserved_addr a -> map.get m a = None) ->
        map.get l x = Some v ->
        exec map.empty (write_word_code x tmp) t m l (fun t' m' l' =>
          m = m' /\ exists t'', t' = t ++ t'' /\ write_word_trace v t'' /\ l' = l);
  }.

End IOMacros.

Section Squarer.

  Context {ioLib: IOMacros.Interface}.

  Definition squarer_trace: trace -> Prop :=
    kleene (existsl (fun inp => IOMacros.read_word_trace inp +++
                                IOMacros.write_word_trace (word.mul inp inp))).

  Definition squarer: cmd. Admitted.

  Lemma squarer_correct: forall (m: mem) (l: locals),
      exec map.empty squarer nil m l (fun t' m' l' => squarer_trace t').
  Admitted.

End Squarer.


(* TODO: on which side of the list do we add new events? *)

Module SpiEth.

  Inductive MMIOAction := MMInput | MMOutput.

  Section WithMem.
    Context {byte: word.word 8} {word: word.word 32} {mem: map.map word byte}.

    Definition Event: Type := (mem * MMIOAction * list word) * (mem * list word).

    Definition msb_set(x: word): Prop :=
      word.and x (word.slu (word.of_Z 1) (word.of_Z 31)) <> word.of_Z 0.

    Definition lo_byte(x: word): word :=
      word.and x (word.of_Z 255).

    Definition spi_rx     : Z := Ox"1002404c".
    Definition spi_tx_fifo: Z := Ox"10024048".
    Definition spi_pinmux : Z := Ox"10012038".
    Definition spi_sckdiv : Z := Ox"10024000".
    Definition spi_csmode : Z := Ox"10024018".

    (* TODO should this be so specific or should it be the whole range? *)
    Definition isMMIOAddr(a: word): Prop :=
      a = word.of_Z spi_rx      \/
      a = word.of_Z spi_tx_fifo \/
      a = word.of_Z spi_pinmux  \/
      a = word.of_Z spi_sckdiv  \/
      a = word.of_Z spi_csmode  .

    (*  // Reads one byte over SPI and returns
        static inline w spi_read() {
            w x = -1;
            while (x & (1 << 31)) { x = MMIO(0x1002404c); } // spi rx
            return x&0xff;
        }
    TODO would there be any benefit in using kleene for this? If so, how to do it? *)
    Inductive read_byte: word -> list Event -> Prop :=
    | read_byte_go: forall x m,
        ~ msb_set x ->
        read_byte (lo_byte x) [((m, MMInput, [word.of_Z spi_rx]), (m, [x]))]
    | read_byte_wait: forall x y m rest,
        msb_set x ->
        read_byte y rest ->
        read_byte y (((m, MMInput, [word.of_Z spi_rx]), (m, [x])) :: rest).

    (*  // Requires b < 256
        static inline void spi_write(w b) {
            while (MMIO(0x10024048) & (1 << 31)) {} // high order bit set means fifo is full
            MMIO(0x10024048) = b; // spi tx fifo
        }
    *)
    Inductive write_byte: word -> list Event -> Prop :=
    | write_byte_go: forall x b m,
        ~ msb_set x ->
        0 <= b < 256 ->
        write_byte (word.of_Z b) [((m, MMInput, [word.of_Z spi_tx_fifo]), (m, [x]));
                                  ((m, MMOutput, [word.of_Z spi_tx_fifo; word.of_Z b]), (m, []))]
    | write_byte_wait: forall x b m rest,
        msb_set x ->
        write_byte b rest ->
        write_byte b (((m, MMInput, [word.of_Z spi_tx_fifo]), (m, [x])) :: rest).


    Instance syntax_params: Syntax.parameters := {|
      Syntax.varname := string;
      Syntax.funname := Empty_set;
      Syntax.actname := MMIOAction;
    |}.

    Context {locals: map.map varname word}.
    Context {funname_env: forall T, map.map funname T}.

    Instance semantics_params: Semantics.parameters := {|
      Semantics.syntax := syntax_params;
      Semantics.width := 32;
      Semantics.word := word;
      Semantics.byte := byte;
      Semantics.mem := mem;
      Semantics.funname_eqb f1 f2 := Empty_set_rect (fun _ : Empty_set => bool) f1;
      Semantics.ext_spec t m action (argvals: list word) (post: (mem -> list word -> Prop)) :=
        match argvals with
        | addr :: _ =>
          isMMIOAddr addr /\
          Memory.load access_size.four m addr = None /\
          match action with
          | MMInput => argvals = [addr] /\ forall val, post m [val]
          | MMOutput => exists val, argvals = [addr; val] /\ post m nil
          end
        | nil => False
        end;
    |}.

    Local Set Refine Instance Mode.
    Local Coercion literal(z : Z) : Syntax.expr := Syntax.expr.literal z.
(*  Local Coercion var(x: varname): Syntax.expr := Syntax.expr.var x.*)
    Local Definition var(x : @varname (@syntax semantics_params)):
      @expr.expr (@syntax semantics_params) := Syntax.expr.var x.
    (* TODO make coercions work *)
    (* Set Printing Implicit. Unset Printing Notations. *)

    Definition TODO{T: Type}: T. Admitted.

    Instance MMIOMacros: IOMacros.Interface := {|
      IOMacros.semantics_params := semantics_params;

      (* TODO these only read a byte rather than a word *)
      IOMacros.read_word_code(x _: varname) := bedrock_func_body:(
        x = -1 ;;
        while (var x .& (1 << 31)) {{ cmd.interact [x] MMInput [literal spi_rx] }}
      );
      IOMacros.write_word_code(x tmp: varname) := bedrock_func_body:(
        cmd.interact [tmp] MMInput [literal spi_tx_fifo] ;;
        while (var tmp .& (1 << 31)) {{ (* high order bit set means fifo is full *)
          cmd.interact [tmp] MMInput [literal spi_tx_fifo]
        }};;
        cmd.interact [] MMOutput [literal spi_tx_fifo; var x]
      );

      IOMacros.read_word_trace := read_byte;
      IOMacros.write_word_trace := write_byte;

      IOMacros.is_reserved_addr := isMMIOAddr;
    |}.
    - (* read_word_correct: *)
      intros.
      eapply exec.seq with
          (mid := fun t' m' l' => t' = t /\ m' = m /\ l' = map.put l x (word.of_Z (-1))).
      { eapply exec.set; [reflexivity|auto]. }
      { intros. apply TODO. (* will require a loop invariant *) }
    - (* write_word_correct: *)
      intros.
      (* need to show that this imperative code corresponds to the Inductive write_byte *)
      eapply exec.seq.
      { eapply exec.interact. (* proving that MMIO ext_spec is satisfied *)
        - simpl. reflexivity.
        - simpl. repeat split.
          + unfold isMMIOAddr. auto.
          + (* Interesting: How to know that memory is undefined at spi_tx_fifo? *)
            apply load_None; [lia|].
            apply H.
            unfold isMMIOAddr.
            auto.
          + apply TODO.
        - apply TODO.
      }
      apply TODO.
      Grab Existential Variables. all: intros; apply True.
    Defined.

  End WithMem.
End SpiEth.


Module Syscalls.

  Inductive SyscallAction := Syscall.

  (* Go models syscalls as
     func Syscall(trap, a1, a2, a3 uintptr) (r1, r2 uintptr, err Errno)
     so we will have syscalls with 4 word arguments and 3 word return values *)

  Section WithMem.
    Context {byte: word.word 8} {word: word.word 32} {mem: map.map word byte}.

    Definition Event: Type := (mem * SyscallAction * list word) * (mem * list word).

    Definition magicValue: Z. Admitted.

    (* TODO what about failures? *)
    (* TODO what if the syscall changes the memory? Do we see the whole memory? *)
    Inductive read_word: word -> list Event -> Prop :=
    | read_word_go: forall m x ret2 err,
        read_word x [((m, Syscall, [word.of_Z magicValue; word.of_Z magicValue;
                                      word.of_Z magicValue; word.of_Z magicValue]),
                      (m, [x; ret2; err]))].

    Inductive write_word: word -> list Event -> Prop :=
    | write_word_go: forall m x ret1 ret2 err,
        write_word x [((m, Syscall, [x; word.of_Z magicValue;
                                       word.of_Z magicValue; word.of_Z magicValue]),
                       (m, [ret1; ret2; err]))].


    Instance syntax_params: Syntax.parameters := {|
      Syntax.varname := string;
      Syntax.funname := Empty_set;
      Syntax.actname := SyscallAction;
    |}.

    Context {locals: map.map varname word}.
    Context {funname_env: forall T, map.map funname T}.

    Instance semantics_params: Semantics.parameters := {|
      Semantics.syntax := syntax_params;
      Semantics.width := 32;
      Semantics.word := word;
      Semantics.byte := byte;
      Semantics.mem := mem;
      Semantics.funname_eqb f1 f2 := Empty_set_rect (fun _ : Empty_set => bool) f1;
      Semantics.ext_spec t m action (argvals: list word) (post: (mem -> list word -> Prop)) :=
        (* TODO needs to be more precise *)
        match argvals with
        | [trap; a1; a2; a3] => forall r1 r2 err, post m [r1; r2; err]
        | _ => False
        end;
    |}.

    Local Set Refine Instance Mode.
    Local Coercion literal(z : Z) : Syntax.expr := Syntax.expr.literal z.
(*  Local Coercion var(x: varname): Syntax.expr := Syntax.expr.var x.*)
    Local Definition var(x : @varname (@syntax semantics_params)):
      @expr.expr (@syntax semantics_params) := Syntax.expr.var x.
    (* TODO make coercions work *)
    (* Set Printing Implicit. Unset Printing Notations. *)

    Definition TODO{T: Type}: T. Admitted.

    Instance SyscallIOMacros: IOMacros.Interface := {|
      IOMacros.semantics_params := semantics_params;

      IOMacros.read_word_code(x tmp: varname) :=
        cmd.interact [x; tmp; tmp] Syscall [literal magicValue; literal magicValue;
                                              literal magicValue; literal magicValue];

      IOMacros.write_word_code(x tmp: varname) :=
        cmd.interact [tmp; tmp; tmp] Syscall [var x; literal magicValue;
                                                literal magicValue; literal magicValue];

      IOMacros.read_word_trace := read_word;
      IOMacros.write_word_trace := write_word;

      (* this says "no reserved memory addresses", but probably there are (TODO) *)
      IOMacros.is_reserved_addr addr := False;
    |}.
    - (* read_word_correct: *)
      intros.
      eapply exec.interact with (mid := fun newM resvals =>
         newM = m /\ exists v ignored1 ignored2, resvals = [v; ignored1; ignored2]).
      + simpl. reflexivity.
      + simpl. eauto.
      + intros.
        destruct_products.
        subst.
        eexists. repeat split.
        do 2 eexists. repeat split.
        * (* TODO direction doesn't match *)
          apply TODO.
        * (* TODO need to specify that some ignored1, ignored2 are updated too *)
          apply TODO.
    - apply TODO.
      Grab Existential Variables. all: apply (word.of_Z 42) || apply map.empty.
    Defined.

  End WithMem.
End Syscalls.


Module MMIOUsage.
  Section WithParams.
    Existing Instance SpiEth.syntax_params.
    Context {byte: word.word 8} {word: word.word 32} {mem: map.map word byte}.
    Context {locals: map.map varname word}.
    Context {funname_env: forall T, map.map funname T}.

    Definition squarer_correct := @squarer_correct SpiEth.MMIOMacros.
    Check squarer_correct.
  End WithParams.
End MMIOUsage.


Module SyscallsUsage.
  Section WithParams.
    Existing Instance Syscalls.syntax_params.
    Context {byte: word.word 8} {word: word.word 32} {mem: map.map word byte}.
    Context {locals: map.map varname word}.
    Context {funname_env: forall T, map.map funname T}.

    Definition squarer_correct := @squarer_correct Syscalls.SyscallIOMacros.
    Check squarer_correct.
  End WithParams.
End SyscallsUsage.
