Require Import coqutil.Z.Lia.
Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth32.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import Coq.Strings.String.
Require Import bedrock2.TracePredicate. Import TracePredicateNotations.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.

(* TODO distribute contents of this file into the right places *)

Module Import IOMacros.

  Class Interface := {
    width : Z;
    BW :> Bitwidth width;
    word :> Word.Interface.word width;
    mem :> map.map word Byte.byte;
    locals :> map.map String.string word;
    env :> map.map String.string (list String.string * list String.string * cmd);
    ext_spec :> ExtSpec;

    (* macros to be inlined to read or write a word
       TODO it's not so nice that we need to foresee the number of temp vars
       each implementation might need *)
    read_word_code(x tmp: String.string): cmd;
    write_word_code(x tmp: String.string): cmd;

    (* means "this trace does nothing else than reading the given word", could require
       several events if we're polling until a word is available *)
    read_word_trace: word -> trace -> Prop;
    (* means "this trace does nothing else than outputting the given word", could require
       several events if we have to poll a "ready to accept next word" flag before writing *)
    write_word_trace: word -> trace -> Prop;

    (* the IOMacros module is allowed to reserve part of the address space,
       eg for MMIO, or to communicate with the kernel *)
    is_reserved_addr: word -> Prop;

    read_word_correct: forall t m l mc x tmp,
        (forall a, is_reserved_addr a -> map.get m a = None) ->
        exec map.empty (read_word_code x tmp) t m l mc (fun t' m' l' mc' =>
          m = m' /\ exists t'' v, t' = t ++ t'' /\ read_word_trace v t'' /\ l' = map.put l x v);

    write_word_correct: forall t m l mc x tmp v,
        (forall a, is_reserved_addr a -> map.get m a = None) ->
        map.get l x = Some v ->
        exec map.empty (write_word_code x tmp) t m l mc (fun t' m' l' mc' =>
          m = m' /\ exists t'', t' = t ++ t'' /\ write_word_trace v t'' /\ l' = l);
  }.

End IOMacros.

Section Squarer.

  Context {ioLib: IOMacros.Interface}.

  Definition squarer_trace: trace -> Prop :=
    kleene (existsl (fun inp => IOMacros.read_word_trace inp +++
                                IOMacros.write_word_trace (word.mul inp inp))).

  Definition squarer: cmd. Admitted.

  Lemma squarer_correct: forall (m: mem) (l: locals) mc,
      exec map.empty squarer nil m l mc (fun t' m' l' mc' => squarer_trace t').
  Admitted.

End Squarer.


(* TODO: on which side of the list do we add new events? *)

Module SpiEth.

  Definition MMInput := "MMInput"%string.
  Definition MMOutput := "MMOutput"%string.

  Section WithMem.
    Import Word.Interface.
    Context {word: word.word 32} {mem: map.map word Byte.byte} {mem_ok: map.ok mem}.
    Context {word_ok: word.ok word}.

    Definition Event: Type := (mem * String.string * list word) * (mem * list word).

    Definition msb_set(x: word): Prop :=
      word.and x (word.slu (word.of_Z 1) (word.of_Z 31)) <> word.of_Z 0.

    Definition lo_byte(x: word): word :=
      word.and x (word.of_Z 255).

    Definition spi_rx     : Z := 0x1002404c.
    Definition spi_tx_fifo: Z := 0x10024048.
    Definition spi_pinmux : Z := 0x10012038.
    Definition spi_sckdiv : Z := 0x10024000.
    Definition spi_csmode : Z := 0x10024018.

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

    Context {locals: map.map String.string word}.
    Context {funname_env: forall T, map.map String.string T}.

    Instance ext_spec: ExtSpec :=
      fun t mGive action (argvals: list word) (post: (mem -> list word -> Prop)) =>
        match argvals with
        | addr :: _ =>
          isMMIOAddr addr /\
          if String.eqb action MMInput then
            argvals = [addr] /\ forall val, post map.empty [val]
          else if String.eqb action MMOutput then
                 exists val, argvals = [addr; val] /\ post map.empty nil
          else False
        | nil => False
        end.

    Import Syntax BinInt String List.ListNotations ZArith.
    Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

    Local Axiom TODO: False.

    Instance MMIOMacros: IOMacros.Interface. refine ({|

      (* TODO these only read a byte rather than a word *)
      IOMacros.read_word_code(x _: String.string) := bedrock_func_body:(
        $x = $-1 ;
        while ($x & coq:(Z.shiftl 1 31)) { io! $x = $MMInput($spi_rx) }
      );
      IOMacros.write_word_code(x tmp: String.string) := bedrock_func_body:(
        io! tmp = $MMInput($spi_tx_fifo);
        while (tmp & coq:(Z.shiftl 1 31)) { (* high order bit set means fifo is full *)
          io! tmp = $MMInput($spi_tx_fifo)
        };
        io! coq:(nil) = $MMOutput($spi_tx_fifo, $x)
      );

      IOMacros.read_word_trace := read_byte;
      IOMacros.write_word_trace := write_byte;

      IOMacros.is_reserved_addr := isMMIOAddr;
    |}).
    - (* read_word_correct: *)
      intros.
      eapply exec.seq with
          (mid := fun t' m' l' mc' => t' = t /\ m' = m /\ l' = map.put l x (word.of_Z (-1))).
      { eapply exec.set; [reflexivity|auto]. }
      { intros. case TODO. (* will require a loop invariant *) }
    - (* write_word_correct: *)
      intros.
      (* need to show that this imperative code corresponds to the Inductive write_byte *)
      eapply exec.seq.
      { (* proving that MMIO ext_spec is satisfied *)
        eapply exec.interact with (mKeep := m) (mGive := map.empty).
        - apply map.split_empty_r. reflexivity.
        - simpl. reflexivity.
        - simpl. repeat split.
          + unfold isMMIOAddr. auto.
          + case TODO.
        - case TODO.
      }
      case TODO.
      Unshelve. all: intros; apply True.
    Defined.

  End WithMem.
End SpiEth.


Module Syscalls.

  Definition SyscallAction := String.string.

  (* Go models syscalls as
     func Syscall(trap, a1, a2, a3 uintptr) (r1, r2 uintptr, err Errno)
     so we will have syscalls with 4 word arguments and 3 word return values *)

  Section WithMem.
    Context {word: word.word 32} {mem: map.map word Byte.byte} {mem_ok: map.ok mem}.
    Context {word_ok: word.ok word}.
    Import Word.Interface.

    Definition Event: Type := (mem * SyscallAction * list word) * (mem * list word).

    Definition magicValue: Z. Admitted.

    (* TODO what about failures? *)
    (* TODO what if the syscall changes the memory? Do we see the whole memory? *)
    Inductive read_word: word -> list Event -> Prop :=
    | read_word_go: forall m x ret2 err,
        read_word x [((m, "Syscall"%string, [word.of_Z magicValue; word.of_Z magicValue;
                                            word.of_Z magicValue; word.of_Z magicValue]),
                      (m, [x; ret2; err]))].

    Inductive write_word: word -> list Event -> Prop :=
    | write_word_go: forall m x ret1 ret2 err,
        write_word x [((m, "Syscall"%string, [x; word.of_Z magicValue;
                                             word.of_Z magicValue; word.of_Z magicValue]),
                       (m, [ret1; ret2; err]))].

    Context {locals: map.map String.string word}.
    Context {funname_env: forall T, map.map String.string T}.

    Instance ext_spec: ExtSpec :=
      fun t m action (argvals: list word) (post: (mem -> list word -> Prop)) =>
        (* TODO needs to be more precise *)
        match argvals with
        | [trap; a1; a2; a3] => forall r1 r2 err, post m [r1; r2; err]
        | _ => False
        end.

    Local Axiom TODO: False.

    Import expr.
    Instance SyscallIOMacros: IOMacros.Interface. refine ({|

      IOMacros.read_word_code(x tmp: String.string) :=
        cmd.interact [x; tmp; tmp] "Syscall"%string [literal magicValue; literal magicValue;
                                                     literal magicValue; literal magicValue];

      IOMacros.write_word_code(x tmp: String.string) :=
        cmd.interact [tmp; tmp; tmp] "Syscall"%string [var x; literal magicValue;
                                                       literal magicValue; literal magicValue];

      IOMacros.read_word_trace := read_word;
      IOMacros.write_word_trace := write_word;

      (* this says "no reserved memory addresses", but probably there are (TODO) *)
      IOMacros.is_reserved_addr addr := False;
    |}).
    - (* read_word_correct: *)
      intros.
      eapply exec.interact with (mid := fun newM resvals =>
         newM = map.empty /\ exists v ignored1 ignored2, resvals = [v; ignored1; ignored2])
         (mKeep := m) (mGive := map.empty).
      + apply map.split_empty_r. reflexivity.
      + simpl. reflexivity.
      + simpl. eauto.
      + intros.
        destruct_products.
        subst.
        eexists. split.
        * reflexivity.
        * intros. apply map.split_empty_r in H0. subst m'. split; [reflexivity|]. do 2 eexists. split.
          { (* TODO direction doesn't match *)
            case TODO. }
          { (* TODO need to specify that some ignored1, ignored2 are updated too *)
            case TODO. }
    - case TODO.
      Unshelve. all: apply (word.of_Z 42) || apply map.empty || apply nil.
    Defined.

  End WithMem.
End Syscalls.


Module MMIOUsage.
  Section WithParams.
    Context {word: word.word 32} {mem: map.map word Byte.byte} {mem_ok: map.ok mem}.
    Context {word_ok: word.ok word}.
    Context {locals: map.map String.string word}.
    Context {funname_env: forall T, map.map String.string T}.

    Definition squarer_correct := @squarer_correct SpiEth.MMIOMacros.
    (*Check squarer_correct.*)
  End WithParams.
End MMIOUsage.


Module SyscallsUsage.
  Section WithParams.
    Context {word: word.word 32} {mem: map.map word Byte.byte} {mem_ok: map.ok mem}.
    Context {word_ok: word.ok word}.
    Context {locals: map.map String.string word}.
    Context {funname_env: forall T, map.map String.string T}.

    Definition squarer_correct := @squarer_correct Syscalls.SyscallIOMacros.
    (*Check squarer_correct.*)
  End WithParams.
End SyscallsUsage.
