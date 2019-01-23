Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Interface.
Require Import bedrock2.ListPred. Import ListPredNotations.
Require Import bedrock2.Semantics.

(*Require Import bedrock2.BasicC64Syntax.*)
Require Import bedrock2.Syntax.
(*Local Existing Instance bedrock2.BasicC64Syntax.StringNames_params.*)


(* TODO distribute contents of this file into the right places *)

Section Squarer.

  Context {p: Semantics.parameters}.

  Definition Event: Type := (mem * actname * list word) * (mem * list word).

  Context (read_word: word -> list Event -> Prop).
  Context (write_word: word -> list Event -> Prop).

  Definition squarer_trace: list Event -> Prop :=
    (existsl (fun inp => read_word inp +++ write_word (word.mul inp inp))) ^*.

  Definition squarer: Syntax.cmd. Admitted.

  Lemma squarer_correct: forall (m: mem) (l: locals),
      exec map.empty squarer nil m l (fun t' m' l' => squarer_trace t').
  Admitted.

End Squarer.


(* TODO: on which side of the list do we add new events? *)

Module SpiEth.

  Inductive actname := MMInput | MMOutput.

  Section WithMem.
    Context {byte: word.word 8} {word: word.word 32} {mem: map.map word byte}.
    (* Context {mem: Type}. *)

    Definition Event: Type := (mem * actname * list word) * (mem * list word).

    Definition msb_set(x: word): Prop :=
      word.and x (word.slu (word.of_Z 1) (word.of_Z 31)) <> word.of_Z 0.

    Definition lo_byte(x: word): word :=
      word.and x (word.of_Z 255).

    (* TODO hex notation *)
    Definition spi_rx     : word := word.of_Z 268582988. (* 0x1002404c *)
    Definition spi_tx_fifo: word := word.of_Z 268582984. (* 0x10024048 *)

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
        read_byte (lo_byte x) [((m, MMInput, [spi_rx]), (m, [x]))]
    | read_byte_wait: forall x y m rest,
        msb_set x ->
        read_byte y rest ->
        read_byte y (((m, MMInput, [spi_rx]), (m, [x])) :: rest).

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
        write_byte (word.of_Z b) [((m, MMInput, [spi_tx_fifo]), (m, [x]));
                                  ((m, MMOutput, [spi_tx_fifo; word.of_Z b]), (m, []))]
    | write_byte_wait: forall x b m rest,
        msb_set x ->
        write_byte b rest ->
        write_byte b (((m, MMInput, [spi_tx_fifo]), (m, [x])) :: rest).

  End WithMem.
End SpiEth.


Module Syscalls.

  Inductive actname := Syscall.

  (* Go models syscalls as
     func Syscall(trap, a1, a2, a3 uintptr) (r1, r2 uintptr, err Errno)
     so we will have syscalls with 4 word arguments and 3 word return values *)

  Section WithMem.
    Context {byte: word.word 8} {word: word.word 32} {mem: map.map word byte}.
    (* Context {mem: Type}. *)

    Definition Event: Type := (mem * actname * list word) * (mem * list word).

    Definition magicValue: word. Admitted.

    (* TODO what about failures? *)
    (* TODO what if the syscall changes the memory? Do we see the whole memory? *)
    Inductive read_word: word -> list Event -> Prop :=
    | read_word_go: forall m x ret2 err,
        read_word x [((m, Syscall, [magicValue; magicValue; magicValue; magicValue]),
                      (m, [x; ret2; err]))].

    Inductive write_word: word -> list Event -> Prop :=
    | write_word_go: forall m x ret1 ret2 err,
        write_word x [((m, Syscall, [x; magicValue; magicValue; magicValue]),
                       (m, [ret1; ret2; err]))].

  End WithMem.
End Syscalls.
