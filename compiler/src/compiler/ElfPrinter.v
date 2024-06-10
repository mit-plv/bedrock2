(* ELF printer for a tiny subset of the spec at
   https://refspecs.linuxfoundation.org/elf/elf.pdf *)

Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import coqutil.Datatypes.ZList.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.LittleEndianList.
Require Import coqutil.Byte.
Require Import compiler.MemoryLayout.
Import List.ZIndexNotations. Local Open Scope zlist_scope.

Definition pad_right[A: Type](default: A)(desiredLength: Z)(l: list A): list A :=
  l ++ List.repeatz default (desiredLength - len l).

Definition padded_byte_array: Z -> list byte -> list byte := pad_right Byte.x00.

Definition ord(c: ascii): Z := Z.of_N (N_of_ascii c).

Definition Elf32_Addr: Z -> list byte := le_split 4.
Definition Elf32_Half: Z -> list byte := le_split 2.
Definition Elf32_Off: Z -> list byte := le_split 4.
Definition Elf32_Word: Z -> list byte := le_split 4.

(* ELF files for linking have the following structure:

     ELF header, optional program header table, sections, section header table

   ELF files for execution have the following structure:

     ELF header, program header table, segments, optional section header table

   We only focus on ELF files for execution. *)

Definition ELFMAG0 := 0x7f.
Definition ELFMAG1 := ord "E".
Definition ELFMAG2 := ord "L".
Definition ELFMAG3 := ord "F".

Definition ELFCLASS32 := 1.
Definition ELFCLASS64 := 2.
Definition ELFDATA2LSB := 1.
Definition ELFDATA2MSB := 2.
Definition EV_CURRENT := 1.

Definition EI_NIDENT := 16.

Definition ET_REL := 1. (* Relocatable file *)
Definition ET_EXEC := 2. (* Executable file *)
Definition ET_DYN := 3. (* Shared object file *)
Definition ET_CORE := 4. (* Core file *)

Definition SHN_UNDEF := 0.

Definition PT_LOAD := 1.

Definition PF_X := 1. (* Execute *)
Definition PF_W := 2. (* Write *)
Definition PF_R := 4. (* Read *)

Definition NO_ALIGNMENT := 0.

(* Magic number from
   https://github.com/riscv-non-isa/riscv-elf-psabi-doc/blob/master/riscv-elf.adoc *)
Definition EM_RISCV := 243.

Section WithParams.
  Context (width: Z) {word: word.word width}.
  Context (ml: @MemoryLayout width word).

  Definition e_class := if width =? 32 then ELFCLASS32 else ELFCLASS64.

  Definition e_ident: list byte := List.map byte.of_Z
    [|ELFMAG0; ELFMAG1; ELFMAG2; ELFMAG3; e_class; ELFDATA2LSB; EV_CURRENT|].

  Definition e_type := ET_EXEC. (* the only supported type, at the moment *)

  Definition e_machine := EM_RISCV. (* the only supported machine, at the moment *)

  Definition e_version := EV_CURRENT.

  (* address of first instruction to execute *)
  Definition e_entry := word.unsigned ml.(code_start).

  (* program header offset, equals ELF header size *)
  Definition e_phoff := 52.

  (* section header offset, measured in bytes, zero if none *)
  Definition e_shoff := 0.

  (* processor-specific flags *)
  Definition e_flags := 0.

  (* ELF header size, measured in bytes *)
  Definition e_ehsize := 52.

  (* size in bytes of 1 entry in the program header table *)
  Definition e_phentsize := 32.

  (* number of entries in the program header table *)
  Definition e_phnum := 3. (* in our simple case, always just 3: code, heap, stack *)

  (* section header size, measured in bytes *)
  (* we don't emit any sections, but the standard section header size is 40 *)
  Definition e_shentsize := 40.

  (* number of entries in the section header table *)
  Definition e_shnum := 0.

  (* section header table index for string table *)
  Definition e_shstrndx := SHN_UNDEF. (* no string table *)

  Definition ELF_header :=
    padded_byte_array EI_NIDENT e_ident ++    (* 16 *)
    Elf32_Half e_type ++                      (* 18 *)
    Elf32_Half e_machine ++                   (* 20 *)
    Elf32_Word e_version ++                   (* 24 *)
    Elf32_Addr e_entry ++                     (* 28 *)
    Elf32_Off e_phoff ++                      (* 32 *)
    Elf32_Off e_shoff ++                      (* 36 *)
    Elf32_Word e_flags ++                     (* 40 *)
    Elf32_Half e_ehsize ++                    (* 42 *)
    Elf32_Half e_phentsize ++                 (* 44 *)
    Elf32_Half e_phnum ++                     (* 46 *)
    Elf32_Half e_shentsize ++                 (* 48 *)
    Elf32_Half e_shnum ++                     (* 50 *)
    Elf32_Half e_shstrndx.                    (* 52 *)

  Record program_header_t: Set := {
    p_type:   Z; (* always PT_LOAD in our simple implementation *)
    p_offset: Z; (* offset from beginning of file at which first byte resides *)
    p_vaddr:  Z; (* at which virtual address to place this segment *)
    p_paddr:  Z; (* at which physical address to place this segment *)
    p_filesz: Z; (* number of bytes to be read from file, may be zero *)
    p_memsz:  Z; (* size in bytes of the segment to be created in memory,
                    p_filesz <= p_memsz, if strict inequality, remaining bytes are
                    initialized to 0 *)
    p_flags:  Z; (* R/W/X permission flags *)
    p_align:  Z; (* alignment *)
  }.

  Definition encode_program_header(h: program_header_t) :=
    Elf32_Word (p_type   h) ++
    Elf32_Off  (p_offset h) ++
    Elf32_Addr (p_vaddr  h) ++
    Elf32_Addr (p_paddr  h) ++
    Elf32_Word (p_filesz h) ++
    Elf32_Word (p_memsz  h) ++
    Elf32_Word (p_flags  h) ++
    Elf32_Word (p_align  h).

  (* Note: output also depends on section vars for bitwidth and memory layout *)
  Definition simple_riscv_elf(code: list byte): list byte :=
    let code_phdr := encode_program_header {|
      p_type := PT_LOAD;
      p_offset := e_phoff + e_phentsize * e_phnum;
      p_vaddr := word.unsigned ml.(code_start);
      p_paddr := word.unsigned ml.(code_start);
      p_filesz := len code;
      p_memsz := word.unsigned ml.(code_pastend) - word.unsigned ml.(code_start);
      p_flags := Z.lor PF_R PF_X;
      p_align := NO_ALIGNMENT;
    |} in
    let heap_phdr := encode_program_header {|
      p_type := PT_LOAD;
      p_offset := 0; (* ok because we won't read any bytes *)
      p_vaddr := word.unsigned ml.(heap_start);
      p_paddr := word.unsigned ml.(heap_start);
      p_filesz := 0;
      p_memsz := word.unsigned ml.(heap_pastend) - word.unsigned ml.(heap_start);
      p_flags := Z.lor PF_R PF_W;
      p_align := NO_ALIGNMENT;
    |} in
    let stack_phdr := encode_program_header {|
      p_type := PT_LOAD;
      p_offset := 0; (* ok because we won't read any bytes *)
      p_vaddr := word.unsigned ml.(stack_start);
      p_paddr := word.unsigned ml.(stack_start);
      p_filesz := 0;
      p_memsz := word.unsigned ml.(stack_pastend) - word.unsigned ml.(stack_start);
      p_flags := Z.lor PF_R PF_W;
      p_align := NO_ALIGNMENT;
    |} in
    let program_header_table := code_phdr ++ heap_phdr ++ stack_phdr in
    let segments := code in
    ELF_header ++ program_header_table ++ segments.

End WithParams.
