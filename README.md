Live Verification Artifact
==========================

We provide two ways to evaluate our artifact:
* Docker: Using a docker image with all software pre-installed and all files pre-compiled. It uses the `amd64` architecture. We built and tested it on Ubuntu 22 and Fedora 39 hosts, and we believe that it should also run on other Linux distros with an Intel x86-64 / amd64 architecture and on Mac OS.
* From source: Does not require docker, but requires a system with Coq, an IDE for it (preferably ProofGeneral), `make`, `python` and `gcc`, and up to half an hour of compilation time
The headings below indicate for which options they apply.


Getting Started (aka kick-the-tires phase)
------------------------------------------

### Install Docker [Docker only]

Install the Docker Engine (Docker CE) as described on https://docs.docker.com/engine/install/.
The docs try to convince you to install Docker Desktop, but Docker Desktop is not necessary and we did not use it.
We only use the Docker Engine (Docker CE). On the other hand, if you really like Docker Desktop, it probably also works with our image.
We used Docker version 25.0.4, but other versions could work too.
Note: On some systems (eg Fedora), after installing docker, you need to start the docker daemon explicitly using a command like eg `sudo systemctl start docker`, while on others, this seems to happen automatically.


### Import & start the image [Docker only]

Download `LiveVerifArtifactDockerImage.tar` and import it into docker:

```
sudo docker load -i /path/to/LiveVerifArtifactDockerImage.tar
```

After that, `sudo docker images` should list a "repository" named `LiveVerifArtifact`.
Then run the image:

```
sudo docker run -it LiveVerifArtifact
```

This should open a command prompt inside the docker image, where you can use `ls` and `cd` to look around to see what's there.
`~/bedrock2-LiveVerifArtifact-coq-8.17.1` is the *toplevel directory* containing the artifact.


### Install dependencies [from-source only]

You need the following software:
* Coq 8.17.1, installed using your preferred installation method. Versions < 8.17 will not work, version 8.18 and 8.19 probably work too.
* An IDE for Coq. We use Emacs + Proof General, but if you are familiar with another IDE, that might work too.
* GCC (we use version 9.4.0, but other versions probably work too)
* Python (we use version 3.12.2, but other 3.x versions probably work too)


### Compile Coq files [from-source only]

In the *toplevel directory* of the artifact, run `make LiveVerifCompile`.
This might take up to an hour. If you have 16GB of RAM, it should be safe to add `-j4` to get some parallelism (but too much parallelism can cause the system to run out of memory). On the author's (not so new) laptop, `make LiveVerifCompile -j4` took 18 minutes.

The build prints a few thousand lines of output to the terminal, which contains many warnings that can all safely be ignored.


### Check that you can step through a proof in your IDE [docker & from-source]

The following instructions are for emacs + proof general, but if you prefer a different Coq IDE, that should work too.

In the *toplevel directory* of the artifact, run `emacs LiveVerif/src/LiveVerifExamples/memset.v`.
Navigate to the line just after the one starting with `uintptr_t i = 0`.
Process the proof up to that point (Ctrl-c Ctrl-Enter), and make sure you see the source window and the window with the proof goal.
Process a few more lines of the proof (Ctrl-c Ctrl-n), and make sure you can see how this stepping affects the proof goal.



Overview
--------

The artifact contains the following dependencies:
* `deps/coqutil`: Generic Coq library
* `deps/riscv-coq`: Specification of the RISC-V ISA
* `bedrock2`: The bedrock2 source language
* `compiler`: The bedrock2-to-RISC-V compiler

And it contains the following directories related to the paper:
* `LiveVerif/src/LiveVerif`: The LiveVerif framework
* `LiveVerif/src/LiveVerifExamples`: Sample programs verified in the LiveVerif framework
* `LiveVerifCompile`: A small demo illustrating that the bedrock2 compiler indeed compiles a LiveVerif-generated Bedrock2 program

The project dependency structure looks as follows (right depends on left):

```
                   LiveVerif
                  /         \
         bedrock2            LiveVerifCompile
       /          \         /
coqutil            compiler
       \          /
         riscv-coq
```

#### Paper-section-to-source-file mapping

In the following, section numbers refer to the submission version of the paper (which has been provided to the artifact reviewers through hotcrp).
For each subsection, where applicable, we list the corresponding source files:

1. Introduction
2. Background
3. User Interface
   * 3.1 Overview by an Example (`LiveVerif/src/LiveVerifExamples/memset.v`)
       * 3.1.1 Polyglot Source File Can be Read as C or Coq at the Same Time
           * `LiveVerif/src/LiveVerifExamples/memset_exported.h`
       * 3.1.2 Function Signature Using Only One Type
       * 3.1.3 Specifications Using Separation Logic and Z
           * `bedrock2/src/bedrock2/SepBulletPoints.v`
           * Notations at the end of `LiveVerif/src/LiveVerif/LiveProgramLogic.v`
       * 3.1.4 The Initial Proof Goal
       * 3.1.5 C Snippets Acting As Proof-Script Steps
       * 3.1.6 Applying Tailored Weakest-Precondition Rules
           * `LiveVerif/src/LiveVerif/LiveRules.v`
       * 3.1.7 Expressing the Loop Invariant as a Diff from the Current Symbolic State
           * `LiveVerif/src/LiveVerif/PackageContext.v`
           * `Ltac while` in `LiveVerif/src/LiveVerif/LiveProgramLogic.v`
       * 3.1.8 Heapletwise Separation Logic
           * `bedrock2/src/bedrock2/HeapletwiseHyps.v`
       * 3.1.9 Accessing Memory That Is Part of a Bigger Separation-Logic Clause
           * `bedrock2/src/bedrock2/HeapletwiseAutoSplitMerge.v`
       * 3.1.10 Proving That The Current Symbolic State Satisfies Expectations
   * 3.2 Tradeoffs Between Three Different Ways of Compiling
       * `LiveVerif/src/LiveVerifExamples/Makefile`
       * `LiveVerifCompile/src/LiveVerifCompile/compile_memset.v`
   * 3.3 Concepts
       * 3.3.1 Predicate size
           * `bedrock2/src/bedrock2/SepLib.v`
       * 3.3.2 Support for adjacent sep clauses `sepapp` and `sepapps`
           * `bedrock2/src/bedrock2/sepapp.v`
       * 3.3.3 `n`-fillable predicates
           * `bedrock2/src/bedrock2/to_from_anybytes.v`
   * 3.4 Features
       * 3.4.1 Record Predicates
           * `Bedrock2/src/Bedrock2/RecordPredicates.v`
       * 3.4.2 IDE extensions
           * `LiveVerif/src/LiveVerif/live_verif_setup.el`
   * 3.5 Techniques
       * 3.5.1 Expressing a Loop Invariant as a Diff from the Current Symbolic State
           * `LiveVerif/src/LiveVerifExamples/memset.v`
           * `LiveVerif/src/LiveVerif/PackageContext.v`
           * `Ltac while` in `LiveVerif/src/LiveVerif/LiveProgramLogic.v`
           * `Lemma wp_while` in `LiveVerif/src/LiveVerif/LiveRules.v`
       * 3.5.2 Treating While Loops as Tail-Recursive Calls
           * Function `Strcmp` in `LiveVerif/src/LiveVerifExamples/nt_uint8_string.v`
           * `Ltac while_tailrec_use_functionpost` in
             `LiveVerif/src/LiveVerif/LiveProgramLogic.v`
           * `Lemma wp_while_tailrec_use_functionpost` in
             `LiveVerif/src/LiveVerif/LiveRules.v`
       * 3.5.3 Variable-Naming Scheme
           * `Ltac put_into_current_locals` in `LiveVerif/src/LiveVerif/LiveProgramLogic.v`
       * 3.5.4 Context Packaging and Merging for if-then-else
           * `LiveVerif/src/LiveVerifExamples/sort3_separate_args.v`
           * `Lemma wp_if_bool_dexpr` in `LiveVerif/src/LiveVerif/LiveRules.v`
           * `LiveVerif/src/LiveVerif/PackageContext.v`, especially `Ltac after_if`
       * 3.5.5 Safe Steps -- Avoiding backtracking for better proof debuggability
           * `Ltac sidecond_step` in `LiveVerif/src/LiveVerif/LiveProgramLogic.v`
           * `bedrock2/src/bedrock2/safe_implication.v`
4. Implementation Notes
   * 4.1 Parsing C in Coq
       * `LiveVerif/src/LiveVerif/LiveParsing.v`
       * `LiveVerif/src/LiveVerif/LiveSnippet.v`
       * `bedrock2/src/bedrock2/ident_to_string.v`
       * `LiveVerif/src/LiveVerif/string_to_ident.v`
   * 4.2 On-Demand Addition of Callee-Correctness Hypotheses
       * `Ltac call` in `LiveVerif/src/LiveVerif/LiveProgramLogic.v`
   * 4.3 Extracting Pure Facts from Sep Clauses
       * `bedrock2/src/bedrock2/PurifyHeapletwise.v`
       * `bedrock2/src/bedrock2/PurifySep.v`
   * 4.4 Pattern-Based Selective Warning Suppression
       * `bedrock2/src/bedrock2/SuppressibleWarnings.v`
   * 4.5 Mixed Word/Integer Arithmetic Side Conditions
       * `bedrock2/src/bedrock2/WordPushDownLemmas.v`
       * `bedrock2/src/bedrock2/unzify.v`
   * 4.6 Undoable, Reusable Zification
       * `bedrock2/src/bedrock2/unzify.v`
5. Discussion
   * 5.1 Why Not a Stand-Alone Tool?
   * 5.2 Limiting the Number of Conversions and Avoiding Operator Overloading
       * `deps/coqutil/src/coqutil/Datatypes/OperatorOverloading.v`
         (the heavy-weight approach we stopped using)
   * 5.3 Implementation Language
   * 5.4 Ltac1 vs Ltac2: When to prefer an untyped language with undocumented semantics
   * 5.5 Bitwidth Parameterization
6. Evaluation
   * 6.1 Scope of Sample Programs
       * `LiveVerif/src/LiveVerifExamples/`
   * 6.2 Qualitative Discussion of Loop-Invariants-As-Diff Approach
   * 6.3 Some Statistics
       * `LiveVerif/stats.py`
7. Related Work
8. Conclusion and Future Work


Step-by-step instructions [docker & from-source]
------------------------------------------------

### Make yourself feel at home in Proof General (or your other preferred Coq IDE)

To evaluate our artifact conveniently, a few editor settings are important.
First, make sure your terminal, emacs, or other IDE is maximized to occupy your whole screen. In emacs, you should have enough space to have two windows side-by-side that each is at least 85 characters wide (you can run `M-x` `column-number-mode` to display the current column of your cursor).

You also need a way to quickly move the cursor between different emacs windows (from the source window to the goal window and back). In the docker image, the `.emacs` file defines `C-c arrowkey` to jump to the window to the left/top/right/bottom of the current window.

No matter what IDE you're using, you should make sure that you have almost all of the left half of your screen to display the source (`.v` file) and almost all of the right half of your screen to display the proof goal (seeing the response/output window of Coq is useful too, but less important).

If you're using your own emacs (not in docker), the first time you open a LiveVerif example file (such as eg `LiveVerif/src/LiveVerifExamples/memset.v`, you will see the following message:

```
The local variables list in memset.v
or .dir-locals.el contains values that may not be safe (*).

Do you want to apply it?  You can type
y  -- to apply the local variables list.
n  -- to ignore the local variables list.
!  -- to apply the local variables list, and permanently mark these
      values (*) as safe (in the future, they will be set automatically.)
i  -- to ignore the local variables list, and permanently mark these
      values (*) as ignored

  * eval : (load-file "../LiveVerif/live_verif_setup.el")
```

We suggest to answer `!`, so that it won't be displayed again. Its effect is that when opening a file starting with the line `(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)`, emacs automatically executes the commands in `LiveVerif/src/LiveVerif/live_verif_setup.el`, which set up a few convenient shortcuts for the buffer of current file only.

And finally, an inconvenience warning for emacs users:
LiveVerif files end with the line `End LiveVerif. Comments .**/ //.`, which can greatly confuse Proof General's script management, to the point where you need to restart emacs.
It is therefore recommended to only process files up to the second-to-last line.
(But note that `coqc` of course processes the full files, and does not get confused).


### List of claims

In the following, section numbers refer to the submission version of the paper (which has been provided to the artifact reviewers through hotcrp).

List of claims from the paper supported by the artifact:
1. LiveVerif Coq files become C files when prefixed with an opening C comment `/*` (§1.1)
2. LiveVerif files can be compiled with GCC (§3.1.1)
3. LiveVerif ASTs can be compiled with GCC (§3.2)
4. LiveVerif ASTs can be compiled with the Bedrock2 compiler (§3.2)
5. Loop invariants can be expressed as a diff from the the current symbolic state (§3.1.7 and §3.5.1)
5. We implemented Emacs keyboard shortcuts for three very common LiveVerif-related operations (§3.4.2)
6. Inserting safe steps can help debug programs (§3.5.5)
7. The statistics in Table 2 are reproducible (§6)

List of claims from the paper not supported by the artifact:
- The intro claims that expressing loop invariants as a diff "potentially leads to an easier, more intuitive, and more enjoyable user experience and to proofs that are more robust against code changes, because diffs (edits) tend to be smaller than whole invariants". We have not yet collected numbers to support this claim, because, as we explain at the end of section 6.2, "our framework is still in an early prototype phase where most new examples that we verify point us to some bugs and limitations in the framework that we fix on the fly, but for a meaningful evaluation, one should not make fixes to the framework while verifying examples."
- The row "Performance of compiled code" of Table 1: The focus of this paper is the verification of C programs, while integrating it into bigger stacks and evaluating its performance there is part of our future projects.
- The star ratings in the table in Fig 5 are based on our perceived experience, not on numbers. We believe that if the artifact reviewers worked with our framework and other frameworks for a few weeks, they might come to similar ratings, but of course verifying this is out of scope of the artifact evaluation process.
- We do not include instructions on how to run RISC-V binaries created by the Bedrock2 compiler from LiveVerif programs, as this is not the focus of this paper (but we do run Bedrock2-compiler-generated RISC-V binaries in other not-yet-published projects, using qemu, both in user mode and system (bare-metal) mode, and also using spike, and also in a published project, using an FPGA running a verified processor, see [Erbsen et al. 2021]).


### How to verify the claims

#### 1. LiveVerif Coq files become C files when prefixed with an opening C comment `/*` (§1.1)

`cd` into `LiveVerif/src/LiveVerifExamples` and run `ls *_exported.h` to see the C code files that was obtained from Coq files. Note that to simplify the build process, we use C header files (`.h`) instead of C files (`.c`).

Open an exported file and the corresponding Coq file next to each other, eg by running `emacs memset_exported.h memset.v`, and observe that the `.h` file is the same as the `.v` file except for a prefix consisting of a few `#include` directives and an opening comment `/**.`.

#### 2. LiveVerif files can be compiled with GCC (§3.1.1)

`cd` into `LiveVerif/src/LiveVerifExamples` and run `make clean`.
Then, to turn the `.v` files into `.h` files and compile and run them, run `make`.
It prints the commands that it executes to the terminal. For each `FILE`, it should print and execute the following commands:

```
cat prelude.h.snippet FILE.v > FILE_exported.h
cc -O2 FILE_test.c -o FILE_test.exe
/path/to/FILE.exe > FILE_test.out
```

#### 3. LiveVerif ASTs can be compiled with GCC (§3.2)

Open `LiveVerif/src/LiveVerifExamples/uglyprint_memset.v` and process it up to the line `Print memset_ast.`
The response window should now contain the AST (containing `Syntax.cmd.seq`, `Syntax.cmd.while` etc) that was created by LiveVerif.

Then, process up to the line `print_bytes string_bytes`.
The response window should now contain a C prelude, followed by the `Memset` function obtained from the AST that was created using LiveVerif.

Copy-paste the C output in the response window into a file called `Memset.c` and compile it using `gcc -c Memset.c`, which should create a `Memset.o` file.


#### 4. LiveVerif ASTs can be compiled with the Bedrock2 compiler (§3.2)

Open `LiveVerifCompile/src/LiveVerifCompile/compile_memset.v` and process until just after `let r := eval cbv in memset_insts in idtac r.`
In the response window, this command outputs the RISC-V assembly instructions produced by running the Bedrock2 compiler on the memset AST created by LifeVerif.

Then, process up to just after `let r := eval cbv in memset_binary in idtac r.`
In the response window, this command outputs the hex-encoded RISC-V binary produced by the bedrock2 compiler.


#### 5. Loop invariants can be expressed as a diff from the the current symbolic state (§3.1.7 and §3.5.1)

Open `LiveVerif/src/LiveVerifExamples/memset.v` and process it upto and including the line starting with `uintptr_t i = 0` (by putting the cursor on the line after that line and hitting `C-c Enter` in emacs).
Verify that the proof goal corresponds to Fig 2a.

Process the next three Ltac commands (which also appear in Fig 2c) by hitting `C-c C-n` three times in Emacs and observe how this affects the proof goal aka symbolic state.
Verify that it corresponds to Fig 2b.

Uncomment the `Ltac log_packaged_context` at the top of the file, and process until just after the `/**.` after the `while`.
In the response window, you can see the loop invariant that was generated from the generalized context.
Verify that it corresponds to Fig 2d (up to a `packaged_mem_clause_marker` that we simplified away).

Run `grep -R LiveVerif/src/LiveVerifExamples --include='*.v' -e while` to list more examples containing while loops and decide for yourself which ones you want to inspect further.


#### 5. We implemented Emacs keyboard shortcuts for three very common LiveVerif-related operations (§3.4.2)

This part only works fully in Emacs. Non-emacs users may skip it the first two shortcuts, because the paper's main claims also hold without these Emacs extensions.
But non-emacs users should try to replicate the third shortcut manually by inserting and processing manually a few `step. step. step. ...`.

**Processing one line of C with `C-c C-k`:**
Open `LiveVerif/src/LiveVerifExamples/memset.v` and process it up to just after `store8(a + i, b);`. On the next line, write some dummy command, e.g. `i = 42;`. Then hit `C-c C-k`, and observe how this inserts spaces, a closing comment `/**.`, processes the buffer up to there, and inserts an opening comment `.**/`, a newline, and appropriate indentation, so that you can write the next command right away.

**Showing/hiding the Ltac block under the cursor with `Shift-Tab`:**
Place your cursor anywhere in the Ltac block just above the while loop. Hit `Shift-Tab` and observe how the Ltac code gets folded into `⋯`, and verify that the code now looks like in Figure 1. Hit `Shift-Tab` again to show the Ltac code again.

**Debugging the proof automation using repeated `step. step. ...` with `C-c C-i`**:
After `store8(a + i, b);`, replace the `/**.` by `/*?.`. This prevents proof automation from running after the snippet, so that you can debug it.
Next, press `C-j` to insert a newline without any indentation (the default indentation procedure that runs when hitting `Enter` unfortunately gets confused and is not usable here).
Then, press `C-c C-i` multiple times, and observe how `step.` gets inserted into the script and processed, and how the proof goal changes.
Also observe that in the response window, each `step` prints a short description of what it did, which is useful for debugging: One can search for the printed description in the file `LiveVerif/src/LiveVerif/LiveProgramLogic.v` to get to the Ltac snippet piece that ran in the current step.
After running `step.` 24 times, the conclusion of the goal should become just `ready` (which is a notation with an implicit argument to hide the actual goal, which is not important at this point).
(Note that if you run more `step.` after that, it will fail).
After insterting these 24 `step.` commands, processing the remainder of the program/proof until after the `Qed.` should still work.

If you are interested how these shortcuts are implemented, you can find the source in `LiveVerif/src/LiveVerif/live_verif_setup.el`.


#### 6. Inserting safe steps can help debug programs (§3.5.5)

Open `LiveVerif/src/LiveVerifExamples/ErrorTests/find_superrange_hyp_errors.v` and process up to just after the first occurrence of `uintptr_t tmp = load16(p-2);`.
After that command, replace the `/**.` by `/*?.`, and insert a few `step. step. step. ...` commands until `Error : "Exactly one of the following claims should hold:" [|subrange (p ^- /[2]) 2 p (8 + n * 4); inrange p (p ^- /[2]) 2|]` shows up as a hypothesis.

Try to think whether any of these two claims might hold, maybe by running commands like `assert (subrange (p ^- /[2]) 2 p (8 + n * 4)).`, `assert (inrange p (p ^- /[2]) 2)`, `unfold subrange, inrange.`.

Conclude that these claims can't hold, and that therefore, something in the program before must be wrong, namely the `p-2` should be `p+2`.
After making that replacement, and changing `/*?.` back into `/**.`, observe that processing this command now works and leads to a goal with `ready` in the conclusion, and a hypothesis `Def0 : tmp = /[barB b]` saying that the variable `tmp` now contains field `barB` of record `b`.


#### 7. The statistics in Table 2 are reproducible (§6)

Open `LiveVerif/src/LiveVerif/LiveProgramLogic.v` and replace the line

```
Ltac _stats := don't_print_stats.
```

by

```
Ltac _stats := print_stats.
```

and save the file.
Then, in the *toplevel directory* of the artifact, run

```
TIMED=1 make LiveVerif_ex > log.txt 2>&1
```

This recompiles all example files with timing and snippet count statistics enabled, and might take about 15 minutes. DO NOT use any `-j` option, because that would make it impossible to attribute the statistics lines to the correct files.
If you use the docker image, the file `log.txt` should already be there, so you could skip that step.
While waiting for the build to complete, you could watch the content of the log grow by running `tail -f log.txt` in a new terminal.

Once `make` has finished, run

```
python LiveVerif/stats.py log.txt
```

and check that its latex output looks similar to Table 2 in the paper.
The Funcs, Snippets, and Lines columns should match exactly, and the Time[s] column should match approximately, depending on the speed of your computer.
The final column, Loops, has to be checked by sampling manually:
`while` loops with only a `decreases` clause are traditional while loops (counted as the first number `x`), whereas `while` loops with both a `decreases` clause and an `initial_ghosts` clause are those in the style popularized by Tuerk [2010] (counted as the second number `y`. Loops using the lemma `wp_while_tailrec` instead of the C notations are also of the second kind.
