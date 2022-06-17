Rupicola: Relation compilation for performance-critical applications |badge|
============================================================================

.. raw:: html

   <p align="center">
     <img src="etc/rupicola_small.webp" alt="Rupicola rupicola">
   </p>

Rupicola is a relational-compilation toolkit. It lets you build
customized compilers that translate (low-level) functional programs into
imperative code, like this:

Input
  .. code:: coq

     Definition onec_add16 (z1 z2: Z) :=
       let sum := z1 + z2 in (Z.land sum 0xffff + (Z.shiftr sum 16)).

     Definition ip_checksum (bs: list byte) :=
       let c := List.fold_left onec_add16 (List.map le_combine (chunk 2 bs)) 0xffff in
       Z.land (Z.lnot c) 0xffff.

Output
  .. code:: c

     uintptr_t ip_checksum(uintptr_t data,
                           uintptr_t len) {
       uintptr_t idx, to, b0, b1, chk17, w16, chk16;
       chk16 = 65535;
       idx = 0; to = len >> (uintptr_t)1;
       while (idx < to) {
         b0 = _br2_load(data + 2 * idx, 1);
         b1 = _br2_load(data + 2 * idx + 1, 1);
         w16 = b0 | (b1 << (uintptr_t)8);
         chk17 = chk16 + w16;
         chk16 = (chk17 & (uintptr_t)65535) +
                 (chk17 >> (uintptr_t)16);
         idx = idx + (uintptr_t)1;
       }
       if (len & (uintptr_t)1) {
         b0 = _br2_load(data + (len - (uintptr_t)1), 1);
         w16 = b0 | (((uintptr_t)0) << ((uintptr_t)8));
         chk17 = chk16 + w16;
         chk16 = (chk17 & (uintptr_t)65535) +
                 (chk17 >> (uintptr_t)16);
       }
       chk16 = (chk16 ^ UINTPTR_MAX) & (uintptr_t)65535;
       return chk16;
     }

--------------

Chose your own adventure below:

-  Learn about relational compilation by following `this tutorial <https://people.csail.mit.edu/cpitcla/thesis/relational-compilation.html>`__ or running through `this abridged version, as a Coq file <etc/relational-compilation-tutorial.v>`__.

-  Read about the design and implementation of Rupicola in `our PLDI 2022 paper <https://pit-claudel.fr/clement/papers/rupicola-PLDI22.pdf>`__, or in `this PhD dissertation <https://pit-claudel.fr/clement/PhD/RelationalCompilation_Pit-Claudel_2022.pdf>`__.

-  Watch the `Rupicola thesis defense <https://youtu.be/BG3RXB8hZo4>`__,

-  … or try Rupicola out by following the tutorial below!

Using Rupicola
==============

If you don’t want to set up Coq, clone Rupicola, and figure out dependencies, we recommend `downloading our artifact <https://doi.org/10.5281/zenodo.6330611>`__. The VM contains a detailed README and a step-by-step guide to reproduce the results in the paper. Otherwise, follow along below.

Setting up Rupicola on your own machine
---------------------------------------

A complete setup and build process is provided as a commented script in ```etc/vm-setup.sh`` <etc/vm-setup.sh>`__. We recommend reading through that file if you prefer to run everything on your own machine. (In fact, our artifact VM was built just by running the script found at ``etc/pldi2022-ae/setup.sh`` in the ``pldi2022-ae`` branch of the repository).

Use ``make -j`` to build Rupicola and its dependencies. The build can be pretty chatty at times, and some of the libraries we depend on (including Bedrock2 and coqutils) have build-time warnings (mostly due to backwards compatibility concerns).

We develop and test Rupicola only on GNU/Linux machines, though we have had students use it on macOS machines as well.

Getting started
---------------

We have an interactive, standalone tutorial on relational compilation in ``etc/relational-compilation-tutorial.v``, which you can following in your favorite Coq editor. This is an implementation of section 2 of the PLDI 2022 paper.

Once you’ve read through that, you can step through ``src/Rupicola/Examples/Uppercase.v`` (this is an implementation of the example in section 3 of the PLDI 2022 paper), which showcases the basics of compiling code with Rupicola.

Experimenting with this file is a good way to get a feel for Rupicola: you can try changing parts of the source code and looking at what part of the derivation breaks, for example.

By the way: “Rupicola Rupicola” is the scientific name of the Guianan cock-of-the-rock — a fitting name, since Rupicola compiles from Coq to Bedrock(2)!

Browsing other examples
~~~~~~~~~~~~~~~~~~~~~~~

The following files are not commented but should be reasonably easy to follow:

Error-detecting codes (cyclic redundancy check)
  ``crc32``: ``src/Rupicola/Examples/CRC32/CRC32.v``
Branchless UTF-8 decoding
  ``utf8``: ``src/Rupicola/Examples/Utf8/Utf8.v``
Scramble part of the Murmur3 algorithm
  ``m3s``: ``src/Rupicola/Examples/Arithmetic.v`` (module ``Murmur3``)
IP (one's-complement) checksum (RFC 1071)
  ``ip``: ``src/Rupicola/Examples/Net/IPChecksum/IPChecksum.v``
In-place DNA sequence complement
  ``fasta``: ``src/Rupicola/Examples/RevComp.v``
Fowler-Noll-Vo (noncryptographic) hash
  ``fnv1a``: ``src/Rupicola/Examples/Arithmetic.v`` (module ``FNV1A``)
A modern pseudorandom number generator
  ``l64x128``: ``src/Rupicola/Examples/L64X128.v``
Memory cells
  ``src/Rupicola/Examples/Cells/Cells.v``,
  ``src/Rupicola/Examples/Cells/IndirectAdd.v``
Nondeterminism
  ``src/Rupicola/Examples/Nondeterminism/StackAlloc.v``,
  ``src/Rupicola/Examples/Nondeterminism/Peek.v``
IO
  ``src/Rupicola/Examples/IO/Echo.v``

Reproducing benchmarks
----------------------

THe VM contains complete benchmarking scripts, which are also on the ``pldi2022-ae`` branch. Each benchmark includes a script ``ubench.sh``, as well as a manual C implementation of the same algorithm, and a driver for the C code generated by Rupicola. Both pieces of C code are benchmarked in the same conditions. Concretely, for e.g. ``Uppercase.v``, we have in ``src/Rupicola/Examples/``:


``Uppercase.v``
  The Coq source code.  Note the fragment at the end that generates C code:

  .. code:: coq

     Definition upstr_cbytes := Eval vm_compute in
       list_byte_of_string (ToCString.c_module [upstr_br2fn]).
``Uppercase/testdata.c``
  A generator that produces ``testdata.bin``, the data fed to the C programs
``Uppercase/upstr_c.c``
  The handwritten C version of the algorithm
``Uppercase/ubench.c``
  A C driver for the benchmarks
``Uppercase/ubench.sh``
  A script that prints out ``upstr_bytes`` from the Coq file into ``upstr_rupicola.c``, then runs the benchmarks
``Uppercase/upstr_rupicola.c`` (auto-generated)
  The Rupicola-generated C version of the algorithm

Compiling your own code with Rupicola
-------------------------------------

We wrote up a small exercise for the artifact evaluation, found in ``src/Examples/Exercises/ByteOps.v`` in the ``pldi2022-ae`` branch of the repo. It explores an extension of Rupicola’s expression compiler by using an arithmetic operator that is not supported out of the box by Rupicola and looking at how the compiler breaks and how support can be added for the new operator. A solution (in the form of a literate program) is in ``src/Examples/Exercises/ByteOps_Solution.v``.

Here are some other tasks that you may consider:

-  Compile a new small program, for example one that computes the max of three numbers (for an additional twist, read the three numbers from an array). The files ``Examples/Conditionals.v`` and ``Examples/Arrays.v`` are good places to start from.

-  Change the ``Uppercase`` example to apply a different transformation on strings. For example, write a string sanitizer that replaces every non-printable character by a space. If you get stuck, look at ``RevComp.v`` for inspiration.

.. |badge| image:: https://github.com/mit-plv/rupicola/workflows/Coq/badge.svg
