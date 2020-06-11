# Intro

## Extraction is crappy [J]

Writing programs in Coq and verifying them works nicely and is well-understood, but there's not great story for running take code.  Extraction is the standard way to take code out of Coq, but it's full of issues:

- Performance
- Trust
- Code size
- Deployment (OCaml runtime)
- Memory use / GC

## Low-level is hard [C]

VCC, VST, Facade, Bedrock 1/2.
Low-level gives you fine-grained control, but forces you to deal with irrelevant details as well.
(with C in particular, the specs force you to pay for stuff you don't use)
Bedrock / Bedrock2 are much better, but you're still writing low-level, with many details that you may not care about
It helps to distinguish fancy low-level code that needs the power of a low-level language with simpler code that assembles pieces together and just needs to be able to invoke efficient code and do simple manipulations.
Common style: write Gallina and C, prove them equivalent.  Why not generate the C code?

□ Question for the group: What are VST success stories at the moment ?

## Gallina is nice [J]

Gallina is a good starting point; we'd like to make it a good place to end, too.

This is a real problem: Narcissus is a good potential client: it's nice for generating code, but we need extra optimizations to run efficiently (previous approach was too heavy/complicated to work reliably)

This is a real problem: parts of fiat-crypto are a good candidate (others need complete control, so fiat-crypto has a custom compiler and we're not going to replace that).  In fact, we have a cool example! [^^]

Q: How do we bridge the gap between the lowest-level gallina spec/impl and actual imperative code?
A: Minimal strategy for bridging that gap: write Gallina with just the right shape and extract that. Target a small but extensible subset of Gallina, use tactics to produce an equivalent Bedrock2 program.  Use Gallina as a macro language to assemble bits of imperative programs (intuitively, we're encoding Bedrock2 into Gallina to gain the advantages of a shallow-embedded language)

### First demo: Montgomery ladder (!!) [J]

## Purpose of the talk [C]

- Explain our approach
- Sync with other projects

# Our approach

## Big picture [C]

1. Target a subset of a good proof language (Gallina)
   This is a common strategy, e.g. in F*-land
2. Use tactics to synthesize Bedrock2
   We do this because we want extensibility: because of the misalignments between Gallina and Bedrock2, there's not a single correct way to translate each construct that we might be interested in compiling.  Instead we let users plug in new tactics.

For now, no need to worry about memory allocation (caller is responsible)

## Second demo: bedrock 2 and simple examples (swap/incr) [J]

- Show Bedrock2 code
- Show Gallina (hopefully with these two it's clear that we'd want to synthesize)
- Show individual calls to compile_step

## Interesting problem: mutating nested structures

[C]

Examples:
- Mutate a value retrieved from a map
- Construct a view over a packet

Problem: We want to split out parts of a container to handle them as independent objects, but the typical predicate in separation logic for a container owns all contained objects (e.g. an array of pointers, or a tree).  IOW, standard predicates are not ready to relinquish ownership of some of their children.

This is not a new problem: Bedrock2 has a predicate to let you split an array into (prefix * element * suffix).  This type of approach also works for a linked list.  But the split isn't as simple for more complex datastructures (often it's just not possible, like in a tree).

Approach: annotate elements as [Borrowed (a: address)] or [Owned].

---

[J]

Problem: how do you borrow multiple values?  Borrowing one value might invalidate results of subsequent lookups, because borrowed values may have been mutated (hence invalidating the gallina model for that address).

(This is a real issue; consider a packet with [length(header); header..; B]; then to find B we need to read length(header), so it must not be borrowed).

Approach: use an extra state, [Reserved (a: address)]. Reserved is inbetween owned and borrowed: it has an address that is asserts but it still claims ownership.

## Third demo: manual derivation of the map swap example [C]

# Next steps [J]

- Nested packets to stress-test the approach
- Loops
- Translating monadic code
- Memory allocation (long-term)
