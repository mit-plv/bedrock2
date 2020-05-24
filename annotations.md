We use the following tags to annotate lines of code (in parentheses, we indicate whether this kind of code would still be needed in a near-perfect proof assistant):

- `spec`: interesting specification and notations needed to make the specs concise (would remain the same)
- `importboilerplate`, `administrivia`: imports, section management, section variables, `Add Ring`, `Set Printing Depth`, etc (shrinkable, but not completely removable, but also not a problem because mostly copy pasted)
- `code`: code that runs at runtime, i.e. implementation of lightbulb app (would remain the same)
- `compiletimecode`: code that runs at compile time, i.e. implemenation of compiler (would remain the same)
- `obvious`, `workaround`, `lists`, `bitvector`, `maps`, `symex`: accidental complexity (would not be needed)
- `proofsummary`: English summary of long obvious proofs (we believe that a machine checkable proof using roughly the same number of lines should be possible)
- `proof`, `loopinv`: interesting proof, includes statements of relevant helper lemmas (would be impossible or hard to remove due to Gödel's second incompleteness theorem)
- `doc`: inline documentation (would remain the same, just a convenience for humans, not relevant for machines)
- `library`: Code that should be in a general-purpose Coq library (would not be needed)
- `unrelated`: Code not needed for the lightbulb project
