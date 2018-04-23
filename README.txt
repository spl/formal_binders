To compile the scripts, you need Coq v8.1 or later.

Before you may run interactively the files,
you need to compile its dependencies. Run:
- "make all"  to compile all the scripts (takes 2 minutes on 1Ghz)
- "make main" to compile only the library and the main developments
- "make lib"  to compile only the library

To run the proofs interactively, use CoqIDE (recommanded),
or set up Proof General mode for Emacs.

Files are organized according to their prefix.

Prefix           Contents
------------------------------------------------------------
Lib          Extensions to Coq standard library (independent of Metatheory)
Metatheory   Shared library for metatheory developments

ML           ML with features development, type soundness
Fsub         Fsub, type soundness (Poplmark 1A+2A)
Coc          CoC, subject reduction

Lambda       Pure lambda terms, confluence
ML-core      ML core, type soundness
STLC_Core    STLC, type soundness (corresponds to the paper)
STLC_Data    STLC + patterns and recursion
STLC_Dec     STLC + annotations on app, type checking decidable
STLC_Core_WF STLC in Wright & Felleisen style, type soundness
STLC_Exn     STLC + exceptions, type soundness
STLC_Ref     STLC + references, type soundness
