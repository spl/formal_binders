This project was originally developed for Coq 8.1. Other versions of Coq have
not been tested.

To install Coq 8.1:

1. [Install `opam`](https://opam.ocaml.org/doc/Install.html)

2. Install Coq 8.1 from the [opam-coq-archive](https://github.com/coq/opam-coq-archive/tree/master/core-dev):

   1. `opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev`
   2. `opam install coq.8.1.dev`

Before you can run interactively the files, you need to compile its
dependencies. These are the build options:

* `make all`:  compile all scripts
* `make main`: compile only the library and the main developments
* `make lib`:  compile only the library

To run the proofs interactively, use CoqIDE (recommended) or Proof General.

The files are organized according to prefix:

| Prefix         | Contents                                                       |
| -------------- | -------------------------------------------------------------- |
| `Lib`          | Extensions to Coq standard library (independent of Metatheory) |
| `Metatheory`   | Shared library for metatheory developments                     |
|                |                                                                |
| `ML`           | ML with features development, type soundness                   |
| `Fsub`         | Fsub, type soundness (Poplmark 1A+2A)                          |
| `CoC`          | CoC, subject reduction                                         |
|                |                                                                |
| `Lambda`       | Pure lambda terms, confluence                                  |
| `ML_Core`      | ML core, type soundness                                        |
| `STLC_Core`    | STLC, type soundness (corresponds to the paper)                |
| `STLC_Data`    | STLC + patterns and recursion                                  |
| `STLC_Dec`     | STLC + annotations on app, type checking decidable             |
| `STLC_Core_WF` | STLC in Wright & Felleisen style, type soundness               |
| `STLC_Exn`     | STLC + exceptions, type soundness                              |
| `STLC_Ref`     | STLC + references, type soundness                              |
