# Ring buffer in SPARK

## Quick start

Install Alire, GNATprove, and the Z3 solver.

```console
$ # Build package
$ alr build

$ # Run prover
$ gnatprove --pedantic --counterexamples=on --prover=z3
$ cat obj/development/gnatprove/gnatprove.out
```
