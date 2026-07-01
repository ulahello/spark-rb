# Ring buffer in SPARK

An implementation of a ring buffer in Ada/SPARK, fully proven to match its specification.
This is done with lots of [modular arithmetic lemmas](./src/lemmas.ads).

## Quick start

Install Alire, GNATprove, and the Z3 solver.

```console
$ # Build package
$ alr build

$ # Run prover
$ gnatprove -P spark_rb.gpr --pedantic --prover=z3
```
