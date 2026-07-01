# Ring buffer in SPARK

Note: incomplete, WIP!

## Quick start

Install Alire, GNATprove, and the Z3 solver.

```console
$ # Build package
$ alr build

$ # Run prover
$ gnatprove -P spark_rb.gpr --pedantic --prover=z3
```

## TODOs
- [X] Implement ring buffer
- [X] Fully specify ring buffer code
- [X] Prove ring buffer specification
- [X] Prove all arithmetic lemmas
