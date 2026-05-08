# Ring buffer in SPARK

Note: incomplete, WIP!

## Quick start

Install Alire, GNATprove, and the Z3 solver.

```console
$ # Build package
$ alr build

$ # Run prover
$ gnatprove --pedantic --counterexamples=on --prover=z3
$ cat obj/development/gnatprove/gnatprove.out
```

## TODOs
- [ ] Prove all arithmetic lemmas
- [ ] Finish implementing ring buffer
- [ ] Fully specify ring buffer code
- [ ] Prove ring buffer specification
