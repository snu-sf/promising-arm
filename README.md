# Promising-ARM/RISC-V

This is the supplementary material for POPL 2019 submission #23: "Promising-ARM/RISC-V: a simpler
and faster operational memory model for ARMv8 and RISC-V".

## Build

- Requirement: [Coq 8.8](https://coq.inria.fr/download), Make, Rsync.

- Initialization

        cd promising-arm
        git submodule init
        git submodule update

- `make`: quickly build without checking the proofs.

- `./build.sh`: build with checking all the proofs.  It will incrementally copy the development to
  `.build` sub-directory, and then build there.

- Interactive Theorem Proving: use [ProofGeneral](https://proofgeneral.github.io/) or
  [CoqIDE](https://coq.inria.fr/download).  Note that `make` creates `_CoqProject`, which is then
  used by ProofGeneral and CoqIDE. To use it:
    + ProofGeneral: use a recent version.
    + CoqIDE: configure it to use `_CoqProject`: `Edit` > `Preferences` > `Project`: change
      `ignored` to `appended to arguments`.

## References

### Model

- `lib` and `src/lib` contains libraries not necessarily related to relaxed-memory concurrency.

- `src/lib/Lang.v`: Definition of assembly-like language and its interpretation

- `src/promising/Promising.v`: Definition of Global-Promising (Section 3-4, 8.1)

- `src/axiomatic/Axiomatic.v`: Definition of Axiomatic (Section 8)

- `src/lcertify`: Thread-local certification (Section 3.5, 8.1)

- `src/certify`: (Work-in-progress) Certification with ARMv8 store exclusives (Section 7) and the
  definition of Extended-Promising (Section 8.1)

### Results

The following theorems collectively prove Theorem 8.1, 8.2, 8.3, and the observation made in Section 6.1:

- The optimisation for exhaustive exploration is sound (Section 6.1).  Or equivalently,
  Global-Promising refines Optimised Global-Promising.  See Theorem `promising_to_promising_pf` in
  `src/promising/PtoPF.v`.

- Optimised Global-Promising refines Axiomatic (Theorem 8.1).  See Theorem
  `promising_pf_to_axiomatic` in `src/axiomatic/PFtoA.v`. The proof consists of:

    + `PFtoA1.v`: construction of axiomatic execution from promising execution
    + `PFtoA2.v`, `PFtoA3.v`: definitions and lemmas for main proof
    + `PFtoA4*.v`: proof for validity of constructed axiomatic execution
        * `PFtoA4SL.v`: simulation between promising and axiomatic execution
        * `PFtoA4OBR.v`, `PFtoA4OBW.v`, `PFtoA4FR.v`: proof for "external" axiom
        * `PFtoA4Atomic.v`: proof for "atomic" axiom

- Axiomatic refines Global-Promising (Theorem 8.1).  See Theorem `axiomatic_to_promising` in
  `src/axiomatic/AtoP.v`.

- Global-Promising refines Promising (Theorem 8.2).  See Theorem `certifiec_exec_complete` in
  `src/lcertify/CertifyComplete.v`.

- Promising refines Global-Promising (Theorem 8.2).  See Theorem `certified_exec_sound` in
  `src/lcertify/Certify.v`.

- Promising-RISC-V is deadlock-free (Theorem 8.3).  See Theorem `certified_deadlock_free` in
  `src/lcertify/CertifyProgressRiscV.v`.


Theorem 8.4 and 8.5 are unprogressed.
