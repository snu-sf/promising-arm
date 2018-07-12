# Promising-ARM/RISC-V

Please visit the [project website](http://sf.snu.ac.kr/promise-concurrency/) for more information.

## Build

- Requirement: [Coq 8.8](https://coq.inria.fr/download), Make, Rsync.

- Initialization

        git clone https://github.com/snu-sf/promising-arm.git
        cd promising-arm
        git submodule init
        git submodule update

- `make`: quickly build without checking the proofs.

- `./build.sh`: build with checking all the proofs.  It will incrementally copy the development in the `.build` directory, and then build there.

- Interactive Theorem Proving: use [ProofGeneral](https://proofgeneral.github.io/) or [CoqIDE](https://coq.inria.fr/download).
  Note that `make` creates `_CoqProject`, which is then used by ProofGeneral and CoqIDE. To use it:
    + ProofGeneral: use a recent version.
    + CoqIDE: configure it to use `_CoqProject`: `Edit` > `Preferences` > `Project`: change `ignored` to `appended to arguments`.

## References

### Model

- `lib` and `src/lib` contains libraries not necessarily related to the relaxed-memory concurrency.

- `src/lib/Lang.v`: Definition of assembly-like language and its interpretation

- `src/promising/Promising.v`: Global-promising model (Section 8)

- `src/axiomatic/Axiomatic.v`: Definition of axiomatic semantics

- `src/lcertify`: Thread-locally certifying promising machine (work in progress)

- `src/certify`: Extended-promising model for ARMv8

### Results

- `src/promising/PtoPF.v`: Equivalence between global-promising and promise-first machine

- `src/axiomatic/AtoP.v`: Proof for inclusion of axiomatic in global-promising (`axiomatic_to_promising`)

- `src/axiomatic/PFtoA.v`: Proof for inclusion of promise-first machine in axiomatic (`promising_pf_to_axiomatic`)
    + `PFtoA1.v`: construction of axiomatic execution from promising execution
    + `PFtoA2.v`, `PFtoA3.v`: definitions and lemmas for main proof
    + `PFtoA4*.v`: proof for validity of constructed axiomatic execution
        * `PFtoA4SL.v`: simulation between promising execution and axiomatic execution
        * `PFtoA4OBR.v`, `PFtoA4OBW.v`: proof for "external" axiom
        * `PFtoA4FR.v`: proof for "external" axiom, especially on `fr` relation
        * `PFtoA4Atomic.v`: proof for "atomic" axiom

- Equivalence between global-promising and promising
    + work in progress

- Dead-lock freedom for RISC-V
    + work in progress

- Equivalence between global-promising and extended-promising
    + work in progress

- Dead-lock freedom for ARMv8
    + work in progress
