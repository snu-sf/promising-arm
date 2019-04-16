# Promising-ARM/RISC-V: a simpler and faster operational concurrency model

Christopher Pulte, Jean Pichon-Pharabod, Jeehoon Kang, Sung-Hwan Lee, Chung-Kil Hur.

40th annual ACM SIGPLAN conference on Programming Languages Design and Implementation ([PLDI 2019](https://pldi19.sigplan.org/)).

Please visit the [project website](https://sf.snu.ac.kr/promising-arm-riscv/) for more information.

## Build

- Requirement: [Coq 8.9](https://coq.inria.fr/download), Make, Rsync.

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

- `lib` and `src/lib` contains libraries not necessarily related to
  relaxed-memory concurrency.

- `src/lib/Lang.v`: Definition of assembly-like language and its interpretation

- `src/promising/Promising.v`: Definition of Promising-ARM/RISC-V without
  certification (corresponding to the rules on Figure 3)

- `src/axiomatic/Axiomatic.v`: Definition of Axiomatic

- `src/lcertify`: Thread-local certification

### Results

- Theorem 6.1: Equivalence between Promising-ARM/RISC-V and Axiomatic
  + Theorem `axiomatic_to_promising` in `src/axiomatic/AtoP.v`:
    Axiomatic refines Promising-ARM/RISC-V without certification.
  + Theorem `promising_to_axiomatic` in `src/axiomatic/PFtoA.v`:
    Promising-ARM/RISC-V without certification refines Axiomatic.
    * `PFtoA1.v`: construction of axiomatic execution from promising execution
    * `PFtoA2.v`, `PFtoA3.v`: definitions and lemmas for main proof
    * `PFtoA4*.v`: proof for validity of constructed axiomatic execution
      * `PFtoA4SL.v`: simulation between promising and axiomatic execution
      * `PFtoA4OBR.v`, `PFtoA4OBW.v`, `PFtoA4FR.v`: proof for "external" axiom
      * `PFtoA4Atomic.v`: proof for "atomic" axiom
  + Since Promising-ARM/RISC-V without certification is equivalent to
    Promising-ARM/RISC-V by Theorem 6.2, Promising-ARM/RISC-V is equivalent to
    Axiomatic.

- Theorem 6.2: Equivalence between Promising-ARM/RISC-V and Promising-ARM/RISC-V
  without certification
  + Theorem `certified_exec_equivalent` in `src/lcertify/CertifyComplete.v`:
    Promising-ARM/RISC-V and Promising-ARM/RISC-V without certification are
    equivalent.

- Theorem 6.3: Deadlock freedom of Promising-RISC-V
  + Theorem `certified_deadlock_free` in `src/lcertify/CertifyProgressRiscV.v`:
    Promising-RISC-V is deadlock-free.

- Theorem 6.4: Correctness of `find_and_certify`
  + Theorem `certified_promise_correct` in `src/lcertify/FindCertify.v`:
    `find_and_certify` is correct.
    * Theorem `certified_promise_sound` in `src/lcertify/FindCertify.v`:
      Assume the thread configuration `<T, M>` is certified, and promising
      `p` leads to `<T', M'>`. Then `<T'. M'>` is certified if `p` is in
      `find_and_certify <T, M>`.
    * Theorem `certified_promise_complete` in `src/lcertify/FindCertify.v`:
      Assume the thread configuration `<T, M>` is certified, and promising
      `p` leads to `<T', M'>`. Then `p` is in `find_and_certify <T, M>` if
      `<T', M'>` is certified.

- Theorem 7.1: For every Promising `tr`, there exists a trace `tr'` with same
  final state such that `tr'` can be split into a sequence of promise
  transitions followed by only non-promise transitions.
  + Theorem `promising_to_promising_pf` in `src/promising/PtoPF.v`:
    Promising-ARM/RISC-V refines Promising-PF, which promises all the writes at
    first.
