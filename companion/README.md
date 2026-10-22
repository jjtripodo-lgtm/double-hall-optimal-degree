# Double Hall Lean companion

This source companion formalizes the mapped construction and existence results in *Asymptotically optimal degree for the double Hall property* by John Tripodo.

## Reproduction

Install the Lean toolchain named in `lean-toolchain`. The pinned mathlib revision and all Lake dependencies are recorded in `lakefile.toml` and `lake-manifest.json`.

```sh
sha256sum -c audit/SOURCE_SHA256.txt
lake exe cache get
lake build
lake env lean --trust=0 AxiomAudit.lean
```

The cache command obtains mathlib's compiled dependencies; it is not a fresh rebuild of mathlib. `lake build` builds the owned DoubleHall sources. For independent verification, use a fresh output checkout and retain the toolchain, source hashes, command logs and axiom output. No dependency versions need to be changed.

## Mathematical boundary

`DoubleHall.semibiplane_order_theorem` is unconditional within Lean's standard axioms for finite fields of odd characteristic with cardinality at least 1153. `DoubleHall.transfer_theorem` retains `PrimeIntervalHyp theta` as an explicit hypothesis. The published Baker–Harman–Pintz prime theorem is not formalized here. The transfer conclusion gives existence and an explicit constant 33. Algorithmic running time and the separate augmentation lower-bound remark are written arguments, not formal theorems in this package.

The archived endpoint output in `audit/axioms.txt` records only `propext`, `Classical.choice` and `Quot.sound`. An axiom list does not discharge theorem hypotheses or replace independent compilation.
