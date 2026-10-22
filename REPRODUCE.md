# Reproduction

From the root of a freshly extracted export:

```sh
python3 verify_package.py
mkdir -p .reproduce
python3 build_paper.py
```

The build writes .reproduce/manuscript/paper.pdf and preserves the frozen paper.pdf. With the same TeX Live 2023 installation and fonts used in this audit, byte-identical output was checked from a second standalone copy. Across TeX installations typography and PDF bytes may differ; inspect the full output and the recorded tool version. No shell escape is enabled.

Pinned formal sources are in `companion/`. With Lean 4.31.0-rc1 and the unchanged Lake manifest:

```sh
cd companion
sha256sum -c audit/SOURCE_SHA256.txt
lake exe cache get
lake build
lake env lean --trust=0 AxiomAudit.lean
cd ..
```

The cache command obtains compiled mathlib dependencies. It is distinct from compiling those dependencies from source. This audit verified all 21 pinned source/configuration hashes and owned import closure, but did not rerun Lean.

Independent finite controls use Python's standard library:

```sh
python3 check_construction.py > .reproduce/finite.json
python3 -O check_construction.py > .reproduce/finite-O.json
cmp .reproduce/finite.json .reproduce/finite-O.json
```

They exhaust shore subsets for the included small rook/duplication and repaired semibiplane examples, check signed orthogonality and degree formulas, exhaust all eligible completion instances of shore order at most three, and reject corrupted controls. These are finite corroboration, not proof of the unbounded theorem. Read paper.tex for the all-order argument and the exact formal statement map.


Editorial PDF build (22 October 2026): Tectonic 0.17.0 was used locally with the same TeX sources and no shell escape. For an alternative build, create an output directory and run `tectonic --untrusted --keep-logs --outdir .reproduce/manuscript paper.tex`. The earlier pdfLaTeX byte-reproduction statement applies to the dated original build; PDF bytes vary with the compiler. The original pdfLaTeX build script remains available.
