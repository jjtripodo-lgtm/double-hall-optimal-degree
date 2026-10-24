# Reader and review guide: optimal degree for the double Hall property

**John Tripodo** · [ORCID 0009-0006-9180-4953](https://orcid.org/0009-0006-9180-4953)

## Publication and citation

- [*Asymptotically optimal degree for the double Hall property*, Hexagon preprint **hexagon:2610.00462v1**](https://hexagonmath.org/2610.00462v1). This is a citable moderated preprint, **not** a peer-reviewed journal article and **not** a DOI.
- [Immutable GitHub PDF, manuscript version 1.0.1](https://github.com/jjtripodo-lgtm/double-hall-optimal-degree/blob/724ed6a8e76b6818e4a0a27b2ab0a16c457a5aa8/paper.pdf) · [TeX](paper.tex) · [citation metadata](CITATION.cff). Refer to the pinned PDF for exact GitHub manuscript bytes; cross-host PDF-byte equivalence with Hexagon has not been independently demonstrated.
- The original Zenodo deposit was **withdrawn** on 22 October 2026. DOI 10.5281/zenodo.23552249 is historical provenance, not an active/preferred identifier. See [publication history](publication_history/README.md).

## Main mathematical claim

For all sufficiently large n, the manuscript constructs a deterministic balanced **regular** bipartite graph with n vertices on each side, with the double Hall property on **both** sides, whose degree is at most

`sqrt(2n) + O(n^(21/80))`.

Combined with the stated lower bound, this yields leading constant `sqrt(2)` for the minimum possible maximum degree as a function of n. The proposed construction combines homology semibiplanes, a repair step, matched duplication and regular completion. The all-order error term uses the published Baker–Harman–Pintz prime-interval theorem.

## What the evidence does, and does not, establish

[Reproduction instructions](REPRODUCE.md) cover the frozen manuscript, package hashes, small exhaustive graph checks and a pinned Lean companion. [Formal scope](FORMAL_SCOPE.md) is important: the prime-interval input is an **explicit hypothesis** in the Lean transfer. The historical axiom audit is not fresh Lean compilation of this editorial version. Small finite computations do not verify the unbounded theorem, and no external specialist or journal review is claimed.

## Modest, useful independent review tasks

A reviewer can examine one tractable dependency without undertaking the whole project:

1. Check the double Hall definition and whether the semibiplane repair really yields the required property on both sides.
2. Check that padding and regular completion preserve the property and deliver the stated degree bound, with quantifiers for every sufficiently large n.
3. Check the Baker–Harman–Pintz interval implication and clearly separate the written all-order conclusion from the Lean theorem under an interval hypothesis.
4. Independently rerun the finite controls and verify they test the intended graph predicates, without extrapolating from finite cases.

A correction, counterexample, or precise missing premise would be as useful as confirmation.

## Other public papers

- [Separated distances in fixed dimension](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension)
- [Projective-plane determinant bounds for sparse binary matrices](https://github.com/jjtripodo-lgtm/sparse-projective-plane-determinants)

AI assistance is disclosed in the manuscript and Hexagon record. No independent human proof review, priority certification, or journal acceptance is represented here.
