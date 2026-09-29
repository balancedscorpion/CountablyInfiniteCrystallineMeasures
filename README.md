# Countably infinite crystalline-measure spaces

Crystalline measures are atomic measures whose support and Fourier spectrum are
both locally finite. They extend Poisson summation beyond periodic lattice combs
and form part of Meyer's programme of understanding simultaneous discreteness in
physical and Fourier space. Given a locally finite carrier
$\Lambda\subset\mathbb R$, let $\mathcal M_\Lambda$ denote the complete complex
vector space of tempered distributions for which both $T$ and its distributional
Fourier transform are locally atomic with support contained in $\Lambda$. A
basic structural question is which algebraic dimensions can occur for these
carrier-defined spaces.

We prove that countably infinite dimension occurs. More precisely, we construct
a locally finite $\Lambda\subset\mathbb R$ and a sequence
$(g_n)_{n\in\mathbb N}$ such that

```math
\mathcal M_\Lambda = \bigoplus_{n\in\mathbb N}\mathbb C g_n
\cong_{\mathbb C}\mathbb C^{(\mathbb N)}.
```

Thus every admissible distribution is a unique finite linear combination of the
$g_n$. In particular, the result exhausts the entire Meyer space associated with
the constructed carrier; it is not merely the construction of countably many
independent crystalline measures inside a larger space. Consequently, there is
no universal finite-or-continuum dichotomy for the Hamel dimension of
distributional Meyer spaces.

The construction assembles reciprocal, dilated high-order gap blocks at
adaptively separated scales. Estimates in negative Hermite scales force every
tempered element of the resulting space to involve only finitely many block
lines, while disjoint spectral selectors establish independence of the
generators. The atomic representations are understood locally on compactly
supported tests; no additional polynomial bound on total variation is imposed.
The principal theorem, including exhaustion and unique finite synthesis, has
been formalised in Lean 4.

## Scope and research relevance

This repository publishes only the exhaustive cardinal occurrence result
from MeyerGeneralProblem's `target-cardinal-closure`. It supplies a
countably infinite possibility between finite and continuum Hamel dimension,
and disproves a universal finite/continuum dichotomy for this distributional
space. Exhaustion is essential: infinitely many independent examples alone
would not bound the dimension from above.

The result is relevant to harmonic analysts studying simultaneous discrete
physical and Fourier supports, crystalline measures, and the relation between
growth conditions and algebraic dimension. It is not a geometric
classification of all locally finite carriers, a universal carrier evaluator,
a classification of shifted square-root sets, or a claim about the stronger
space defined by polynomially controlled total variation. No systematic
novelty search has been performed; novelty and priority are not claimed.

## The formal statement

[`Challenge.lean`](Challenge.lean) is the small, independent Mathlib-only
statement of record. Its definitions spell out local finiteness, local atomic
action, the Fourier transform and the complete Meyer subspace.
[`Solution.lean`](Solution.lean) proves the same declaration:

`CountablyInfiniteCrystallineMeasures.exhaustiveCardinalClaim`

The declaration includes the equality of Hamel rank to ℵ₀, the equivalence of
subspace membership with the two local atomic formulas, and the unique finite
expansion. All three conclusions concern the same carrier. The only `sorry`
is the intentional theorem placeholder in Challenge; it is not imported by
Solution. [`comparator.json`](comparator.json) selects this one theorem and
allows only `propext`, `Quot.sound` and `Classical.choice`.

## Proof architecture

The construction assembles reciprocal, dilated high-order gap blocks with
adaptively chosen separation scales. Each block contributes a genuine
one-dimensional paired atomic source. Estimates in the original negative
Hermite scales show that every whole source at a fixed order is supported on
only finitely many block lines. Those scales exhaust tempered distributions,
so the complete Meyer space equals the algebraic span of the actual
generators. Disjoint spectral selectors prove their independence. The
resulting linear equivalence from finitely supported reciprocal-label
coefficients proves countable Hamel dimension. Solution reindexes those
labels by ℕ and proves the compact statement without any construction
hypothesis.

The internal namespace `MeyerGeneralProblem` is retained to make the
extraction traceable. Only the recursive import closure of
`Cardinal.Adaptive.ConstructedAlgebraicBasis` is included. The supporting
Fourier, interpolation, sampling and Hilbert-space modules serve this proof;
the original research archive, broader classifiers, and other publication
entry points are not included. See [provenance](docs/PROVENANCE.md).

## Reproduce and prepare a submission

Install the Lean toolchain selected by `lean-toolchain`, then run from this
repository root:

```sh
lake exe cache get Challenge.lean Solution.lean
lake build Challenge Solution
python3 scripts/check.py
```

The manifest pins every dependency to an immutable GitHub commit. Do not run
`lake update` as part of verification of a pinned submission. The module-system
port uses Lean 4.35.0-rc3 and matching Mathlib/Tau Ceti revisions.

For Palomar, use the pinned full reusable workflow in
[`.github/workflows/palomar.yml`](.github/workflows/palomar.yml), after making
the submission snapshot public. A successful local build is not a Palomar
mechanical pass. The [publication checklist](docs/PUBLICATION.md) distinguishes
source checks, full mechanical verification, editorial review and permanent
registration.

## Authorship, sources and license

Jamie Martin and Li Shen are the human authors; Jamie Martin is the
responsible maintainer. This extracted snapshot is licensed under
[MIT](LICENSE). The substantive proof comes from the pinned
MeyerGeneralProblem development, with a module-system and dependency port
and a new Palomar interface. MeyerProblem was consulted as a publication
layout reference for a different theorem; its mathematical result is not
included. Exact citations and automation disclosures are in
[`formalization.yaml`](formalization.yaml).

The source repository records separate agent mathematical, adversarial and
verification reviews of its earlier candidate. Those are historical evidence,
not a review of this new extraction and toolchain port. The current preparation
is AI-assisted; no new independent human review or Palomar acceptance is
claimed.
