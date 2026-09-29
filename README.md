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

In Section 6 of [*Measures with locally finite support and spectrum*
(2017)](https://doi.org/10.4171/RMI/962), Yves Meyer asks about the dimension of
$\mathcal M_\Lambda$, the space of atomic measures supported on a common carrier
with their Fourier transforms. This sits alongside the distinction between
uniformly discrete and merely locally finite supports: [Lev and Olevskii
(2016)](https://doi.org/10.4171/RMI/920) establish nonperiodic examples in the
latter setting, beyond the periodic structure forced by uniform discreteness
of both support and spectrum in one dimension.

The theorem here constructs a locally finite carrier $\Lambda\subset\mathbb R$
whose complete distributionally tempered space satisfies

```math
\boxed{\dim_{\mathbb C}\mathcal M_\Lambda=\aleph_0.}
```

It provides a complete algebraic synthesis: every admissible distribution has a
unique finite expansion in the constructed generators. This synthesis and the
exact dimension are formalized in Lean 4.

### Why exhaustion matters

The distinction is between constructing independent sources and determining
the complete source space:

```math
\text{countably many independent sources}
\quad\not\Rightarrow\quad
\dim_{\mathbb C}\mathcal M_\Lambda=\aleph_0.
```

Independence gives a lower bound. The analytic work is proving that **there are
no additional sources** outside the finite generator span, including sources
that could enlarge its dimension to the continuum. The result therefore rules
out a universal finite-versus-continuum principle for these distributional
spaces. This principle is not presented as a named published conjecture, and no
claim of novelty or priority is made.

### Structure across distributional orders

Write $H_{-p}$ for the original negative Hermite scale, identified with its image
in tempered distributions, and put $d_p=\dim_{\mathbb C}(\mathcal M_\Lambda\cap H_{-p})$.
For the constructed carrier, the proof gives finite-dimensional layers whose
dimensions are unbounded across orders:

```math
d_p<\infty\quad(p\in\mathbb N),
\qquad
\sup_{p\in\mathbb N}d_p=\infty.
```

At each positive order $p$, the finite-exhaustion argument confines every whole
source to generator lines with positive block index below $6p$. Each finite
collection of generators, in turn, belongs to some common Hermite order. Their
independence makes the layer dimensions unbounded; the order-zero layer embeds
in the order-one layer. Thus no fixed order contains infinitely many independent
directions, although the union of the layers has countably infinite dimension.

Distributional order therefore records information that the total dimension
alone does not capture. The passage from finite exhaustion and independence to
these layer consequences uses finite-dimensional linear algebra and the nested
Hermite scales. The substantive construction proves the bounds and exhaustion
for the complete space on this carrier. The scope remains this example and its
complete synthesis, with local atomicity on both Fourier sides and no additional
polynomial total-variation condition.

## The formal statement

[`Challenge.lean`](Challenge.lean) is the small, independent Mathlib-only
statement of record. Its definitions spell out local finiteness, local atomic
action, the Fourier transform and the complete Meyer subspace.
[`Solution.lean`](Solution.lean) proves the same theorem.

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

The original internal source paths are retained to make the extraction
traceable. Only the recursive import closure of the complete synthesis theorem
is included. The supporting Fourier, interpolation, sampling and Hilbert-space
modules serve this proof;
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
source development, with a module-system and dependency port
and a new Palomar interface. MeyerProblem was consulted as a publication
layout reference for a different theorem; its mathematical result is not
included. Exact citations and automation disclosures are in
[`formalization.yaml`](formalization.yaml).

The source repository records separate agent mathematical, adversarial and
verification reviews of its earlier candidate. Those are historical evidence,
not a review of this new extraction and toolchain port. The current preparation
is AI-assisted; no new independent human review or Palomar acceptance is
claimed.
