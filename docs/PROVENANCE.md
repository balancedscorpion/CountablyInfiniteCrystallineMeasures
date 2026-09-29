# Extraction and statement correspondence

The substantive source is
[MeyerGeneralProblem at aad158a9f4ba3c4db52385ef1856a918edc22c83](https://github.com/ls558/MeyerGeneralProblem/tree/aad158a9f4ba3c4db52385ef1856a918edc22c83).
Original source bytes were read from that commit, not from uncommitted working files.
The source repository was private when this package was prepared. Its pinned
links identify the source for people with access, but are not publicly
verifiable citations. This publication includes the substantive Lean proof;
the private source and its review records are not required to build it.
The selected claim is `target-cardinal-closure`, statement version 1, contract
`sha256:02d8c18d9acada486a25df5faa90c01491b0160c8a1133c5f93c0e87517363ca`.

The informal source is the retained
[cardinal composition](https://github.com/ls558/MeyerGeneralProblem/blob/aad158a9f4ba3c4db52385ef1856a918edc22c83/attempts/target-cardinal-closure/attempt-countable-cardinal-target-composition/artifacts/TARGET_COMPOSITION.md),
together with its adaptive reciprocal construction prerequisites. The later
[formal source correspondence](https://github.com/ls558/MeyerGeneralProblem/blob/aad158a9f4ba3c4db52385ef1856a918edc22c83/lean/docs/adaptive-cardinal-source-correspondence.md)
and
[formal evidence manifest](https://github.com/ls558/MeyerGeneralProblem/blob/aad158a9f4ba3c4db52385ef1856a918edc22c83/evidence/evidence-lean-adaptive-cardinal-formal/manifest.json)
record the Lean implementation and historical assurance. The earlier
composition report alone is a source audit, not the later formal verification.
Historical review results must not be attributed to this port.

The extracted entry point is
`MeyerGeneralProblem.Cardinal.Adaptive.ConstructedAlgebraicBasis`.
Its selected recursive project import closure is retained with original paths
and namespaces. The unused alternative layer-rank proof and general cardinal
trichotomy, and the unused strong-total-variation comparison theory, were removed from this extraction; the direct exhaustive-generator
proof of countable rank is retained. `docs/extraction.json` lists original source hashes. Necessary
changes are module headers, public imports and exposed definitions, visibility
of helpers referenced by exposed definitions, and repairs for the newer
library APIs. Private `import all` directives give the port explicit access to
pinned library implementation details that the old non-module code unfolded.
The new Challenge and Solution are publication interfaces.
Solution locally disables the additional complex C*-algebra instance introduced
by its proof imports, so both interfaces elaborate the topology on ℂ through
the same normed-field instance. This changes no mathematical definition; it
preserves the structural identity required by Comparator.

| Publication object | Source correspondence |
| --- | --- |
| `LocallyFinite Λ` | `LocallyFiniteCarrier.finite_inter_Icc` |
| `LocallyAtomic Λ T` | `HasLocallyAtomicAction S T`, with `S.carrier = Λ` |
| `atomicSpace Λ` | `AtomicOnCarrier S`: annihilating the full Schwartz vanishing ideal |
| `meyerSpace Λ` | `DistributionalMeyerSpace S`, by the proved local/global atomic equivalence on both Fourier sides |
| Complete generator span | `constructedGenerator_span_eq_meyer` |
| Finite synthesis and uniqueness | `constructedGeneratorSynthesisEquiv` and `constructedGenerator_linearIndependent` |
| Rank ℵ₀ | `constructedMeyerRank_eq_aleph0_via_synthesis` |
| Indexing by ℕ | Reindexing the countably infinite type `ℕ+ × ReciprocalSign` |

MeyerProblem at
[`8aa99c16d2733debd1fac67353b0206802ee52bb`](https://github.com/balancedscorpion/shifted-square-root-fourier-classification/tree/8aa99c16d2733debd1fac67353b0206802ee52bb)
was reviewed for its Challenge/Solution separation, provenance disclosures and
scope presentation. Its older toolchain and submission format are not treated
as current policy. It proves a different shifted-square-root result and is
not a proof dependency here.

Human authorship, maintainer and MIT licensing for this extraction were
confirmed by Jamie Martin during preparation. The source development used AI
systems for mathematical research, implementation and agent review. The exact
model identity of every historical contribution has not been independently
reconstructed. Current extraction, porting, documentation and checks were
performed with OpenAI Codex (GPT-6). These automated roles confer no authorship
or claim of independent human review.
