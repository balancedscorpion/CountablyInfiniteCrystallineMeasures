# Palomar publication procedure

Requirements were checked on 2026-09-28 against the
[submission standard](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md),
[specification](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/docs/specification.md),
and [agent submission protocol](https://submit.palomar-registry.org/llms.txt).
Policy and the minimum toolchain may change; recheck before submitting a later
snapshot. The prepared workflow pins PalomarSubmission to
`65f0154ed776cd26c224254aa57b379137f28b0d`.

## Repository requirements

- A public GitHub repository and one complete 40-character commit SHA.
- A root Lean project with exactly one Lakefile, a matching toolchain and
  immutable public Git dependency pins in the committed manifest.
- A module header in every project Lean source; at most 10,000 physical lines
  per file. Challenge has stricter limits of 1,000 lines and 100 KiB.
- A Mathlib-only Challenge, a separate proved Solution and one Comparator
  configuration selecting the exhaustive cardinal theorem.
- One conventional MIT license file, matching `project.license`.
- Structured authorship, responsible maintainer, mathematical source,
  classification, automation, review, scope and limitation metadata.
- No submodules, LFS pointers, Lean-source symlinks or committed build outputs.

`python3 scripts/check.py` checks the local repository conditions and the final
theorem's axiom report. This is a preparation check, not the full Palomar
verifier. The root README explains the mathematical content, intended research
audience, local atomic meaning, lack of a strong total-variation hypothesis,
classical construction and absence of a novelty claim.

## Verification and submission

1. Finish the local build and checks. Commit the complete source and metadata.
2. Make `balancedscorpion/CountablyInfiniteCrystallineMeasures` public and push
   the reviewed snapshot. Public visibility is required for Palomar to fetch
   and preserve the source. Check that the recorded commit is available.
3. Dispatch the **Palomar mechanical preflight** workflow with that exact SHA.
   It calls Palomar's pinned reusable verifier with `mode: full` and
   `execution_profile: palomar-standard-v1`; configuration is `comparator.json`.
   The caller uses the required twelve-character alphanumeric request ID and
   records authorization from the confirmed responsible maintainer.
   Retain the run URL and mechanical report. Proceed only when its status is
   `pass`. A build, axiom report or standalone Comparator run is insufficient.
4. Before intake, confirm the repository, exact SHA, configuration and the
   submitter's authorization relationship. The responsible-maintainer answer
   concerns the person, not merely possession of GitHub push permissions.
5. Follow the documented agent tag/gist protocol or let the human use the
   browser flow. Do not automate the human sign-in. Review the private
   editorial report once verification completes.
6. Permanent registration is a separate decision after the user sees the
   review. It publishes the exact statement, dependency information, source
   provenance and review in an ordinarily append-only registry. Preparation
   of this repository does not constitute registration.

The automated review is not human peer review, proof of novelty or endorsement.
Do not describe this repository as registered or Palomar-verified before the
corresponding exact-commit reports and registry record exist.
