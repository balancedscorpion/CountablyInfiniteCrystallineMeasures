# Repository scope

Don't use env vars unless it really is the best solution.

This repository is solely for the exhaustive countably infinite Hamel-dimension
claim for a complete distributional Meyer space. Preserve its local atomic and
distributional-tempered meaning, same-carrier quantifiers, finite coefficient
interpretation and exhaustiveness. Do not add the arbitrary-carrier programme,
special-family classifications, historical attempts or unrelated results.

Keep Challenge independent of project imports and Solution independent of
Challenge. Do not add proof holes, custom axioms, native-decision dependencies
or weakened statements to make verification pass. Changes to the theorem must
be reflected in both interfaces, the README and formalization metadata.

Run `lake build Challenge Solution`, `python3 scripts/check.py`, and
`git diff --check`. Distinguish local verification from the pinned Palomar full
workflow and permanent registry registration.
