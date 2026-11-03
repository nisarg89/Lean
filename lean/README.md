# Lean workspace

Certificate for the Balanced Fair Division manuscript. Lean and Mathlib versions
are pinned in `lean-toolchain` and `lake-manifest.json`.

Install [Elan](https://github.com/leanprover/elan), then run from the repository root:

```sh
python3 lean/scripts/verify-paper.py BF
```

This builds the certificate and audits all 47 endpoints.
[Passing checks](https://github.com/nisarg89/Lean/actions/runs/41530290076).

[Statements](../manuscripts/balanced-fair-division/STATEMENTS.md) · [Optional Comparator checks](ComparatorChallenges/README.md)
