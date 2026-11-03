# Verification

The complete certificate build and all 47 endpoint axiom checks
[passed in CI](https://github.com/nisarg89/Lean/actions/runs/41530290076).
The audit permits only `propext`, `Classical.choice` and `Quot.sound`.

From the repository root:

```sh
python3 lean/scripts/verify-paper.py BF
```

[Setup](../README.md) · [Optional Comparator checks](../ComparatorChallenges/README.md) · [Regression policy](../../docs/REGRESSION.md)
