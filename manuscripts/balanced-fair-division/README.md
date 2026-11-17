# Balanced Fair Division in Lean

Lean 4 formalization of the Balanced Fair Division manuscript, by Benjamin Cookson, Jakob de Raaij, Max Dupré la Tour, and Nisarg Shah.

The [certificate guide](../BalancedFairDivision/README.md) describes the formal statements, proof layout, and axioms. The [certificate](../BalancedFairDivision/Certificate.lean) assembles the proofs.

Install [Elan](https://github.com/leanprover/elan) and Python 3. From the repository root, build and audit the certificate with:

```sh
python3 lean/scripts/verify-paper.py BF
```

The pinned toolchain and dependencies are in [`lean/`](../../lean/). See the [repository license](../../LICENSE) and [third-party credits](../../THIRD_PARTY.md).
