# Balanced Fair Division in Lean

Lean 4 formalization of *Balanced Fair Division* by Benjamin Cookson, Jakob de Raaij, Max Dupré la Tour, and Nisarg Shah.

The paper asks when indivisible items can be divided into bundles of nearly equal size while controlling envy. The [Lean certificate](../BalancedFairDivision/Certificate.lean) assembles the existence theorems, the sharp swap result, and the applications.

## What Lean verifies

In a **balanced** allocation, bundle sizes differ by at most one. **EF[1,1]** means that envy between two bundles can be eliminated by removing at most one item from each. The precise notions are in [Definitions.lean](../../Library/FairDivision/Definitions.lean).

| Result | Guarantee | Lean source |
| --- | --- | --- |
| Identical valuations | A balanced EF[1,1] allocation exists for every positive number of agents. | [MainTheorems.lean](../BalancedFairDivision/MainTheorems.lean) |
| Heterogeneous valuations | A balanced EF[1,1] allocation exists for every prime-power number of agents. | [MainTheorems.lean](../BalancedFairDivision/MainTheorems.lean) |
| Size-preserving swaps | Every equal-size allocation is $t$-swap envy-free when each bundle has at most $2t$ items. Larger bundles admit counterexamples. | [SwapThreshold.lean](../BalancedFairDivision/SwapThreshold.lean) |
| Bounded value spread | If adding an item changes the value by at most $L$, a balanced partition has spread at most $2L$, or $L$ for monotone functions. Both bounds are sharp. | [Existence](../BalancedFairDivision/Applications/NonlinearDiscrepancy.lean) and [sharpness](../BalancedFairDivision/Applications/DiscrepancySharpness.lean) |
| Graph densities | Balanced partitions attain sharp bounds on the spread of induced-subgraph densities. | [DensityExistence.lean](../BalancedFairDivision/Applications/DensityExistence.lean) |
| Equal graph parameters | Disjoint induced subgraphs of the prescribed order can have equal clique, independence, or chromatic numbers. | [EqualParametersGraphs.lean](../BalancedFairDivision/Applications/EqualParametersGraphs.lean) |

The [applications](../BalancedFairDivision/Applications/) also cover equal capacities and coverage. The [axiom audit](../BalancedFairDivision/CertificateAudit.lean) checks all 47 released results and reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Verification

### Build and audit from source

Install [Elan](https://github.com/leanprover/elan) and Python 3. The workspace pins Lean **4.35.0** in [lean-toolchain](../../lean/lean-toolchain) and library revisions in [lake-manifest.json](../../lean/lake-manifest.json).

From the repository root:

```sh
python3 lean/scripts/verify-paper.py BF
```

The command builds the certificate, runs the axiom audit, and checks the dependency lock. The earlier repository layout also passed its [build and audit in CI](https://github.com/nisarg89/Lean/actions/runs/41591365027).

### Download the compiled cache

The [Balanced Fair Division GitHub release](https://github.com/nisarg89/Lean/releases/tag/balanced-fair-division-932c28c) includes the shared FairDivision cache, the paper cache, `SHA256SUMS`, and restore instructions. The restore test used Linux x86-64, Lean 4.35.0, and the pinned dependency artifacts. Lake uses the archives as trusted compiled imports.

## Proof layout

- [Topology](../BalancedFairDivision/Topology/) and [Finite](../BalancedFairDivision/Finite/) contain supporting steps of the paper’s argument.
- [Applications](../BalancedFairDivision/Applications/) contains the partition and graph proofs.
- [Library/FairDivision](../../Library/FairDivision/) contains reusable definitions and results.
- [ComparatorChallenges](../../lean/ComparatorChallenges/) contains independently stated existence results for optional comparison.

The existing `FairDivision.BF.Certificate` import continues to work as a compatibility entry point.

## License and credits

Original code is licensed under [Apache-2.0](../../LICENSE). See [third-party credits](../../THIRD_PARTY.md) for reused libraries and proofs.
