# Balanced Fair Division in Lean

Lean 4 formalization of the **Balanced Fair Division manuscript**, by Benjamin Cookson, Jakob de Raaij, Max Dupré la Tour, and Nisarg Shah.

Arbitrary identical valuations admit balanced EF[1,1] allocations for every positive number of agents; arbitrary heterogeneous valuations admit them for prime-power agent counts. The formalization also covers the sharp swap theorem and the manuscript’s partition and graph applications.

## Formal statements

Balanced allocations have bundle sizes differing by at most one. EF[1,1] allows removing at most one item from each of two compared bundles to eliminate envy.

- [MainTheorems.lean](lean/FairDivision/BF/MainTheorems.lean): principal existence theorems.
- [Definitions.lean](lean/FairDivision/Definitions.lean): allocation and fairness definitions.
- [SwapThreshold.lean](lean/FairDivision/BF/SwapThreshold.lean): the sharp swap theorem.
- [Applications](lean/FairDivision/BF/Applications/): partition and graph results.

## Axioms

The certificate uses only Lean’s standard axioms: `propext`, `Classical.choice`, and `Quot.sound`. The [axiom audit](lean/FairDivision/BF/CertificateAudit.lean) checks all 47 released results.

## Verification

Install [Elan](https://github.com/leanprover/elan) and Python 3. The workspace pins Lean **4.35.0** in [lean-toolchain](lean/lean-toolchain) and library revisions in [lake-manifest.json](lean/lake-manifest.json).

From the repository root:

```sh
python3 lean/scripts/verify-paper.py BF
```

This builds the certificate, audits its axioms, and checks that the dependency lock is unchanged. The published certificate’s [build and audit passed in CI](https://github.com/nisarg89/Lean/actions/runs/41591365027); [CI](https://github.com/nisarg89/Lean/actions/workflows/verify.yml) runs the same checks for changes.

## Proof layout

The [certificate target](lean/FairDivision/BF/Certificate.lean) assembles the manuscript’s proofs. Reusable mathematics is organized under [FairDivision](lean/FairDivision/). [ComparatorChallenges](lean/ComparatorChallenges/) contains independently stated existence results for optional comparison. Each certificate builds its own import closure and reuses shared definitions and proofs.

## License and credits

Original code is licensed under [Apache-2.0](LICENSE). See [third-party credits](THIRD_PARTY.md) for reused libraries and proofs.
