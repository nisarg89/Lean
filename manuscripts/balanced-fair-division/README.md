# Balanced Fair Division in Lean

Lean 4 formalization of the **Balanced Fair Division manuscript**, by Benjamin Cookson, Jakob de Raaij, Max Dupré la Tour, and Nisarg Shah.

Arbitrary identical valuations admit balanced EF[1,1] allocations for every positive number of agents; arbitrary heterogeneous valuations admit them for prime-power agent counts. The formalization also covers the sharp swap theorem and the manuscript’s partition and graph applications.

## Formal statements

Balanced allocations have bundle sizes differing by at most one. EF[1,1] allows removing at most one item from each of two compared bundles to eliminate envy.

- [STATEMENTS.md](STATEMENTS.md): concise statements of the manuscript’s results.
- [MainTheorems.lean](../../lean/FairDivision/BF/MainTheorems.lean): principal existence theorems in Lean.
- [Definitions.lean](../../lean/FairDivision/Definitions.lean): allocation and fairness definitions.

## Axioms

The certificate uses only Lean’s standard axioms: `propext`, `Classical.choice`, and `Quot.sound`. The [axiom audit](../../lean/FairDivision/BF/CertificateAudit.lean) checks all 47 released results.

## Verification

Follow the [repository setup](../../README.md#setup-and-verification), then run from the repository root:

```sh
python3 lean/scripts/verify-paper.py BF
```

This builds the certificate, audits its axioms, and checks that the dependency lock is unchanged. The [certificate build and audit have passed in CI](https://github.com/nisarg89/Lean/actions/runs/41591365027).

## Proof layout

The [certificate target](../../lean/FairDivision/BF/Certificate.lean) assembles the manuscript’s proofs. [BF/Applications](../../lean/FairDivision/BF/Applications/) contains application theorems; reusable mathematics is organized under [FairDivision](../../lean/FairDivision/).

## License and credits

Original code is licensed under [Apache-2.0](../../LICENSE). See [third-party credits](../../THIRD_PARTY.md) for reused libraries and proofs.
