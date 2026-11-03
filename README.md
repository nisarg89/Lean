# Lean formalizations

Lean 4 formalizations accompanying mathematical manuscripts, with a shared library of definitions and proofs. Each manuscript has its own reader guide, theorem statements, certificate target, and axiom audit.

## Manuscripts

| Manuscript | Guide | Statements | Identifier |
| --- | --- | --- | --- |
| Balanced Fair Division | [README](manuscripts/balanced-fair-division/README.md) | [Statements](manuscripts/balanced-fair-division/STATEMENTS.md) | `BF` |

## Setup and verification

Install [Elan](https://github.com/leanprover/elan) and Python 3. The workspace pins Lean **4.35.0** in [lean-toolchain](lean/lean-toolchain) and library revisions in [lake-manifest.json](lean/lake-manifest.json).

From the repository root, verify a manuscript using its catalogue identifier:

```sh
python3 lean/scripts/verify-paper.py BF
```

The verifier downloads cached dependencies, builds the selected certificate, audits its released results, and checks that the dependency lock is unchanged. Each target builds its own import closure. Shared definitions and proofs are reused across manuscripts.

[CI](https://github.com/nisarg89/Lean/actions/workflows/verify.yml) checks every manuscript registered in [certificates.json](certificates.json).

## Layout

- [manuscripts/](manuscripts/): manuscript guides and result statements.
- [lean/](lean/): pinned workspace, proof sources, and shared mathematics.
- [lean/scripts/](lean/scripts/): verification tools.
- [docs/](docs/): repository architecture and release policies.

See [contribution guidelines](CONTRIBUTING.md), [architecture](docs/ARCHITECTURE.md), and [regression policy](docs/REGRESSION.md) for development.

## License and credits

Original code is licensed under [Apache-2.0](LICENSE). See [third-party credits](THIRD_PARTY.md) for reused libraries and proofs.
