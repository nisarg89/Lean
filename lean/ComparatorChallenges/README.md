# Comparator challenge

The challenge/solution organization follows OpenAI's
[certificate challenges](https://github.com/openai/math/tree/main/lean/ComparatorChallenges).
[`BalancedFairDivision.lean`](BalancedFairDivision.lean) fixes ten existence
statements independently of the BF proof modules.
[`BalancedFairDivision.json`](BalancedFairDivision.json) names the solution,
selected theorems, and permitted axioms. There are no definition holes.

The `sorry` placeholders occur only in this statement challenge. They do
not prove any result and are not imported by the solution. The challenge
imports the shared definition/statement files, whose bodies are part of
the comparison, rather than importing the proof entry point.

## Run the comparison

Our pinned Lean 4.35.0 includes Comparator in Lake. This replaces the
separate `comparator`, `landrun`, and `lean4export` installations used by
OpenAI's older 4.34.1 environment. On Linux with `bwrap` available and
unprivileged user namespaces enabled, run from `lean/`:

```sh
lake exe cache get
lake comparator --config=ComparatorChallenges/BalancedFairDivision.json
```

For the bundled independent kernels as well:

```sh
lake comparator --paranoid --config=ComparatorChallenges/BalancedFairDivision.json
```

See the official [Lean 4.35 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/)
for platform requirements and the relationship between `lake comparator`
and `lake check`. The sandbox is Linux-specific; ordinary building and the
axiom audit are also available on macOS.

## Scope and status

The comparison covers seven `MainTheorems` existence exports and three
stable existence aliases. Swaps and applications are covered by the
separate 47-endpoint [axiom audit](../FairDivision/BF/CertificateAudit.lean),
not by this challenge.

This draft challenge has not yet been compiled or compared. A passing
Comparator log must be recorded before advertising it as independently
checked. A useful release check is to alter a theorem or interpreting
definition **in a disposable copy of the challenge**, confirm comparison
fails, and discard that copy.

Human review concerns whether the final theorem types and definitions say
what the paper means. Comparator checks formal agreement; it does not
perform that mathematical interpretation.

## Cross-commit regression

`BFRegression.json` covers all 47 audited endpoints against a sealed old
environment export, as described in [REGRESSION.md](../../docs/REGRESSION.md).
Always supply `--challenge-from-export`; its intentionally absent challenge
module makes accidental self-comparison fail. This baseline has not been
sealed in the new repository draft.
