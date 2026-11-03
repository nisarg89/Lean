# Preserving contracts across commits

A successful build alone is insufficient: a changed definition could silently
weaken what an unchanged theorem name means. Use three protections together.

## 1. Immutable paper releases

Tag each accepted manuscript release, record the full commit and environment,
and link the paper to that tag/commit. Do not move tags. A current branch may
change, while the old checkout remains reproducible. GitHub branch/tag rules
are configured in the repository settings.

## 2. Rebuild all certified papers

Every pull request runs the catalogue and every registered regression target,
even if only a shared file changed. The matrix uses `fail-fast: false`, so a
failed paper does not cancel another paper's checks. Require the aggregate
`all-certificates` check before merge. This is deliberate; path-only CI can
miss consequences of a shared definition or tactic change.

The catalogue records the target, audit and complete endpoint list. On pull
requests, its guard refuses to remove an existing required regression. Once an
entry is `certified`, the guard also refuses to change its baseline metadata,
endpoint manifest, status or Comparator configuration. An intentional new
specification requires an additional versioned paper entry, not silently
replacing a previously certified contract.

### Incremental work and clean release checks

CI reuses toolchains and the Lake workspace cache, keyed by operating system,
pinned environment, paper and commit. Lake decides which changed modules and
importers need rebuilding; every registered paper still runs its verification
job. The saved build is an accelerator, not evidence that a different source
snapshot is correct. Use the workflow's manual `clean` option for a fresh
package release check, or use a clean server checkout. Mathlib's official cache
may still supply the pinned library artifacts.

The [cache action](https://github.com/actions/cache/blob/main/README.md) is
pinned to its inspected v4.2.4 release commit. Source exports, axioms and
semantic baseline comparisons remain separate verification steps.

## 3. Compare to an immutable semantic baseline

After the first clean repository build and full audit, export the accepted
certificate with the pinned toolchain's `leanexport`. Retain the export as a
release artifact and commit its SHA256 and immutable source commit in baseline
metadata. Do not commit a huge generated environment export to the source tree.

`BFRegression.json` lists **all 47** released endpoints. Its challenge module
is deliberately absent: omitting `--challenge-from-export` must fail rather
than accidentally comparing the current certificate with itself. Lean 4.35's native
Comparator accepts the recorded export as its challenge:

```sh
cd lean
lake comparator --config=ComparatorChallenges/BFRegression.json \
  --challenge-from-export=artifacts/verification/BF/baseline.ndjson
```

Unlike comparing two environments assembled from the same edited definitions,
this compares the new proof environment with the old exported specification.
The implementation checks endpoint types and recursively compares the constants
needed to interpret them. Endpoint proof bodies can change; meanings cannot
silently drift. No definition holes are permitted. The ordinary principal
statement challenge is still useful for independent reading and checking; it
covers ten endpoints and is not a substitute for this 47-endpoint regression.

This comparison is conservative: some meaning-preserving refactors of
interpreting definitions, or library upgrades, can change kernel expressions.
Resolve those in an explicit reviewed new baseline/version, retaining the old
release; do not defeat the checker by redefining its contract in the same PR.
A shared service API can receive the same treatment by registering its exported
public theorem names as a separate regression surface. It need not duplicate
its implementation or expose every private helper as a permanent public API.

## Build status and optional semantic baseline

Implemented in this repository: catalogue, separate target selection, full-catalogue
CI, 47-endpoint audit, 47-endpoint regression configuration, baseline hash
validation/download, Comparator invocation and protection of sealed entries
against the pull request's base commit.

The repository certificate build and 47-endpoint axiom audit passed in
[CI](https://github.com/nisarg89/Lean/actions/runs/41530290076). The catalogue records
`build-and-axiom-audit-passed`. The optional cross-commit semantic baseline
is not configured; Comparator and baseline sealing are separate from those
successful build and axiom checks. The `certified` status additionally requires
a sealed baseline. Branch protection is configured in GitHub settings.

After sealing, the full verification script runs Comparator by default. On a
Mac, use the direct Lake build/audit commands or `--skip-comparator` for a local
component check; that is not a complete release/regression check. The sandboxed
Comparator gate runs on Linux with bubblewrap. No sandbox bypass is recommended.

## Branch protection settings

Require pull requests, required status checks including `all-certificates`,
and review of workflow, catalogue, baseline and public API changes. Apply the
rules to administrators and block force pushes. Limit who can change rules or
move tags. Code in a repository cannot prevent its owner from removing these
protections; the intended guarantee is enforced at the protected merge boundary
and preserved independently by immutable release references.

Official references: [Lake](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/),
[Comparator](https://github.com/leanprover/comparator), and
[protected branches](https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/managing-protected-branches/about-protected-branches).
