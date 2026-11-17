# Voting in Lean

This library provides reusable definitions and theorems for finite preference
profiles, random-size stable lotteries, and metric distortion.

- [Voting.lean](../Voting.lean) exposes `Voting.Ranking`, `Profile`, `Lottery`,
  `Rule`, and basic preference and lottery operations.
- [Stable.lean](Stable.lean) exposes `Voting.Stable.DrawLaw`, `IsStable`,
  `IsApproxStable`, `exists_stable`, and other stable-lottery results. Draw-law
  index `k` represents `k+1` draws.
- [Distortion.lean](Distortion.lean) exposes `Voting.Distortion.UpperBoundCertificate`,
  `distortion_le_of_certificate`, and `exists_stable_with_distortion_bound`.
  A certificate includes witness data and a proof that they satisfy `ValidCut`.
  The [full criterion](Distortion/Certificate.lean) also supplies an
  approximate-stability cost bound.
- [Audit.lean](Audit.lean) and [Distortion/Audit.lean](Distortion/Audit.lean)
  check public results and their transitive axioms.

The [randomized metric-distortion paper](../../manuscripts/RandomSizeMetricDistortion/)
provides a concrete draw law and verified witness. To study a different law,
provide a valid witness for that law; numerical data alone do not prove validity.
The present rank-cut witness format uses nine indexed components.

Install [Elan](https://github.com/leanprover/elan); the toolchain and dependency
revisions are pinned in [`lean/`](../../lean/). From `lean/`, check the shared
exports with:

```sh
lake build +Voting.Audit +Voting.Distortion.Audit
```

Lake can reuse matching build artifacts; changed sources or configuration can
require dependent modules to rebuild. Downloaded compiled artifacts are trusted
imports, so use a fresh source build when independent checking is required.
