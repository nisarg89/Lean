# Improving Randomized Metric Distortion to 2.1361 in Lean

This certificate formalizes results of *Improving Randomized Metric Distortion
to 2.1361*, by Nisarg Shah. It covers random-size stable lotteries, the paper's
metric-distortion bounds, and its approximation algorithm.

## Formal statements

The principal exports are in [Certificate.lean](./Certificate.lean):

- `MetricDistortion.main_upper_bound`: a randomized voting rule with distortion at most `213609 / 100000` on every nonempty finite profile.
- `MetricDistortion.integer_draw_lower_bound`: for every fixed positive-integer draw distribution, some finite profile makes every stable lottery's distortion strictly greater than `267 / 125`.
- `MetricDistortion.approximation_program` and `MetricDistortion.polynomial_time_corollary`: the approximation program and its bound in the paper's real-arithmetic model.

The [paper certificate](./Certificate.lean) also exports
`MetricDistortion.Certified.Results_ExactStarDistortion` for every stable
lottery of the paper's draw law, `Appendix_MixingCounterexample` for the
fixed-size mixing example, and `Examples_TwoCandidateGap` for the introductory
example. The latter two names are also in the `MetricDistortion.Certified`
namespace.

Shared results appear in the `MetricDistortion.Certified` namespace. The
[stable-lottery certificate](../../Library/Voting/Stable/Certificate.lean) includes
`Stability_Existence`, `Comparison_CandidateDraws`, `Geometry_RankStability`,
`Geometry_Rearrangement`, `Analysis_GeneratingFunction`,
`Comparison_ChallengerLinearity`, `Comparison_FixedDrawSpecialization`, and
`Comparison_MaximalLottery`. The [distortion certificate](../../Library/Voting/Distortion/Certificate.lean)
includes `Geometry_MetricRankCuts`, `Geometry_RankCutCriterion`,
`Offsets_ReductionToOffsets`, and `Offsets_MetricRealization`. Their contracts
state the full hypotheses and conclusions.

The [paper contracts](./Statements.lean) and
[definitions](./Definitions.lean) specify the paper's
witness and computation model. Shared definitions and contracts are organized
under [Voting](../../Library/Voting/), [Stable](../../Library/Voting/Stable/), and
[Distortion](../../Library/Voting/Distortion/). Profiles have strict rankings; metrics
are pseudometrics on the finite voter/candidate union. Draw-law index `k`
represents `k+1` draws.

## Reusing the upper-bound method

[StarCertificate.lean](./StarCertificate.lean) exposes
`MetricDistortion.starLaw`, the paper's specified draw law, and
`MetricDistortion.starCertificate`, its valid witness.
`MetricDistortion.starCertificate_bound` states that the certificate's bound is
exactly `213609 / 100000`; `starCertificate_approximation` gives the additional
approximate-stability condition with constant `16`.

For another draw law, construct a `Voting.Distortion.UpperBoundCertificate` by
providing witness data and a proof of `Voting.Distortion.ValidCut`. Then
`Voting.Distortion.distortion_le_of_certificate` bounds any stable lottery;
`Voting.Distortion.exists_stable_with_distortion_bound` also supplies one on
each nonempty profile. The criterion's current witness has nine indexed
components. A new draw law can require additional proofs of witness validity;
rational witness data alone do not establish the conditions.

## Verification

Install [Elan](https://github.com/leanprover/elan). The repository pins the
Lean toolchain and dependency revisions under [`lean/`](../../lean/). To run
the certificate build, audit coverage and dependency-lock checks, also install
Python 3 and run from the repository root:

```sh
python3 lean/scripts/verify-paper.py RandomSizeMetricDistortion
```

To build the Lean certificate, the paper's concrete witness, and the shared and
paper audits directly:

```sh
cd lean
lake build +RandomSizeMetricDistortion.CertificateAudit +RandomSizeMetricDistortion.StarCertificate +Voting.Audit +Voting.Distortion.Audit
```

The audits check the exported contracts and their transitive axioms. The
permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. The
numerical certificates use exact data and proved soundness results checked by
Lean. Building from source can require substantial computational resources.

Lake reuses artifacts when its build traces match the current inputs; source or
configuration changes can require dependent modules to be rebuilt. A downloaded
build artifact is a trusted compiled import: a checksum identifies its bytes,
but does not independently recheck its proofs. For source verification, build
the paper and shared modules in a fresh checkout without imported project build
artifacts, and choose separately whether to rebuild the pinned dependencies.

### Optional compiled cache

The shared voting and paper caches can be restored from the release assets
`shared-cache-lean-4.35.0.tar` and `metric-cache-lean-4.35.0.tar`. This procedure
was tested on Linux x86-64 with the pinned dependency packages and their compiled
artifacts already available in `lean/.lake/packages`. Other platforms and
dependency setup from scratch have not been tested with these assets.

From the repository root, set `asset_dir` to the absolute path containing both
archives and `SHA256SUMS`, then run:

```sh
asset_dir=/absolute/path/to/downloads
(cd "$asset_dir" && sha256sum -c SHA256SUMS)
cd lean
metric_cache_tmp=$(mktemp -d)
export LAKE_ARTIFACT_CACHE=true
export LAKE_CACHE_DIR="$metric_cache_tmp/cache"
mkdir -p "$metric_cache_tmp/shared" "$metric_cache_tmp/metric"
tar -xf "$asset_dir/shared-cache-lean-4.35.0.tar" -C "$metric_cache_tmp/shared"
tar -xf "$asset_dir/metric-cache-lean-4.35.0.tar" -C "$metric_cache_tmp/metric"
lake cache unstage "$metric_cache_tmp/shared"
lake cache unstage "$metric_cache_tmp/metric"
lake --no-cache --rehash --no-build build Voting +MetricDistortion.StarCertificate +RandomSizeMetricDistortion.CertificateAudit +Voting.Audit +Voting.Distortion.Audit
```

The last command checks whether Lake considers the restored artifacts fresh;
it does not rebuild them. The verification script above can then run the audits.

## License and credits

See the repository's [license](../../LICENSE) and
[third-party credits](../../THIRD_PARTY.md).
