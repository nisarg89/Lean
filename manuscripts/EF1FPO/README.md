# A Polynomial-Time Algorithm for Fair and Efficient Allocation of Indivisible Goods

The theorem `EF1FPO.ef1_fpo_polynomial` states that one deterministic program computes a complete EF1 and fractionally Pareto optimal allocation in time polynomial in the binary input length. It allows any positive number of agents, any finite number of goods, and nonnegative rational additive values, including zeros. [Headline theorem](./Certificate.lean)

The input explicitly lists the agents, goods, and valuation table. Natural-number fields and the reduced numerator and denominator of each rational have self-delimiting binary encodings. The output gives the original agent and good counts, followed by one owner per good in input order. The program runs on a finite collection of binary stacks. Its polynomial clock covers the complete computation, including evaluations of the logarithmic map used to find supporting weights. [Encodings and time model](./Computation.lean)

EF1 requires that for each ordered pair of agents with a nonempty second bundle, some good can be removed from the second bundle so that the first agent values her own bundle at least as highly as the remainder. Fractional Pareto optimality rules out a weak improvement for everyone and a strict improvement for someone, even when goods can be divided into arbitrary nonnegative real shares. Both guarantees use the original input valuations. [Allocation and fairness definitions](./Model.lean)

## Reading the proof

| Question | Lean source |
| --- | --- |
| Why do the price inequalities imply EF1 and fPO, and how can two supported allocations be combined? | [Prices](./Prices.lean) |
| Why does a single allocation cover every agent at the greatest feasible weights? | [Weights](./Weights.lean) |
| How does an approximate fixed point determine the exact highest bidders? | [Geometry](./Geometry.lean) |
| How are the original guarantees preserved when the instance is perturbed and private goods are added? | [Preparation](./Preparation.lean) |
| How is a fixed point of an order-preserving contraction approximated in polynomial bit time? | [Contraction driver](./ContractionDriver.lean) |
| Where are the polynomial-time programs for preparation, exact weight recovery, forest rounding and original-owner recovery? | [Allocation stages](./Algorithm.lean) |
| Which programs evaluate logarithms, compute dyadic approximations of the map, and identify the highest-bidder graph? | [Logarithms](./LogDeployment.lean) · [Map evaluation](./EvaluationDeployment.lean) · [Fixed-point approximation and graph identification](./GraphDeployment.lean) |
| How do the stages form a single program on the original binary input? | [Program composition](./Pipeline.lean) |

The contraction driver uses the finite sign-recovery program and correctness proofs from OpenAI's *Strongly polynomial linear programming*. Monotonicity lets the driver compare one fixed-point coordinate with a threshold using the sign program. Repeated comparisons recover the requested dyadic approximation. The closed allocation program supplies its own evaluator. [OpenAI source at the pinned revision](https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Optimization/LinearProgramming/PriceGame)

## Reproducing the certificate

With Python 3, Git, and elan installed, run the following from the root of this repository. Lake uses the Lean version and dependency revisions pinned under `lean/`.

```sh
python3 lean/scripts/verify-paper.py EF1FPO
```

The endpoint audit checks the transitive axioms of `EF1FPO.ef1_fpo_polynomial`. The allowed list is `propext`, `Classical.choice`, and `Quot.sound`. For the source build alone, run the following from the repository root.

```sh
cd lean
lake build +EF1FPO.Certificate
```

### Restoring the compiled proof

The optional cache contains the 458 compiled modules used by `EF1FPO.Certificate` in this repository. To use it, check out the source revision accompanying the cache and download `ef1-fpo-cache-lean-4.35.0-linux-x86_64.tar` and `SHA256SUMS` together. Release downloads are listed on the [GitHub Releases page](https://github.com/nisarg89/Lean/releases).

The restore procedure is for Linux x86-64 with Lean 4.35.0. It requires the nine packages pinned in `lean/lake-manifest.json`, including Mathlib, with their compiled artifacts available under `lean/.lake/packages/`. The archive's SHA-256 digest is `981937f7415a61d9ef268f11525b9df14cedf57ed7dbca5f35dcabef4761dbf9`.

From the repository root, set `asset_dir` to the absolute path of the directory containing both downloads, then run the following.

```sh
asset_dir=/absolute/path/to/downloads
(cd "$asset_dir" && sha256sum -c SHA256SUMS)
cd lean
ef1_cache_tmp=$(mktemp -d)
export LAKE_ARTIFACT_CACHE=true
export LAKE_CACHE_DIR="$ef1_cache_tmp/cache"
mkdir "$ef1_cache_tmp/stage"
tar -xf "$asset_dir/ef1-fpo-cache-lean-4.35.0-linux-x86_64.tar" -C "$ef1_cache_tmp/stage"
lake cache unstage "$ef1_cache_tmp/stage"
lake --no-cache --rehash --no-build build +EF1FPO.Certificate
python3 scripts/verify-paper.py EF1FPO --skip-cache
```

The `--no-build` command checks that Lake can use the restored certificate without compiling it. The final command reads the audit from source and checks the headline theorem's transitive axioms against the allowed list. To check the proof from source independently, use the source-build instructions above in a fresh checkout.
