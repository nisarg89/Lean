# Third-party sources and dependencies

This release contains the Lean certificate accompanying *Balanced Fair Division*.
Original project code is distributed under Apache-2.0; see the repository
`LICENSE` and `lean/LICENSE`. Borrowed sources and external dependencies retain
their own licenses and notices. No claim of authorship of upstream work is made.

The authoritative active pins are `lean/lean-toolchain`,
`lean/lakefile.toml`, and `lean/lake-manifest.json`. The vendored sources below
are part of the proof closure. Dependency sources fetched by Lake are not
vendored in this release.

## Vendored DKGM topology proofs

- Upstream: [akopjan/Dolnikov-Karasev-Gromov-Milman](https://github.com/akopjan/Dolnikov-Karasev-Gromov-Milman).
- Exact revision: `a32fae66a704d736f0c2c3ec9b14afd22979fe9f`.
- License: Apache-2.0, retained verbatim in
  [`lean/third_party/dkgm-topology-source/LICENSE`](lean/third_party/dkgm-topology-source/LICENSE).
- Sources: 14 original proof modules under
  `lean/third_party/dkgm-topology-source/RequestProject/Dvoretzky/`, preserving
  their original module paths, namespaces, and proof bodies.
- Provenance and module inventory:
  [`SOURCE-PROVENANCE.md`](lean/third_party/dkgm-topology-source/SOURCE-PROVENANCE.md)
  and [`UPSTREAM-CLOSURE.json`](lean/third_party/dkgm-topology-source/UPSTREAM-CLOSURE.json).

These sources provide the chain-level cyclic Dold and elementary-abelian
join obstructions reused by the certificate. The upstream toolchain was
Lean `v4.35.0-rc3`, with Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`. The local package configuration
uses the release's stable Lean `v4.35.0` and Mathlib pin listed below. Its
package configuration and entrypoint are local integration metadata; they
are not a second copy of Mathlib. The DKGM license text was compared with
the pinned upstream license and is byte-identical.

## PFR disjoint-coordinate independence excerpt

- Upstream: [teorth/pfr](https://github.com/teorth/pfr).
- Exact revision: `7e7fadf0c4d000fdb21b68505f3fd0e29a6e4a2f`.
- Original file:
  [`PFR/Mathlib/Probability/Independence/Kernel/IndepFun.lean`](https://github.com/teorth/pfr/blob/7e7fadf0c4d000fdb21b68505f3fd0e29a6e4a2f/PFR/Mathlib/Probability/Independence/Kernel/IndepFun.lean).
- Local adapted source:
  [`lean/FairDivision/Probability/FiniteDisjointBlocks.lean`](lean/FairDivision/Probability/FiniteDisjointBlocks.lean).
- License: Apache-2.0, retained verbatim in
  [`lean/third_party/pfr-probability-source/LICENSE`](lean/third_party/pfr-probability-source/LICENSE).

The grouped-independence proof is retained, with its module/import exposure
header adapted and measure-level wrappers added locally. The local file's
header records its upstream repository, revision, source path, license, and
adaptation. The original source header at this revision has no additional
copyright or author banner. The PFR license text was compared with the pinned
upstream license and is byte-identical. The full PFR project is not included
or required.

## Lean and Mathlib

| Component | Exact active pin | License | Source |
|---|---|---|---|
| Lean 4 | `leanprover/lean4:v4.35.0` | Apache-2.0 | [leanprover/lean4](https://github.com/leanprover/lean4/tree/v4.35.0) |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` | Apache-2.0 | [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679) |

Lean is installed through its pinned toolchain. Mathlib is fetched by Lake;
its original license and source notices remain in the fetched package,
including `lean/.lake/packages/mathlib/LICENSE`. The Lean distribution
retains its own license and bundled-component notices. This repository does
not redistribute a Lean toolchain or compiled Mathlib cache.

## Mathlib companion packages

The companion pins below match the accepted Mathlib dependency lock and are
also explicit in the release's Lake configuration. They are fetched rather
than copied into this source release. Each fetched package retains its
original `LICENSE` and any source notices; these are available under
`lean/.lake/packages/<package>/` after dependency retrieval.

| Package | Repository | Exact revision | License |
|---|---|---|---|
| plausible | [leanprover-community/plausible](https://github.com/leanprover-community/plausible) | `dfa4f38190d07c37e315953e08b90fe2d95b3c24` | Apache-2.0 |
| LeanSearchClient | [leanprover-community/LeanSearchClient](https://github.com/leanprover-community/LeanSearchClient) | `d6b4c7be5be75ec4917c873ac50c756dc1436372` | Apache-2.0 |
| importGraph | [leanprover-community/import-graph](https://github.com/leanprover-community/import-graph) | `a41f0e9a4dea23188ea9cc1c41ac9f8bbafe0b93` | Apache-2.0 |
| proofwidgets | [leanprover-community/ProofWidgets4](https://github.com/leanprover-community/ProofWidgets4) | `df72b022e558978a1c50264cfc4d7fec86fa8e04` | Apache-2.0 |
| aesop | [leanprover-community/aesop](https://github.com/leanprover-community/aesop) | `4a174c490d8707121c4a9290800489f105d85e07` | Apache-2.0 |
| Qq | [leanprover-community/quote4](https://github.com/leanprover-community/quote4) | `dce0ad79c486cb1fb504af04f953c3466b0c6db8` | Apache-2.0 |
| batteries | [leanprover-community/batteries](https://github.com/leanprover-community/batteries) | `66e469188fe07963e5cf666c7d4433f45b8131c5` | Apache-2.0 |
| Cli | [leanprover/lean4-cli](https://github.com/leanprover/lean4-cli) | `c24fe6078c630e89b489bffe59b3e20ac30d12c8` | MIT |

The fetched Cli license includes the notice `Copyright (c) 2021 mhuisi`.
Its MIT terms remain applicable to that dependency. The project's Apache-2.0
license does not replace any third-party license or notice.
