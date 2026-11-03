# Dolnikov–Karasev–Gromov–Milman topology source port

- Repository: https://github.com/akopjan/Dolnikov-Karasev-Gromov-Milman
- Exact upstream revision: `a32fae66a704d736f0c2c3ec9b14afd22979fe9f`.
- License: Apache-2.0, upstream contributors; full original text is `LICENSE`.
- Requested proof roots: `RequestProject.Dvoretzky.ElemAb.Main` and
  `RequestProject.Dvoretzky.Dold.Main`.
- `UPSTREAM-CLOSURE.json` records the complete recursive project-local import
  closure: 14 original Lean modules, each fetched from the pinned raw GitHub
  source. Their only other import is `Mathlib`.

## Active package and upstream pins

The original proof sources are copied without mathematical or textual edits.
`UPSTREAM-lean-toolchain`, `UPSTREAM-lakefile.toml`,
`UPSTREAM-lake-manifest.json`, `UPSTREAM-README.md`, and `UPSTREAM-LICENSE`
preserve the exact fetched metadata. The original toolchain and manifest pin
Lean `v4.35.0-rc3` and Mathlib commit
`c55e6e786f49471c72fbddbec5415808896aec1e`. The upstream README's statement
that its version is stable 4.35 does not override those literal pins.

This portable local source package uses the certificate's stable Lean
`v4.35.0` and Mathlib `v4.35.0` (root manifest commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`). The only new source entrypoint is
`RequestProject.lean`, importing the two theorem roots. The active package
name is `dkgm_topology_source`; original module paths and theorem namespaces
remain unchanged. No upstream Challenge/Solution targets, cache, toolchain,
build output, or second Mathlib copy is included.

The source port has since passed compilation as part of the complete BF
certificate on stable Lean 4.35.0, including the successful
[repository build and endpoint audit](https://github.com/nisarg89/Lean/actions/runs/41530290076).
The historical component checkpoints below predate that full build.

## Reused mathematical endpoints

- `Dvoretzky.ElemAb.elemAb_join`: no equivariant map from an N-fold join of
  the elementary abelian 2-group to a join of D+1 nontrivial real character
  0-spheres when `D+1<N`.
- `Dvoretzky.Dold.dold_join`: the corresponding cyclic-prime no-map theorem
  between free group joins.

These theorems do not assert the general odd-prime, higher-rank Volovikov
obstruction. The local BF adapters must prove their actual source and target
identifications and respect the literal right-translation action.


## Historical component validation — 1 November 2026

Under the later authorized repair phase, the exact staged Algebra/Chains
modules for Dold, ElemAb.Algebra, and Statement now have focused passes on
stable4.35. The separate optional BF/ExternalObstructionCoreAudit prints
sixteen actual support theorem axiom sets, all limited to propext,
Classical.choice, Quot.sound. The full continuous-to-chain theorem roots
and BF adapters are still pending; this supersedes the historical no-check
status above only for those named modules. No original upstream proof body
has been edited by this checkpoint.


The subsequent named checks also passed all ten remaining original modules,
including Dold.Main and ElemAb.Main: all fourteen original pinned source
modules now have focused stable4.35 passes with unchanged proof bodies.
Local BF source/target/tensor adapters and their final audits remain separate
work; this does not establish Volovikov or either manuscript certificate.
