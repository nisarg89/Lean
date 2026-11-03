# Repository architecture

## Recommended initial arrangement

Use one repository, one coherent pinned Lean workspace, and one explicit
certificate target per manuscript. This follows the root documentation plus
`lean/` workspace and statement-challenge organization used by OpenAI/math.
The paper catalogue, regression CI and release policy add protections needed
for this repository's long-lived shared library.

```text
Lean/
  README.md  LICENSE  CONTRIBUTING.md  certificates.json
  manuscripts/
    balanced-fair-division/   README, statement map, citation
    <future-paper>/          independent reader entry and statement map
  lean/
    lean-toolchain  lakefile.toml  lake-manifest.json
    FairDivision/            existing checked names, preserved unchanged
      Definitions.lean      common fair-division definitions
      BF/Certificate.lean   BF proof import closure
      BF/CertificateAudit.lean
    # Future, when needed: Shared/<Subject>/ and Papers/<PaperName>/
    ComparatorChallenges/   statements separated from proof modules
    scripts/                build, audit and regression tools
    third_party/            licensed source excerpts and provenance
    verification/           accepted historical evidence and endpoint lists
  contracts/                immutable-release baseline metadata
  docs/                     repository, API and release policies
  .github/workflows/        regress every registered certificate
```

`Shared` and `Papers` are future conventions, not empty directories shipped in
the BF release and not a request to rename the
already checked `FairDivision.*` modules. Existing proofs and definition owners
retain their names. New manuscripts may import those lemmas directly. When a
future generalization deserves a different owner, add a new theorem and retain
compatibility declarations for existing users; avoid duplicating proofs.

## Imports and build boundaries

* Shared modules import libraries and lower shared modules, never a paper's
  final certificate facade. Existing reusable FairDivision modules can remain
  where they are until there is a concrete reason to extract them.
* A paper's statement surface imports only interpreting definitions and types
  that are needed to state its results. It must not import its proof closure.
* Its `Certificate` module imports exactly the modules delivering its released
  claims. Its audit names the entire released endpoint list.
* A reader runs `lake build +<paper>.Certificate`. Lake follows imports. It does
  not build another paper merely because its sources share the workspace.
* Do not introduce a default facade importing every manuscript. The historical
  BF facade remains BF-only. Build-all is a CI operation over the catalogue.
* Definitions used by two papers have one owner and are imported by both.
  Statement challenges may restate a theorem; that is deliberate independent
  specification, not a duplicate proof certificate.

Creating a second `lean_lib` is not by itself an isolation guarantee: imports
are the actual dependency boundary. Conversely, a single library can contain
separate explicitly selected module targets. The repository keeps the checked BF
module names and avoids decorative adapters.

## A gradually growing library

The initial GitHub contents are BF-only: its accepted proof closure, the shared
code it uses, reader material and verification/repository infrastructure. FE
roadmaps and unfinished proof work remain in the development workspace and are
not published in this initial repository. When FE is complete, add its own code
and only the additional shared machinery it needs. Register its certificate
after its final statements are reviewed, full target checked and audit accepted.
The BF target and regression baseline remain in place throughout.

Each shared service must have a documented, explicit type. Callers prove their
composition using that exact type before the service implementation expands.
A checked provider record is an interface, not evidence that the provider exists.
Changing a service type requires either a compatibility theorem or a new name.
Do not make downstream papers silently adapt to a weaker meaning.

## Toolchain upgrades

Initially all papers use the same pinned toolchain and lockfile. Upgrade them
in a dedicated change and rebuild every certified target. Keep the previous
release tags. If two future manuscripts cannot reasonably share a toolchain,
introduce versioned workspaces under `workspaces/`, each using a pinned shared
package revision. This adds maintenance cost and should follow demonstrated
incompatibility rather than be imposed on the first release.

## Reader verification burden

The human checks each released final theorem's interpretation: quantifiers,
valuation domain, feasibility and fairness/efficiency definitions, exceptional
cases, algorithm output, computational model and runtime guarantee. Everything
needed to interpret those claims is in scope. They do not need to compare
intermediate proofs to the paper or separately validate the natural-language
interpretation of every internal KKM/Volovikov lemma. Lean checks the actual
composition. An assumed provider, custom axiom or `sorry` would change that
conclusion, so conditional roadmap results remain clearly separate.
