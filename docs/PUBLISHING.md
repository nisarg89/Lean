# Publishing certificate releases

The certificate for the Balanced Fair Division manuscript is published in
`nisarg89/Lean`. The steps below describe tagged certificate releases.

## Before publishing a verified release

1. Check the BF statement map and scope against the final manuscript.
2. Run the certificate build and full endpoint audit on the server or CI.
   The current repository build and 47-endpoint audit have passed in
   [GitHub Actions](https://github.com/nisarg89/Lean/actions/runs/41530290076).
3. Run the independent principal statement Comparator on Linux:

   ```sh
   cd lean
   lake comparator --config=ComparatorChallenges/BalancedFairDivision.json
   ```

4. Commit the checked source tree before preparing its semantic baseline.

5. From that clean committed source tree, prepare a semantic baseline export:

   ```sh
   python3 lean/scripts/prepare-baseline.py BF \
     --artifact-url https://github.com/nisarg89/Lean/releases/download/bf-v1.0.0/baseline.ndjson
   cd lean
   lake comparator --config=ComparatorChallenges/BFRegression.json \
     --challenge-from-export=artifacts/verification/BF/baseline.ndjson
   ```

   This export covers 47 endpoints. It includes generated environment data, so
   keep it as a release artifact, not a tracked source file. Preparation does
   not substitute for the preceding build/audit and comparison.

6. Copy the generated metadata to `contracts/BF-v1.json`, set BF's catalogue
   `semantic_baseline` to that path and status to `certified`, then commit the
   metadata. Its `source_commit` identifies the preceding verified proof tree;
   this metadata commit need not alter proof sources. Upload the export under the filename `baseline.ndjson` at its exact
   recorded URL. A draft release is private to maintainers; for the anonymous
   download check, make the release a public prerelease clearly marked
   verification-pending. Run `verify-paper.py BF` against that uploaded hash.
7. Enable required pull-request checks and protected branches/tags as described
   in `REGRESSION.md`, push, and require the full CI result. After success,
   publish the release and tag the accepted metadata/source state as
   `bf-v1.0.0`. Avoid claiming a tag is verified before its checks finish.
8. Link the manuscript to the tag's reader guide, e.g.
   `https://github.com/nisarg89/Lean/tree/bf-v1.0.0/manuscripts/balanced-fair-division`.
   Record the full commit in the release notes and optional citation metadata.

Never move a published tag. For updates use a new tag. New papers add targets
and reader entries; previously certified targets remain in every regression
run. Do not commit `.lake`, `.elan`, logs, NDJSON exports or archives.

## Common commands after publication

```sh
git clone https://github.com/nisarg89/Lean.git
cd Lean
git checkout bf-v1.0.0
python3 lean/scripts/verify-paper.py BF
```

Readers can instead use the direct Lake commands in the BF guide. Those do not
require the repository's catalogue machinery and compile only BF's imports.
