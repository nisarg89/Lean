# Developing certificates

Use the [top-down workflow](docs/TOP-DOWN-WORKFLOW.md) for new certificates.

1. Record the manuscript title and exact final statement before writing its
   proof. Use descriptive `snake_case` theorem names and `UpperCamelCase` module
   names; retain existing public names. Group reusable results by mathematical
   subject, with manuscript adapters in the paper namespace.
2. Write a narrow deliverable type and check the parent proof against that type.
   Use explicit provider parameters for unimplemented children in a separate
   roadmap tree. No placeholder proof is allowed in a released certificate.
3. Reuse checked services and search Mathlib and external formalizations before
   implementing a standard external theorem. Record source revisions/licenses.
4. Follow the manuscript argument. Record genuine repairs and authorized
   alternatives in the associated review. Add module docstrings for
   scope and paper correspondence; use short comments for non-obvious proof
   steps rather than narrating routine tactics.
5. Check a small complete component as it is written. Then rebuild all released
   paper targets in CI. An isolated conditional proof proves only the implication
   stated in its type; it does not discharge its assumptions.
6. Preserve public contracts. Improve proof bodies freely, but retain the
   released statements and interpreting definitions or add compatibility names.
   Use the sealed baseline comparison described in `docs/REGRESSION.md`.
7. Keep generated `.lake`, `.elan`, compiled objects, exports and logs out of Git.
   Keep small source provenance, endpoint manifests and accepted release hashes.

## Pull requests

Describe changes to theorem types and definitions explicitly. Routine proof
refactors should not require changing a semantic baseline. New assumptions or
weakened conclusions are not compatibility fixes. A new paper must have a reader
guide, exact statement map, target, audit list and explicit status in
`certificates.json`.

Enable required CI checks and protected branches on GitHub before accepting
shared-library changes. Workflow/registry/baseline changes require careful
review too: a workflow in the same editable branch is not an immutable policy.
