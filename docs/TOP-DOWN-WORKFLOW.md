# Writing from contracts

1. Fix the final theorem and every interpreting definition against the manuscript. State its complete quantifiers and output on one witness. For
   algorithms, include the concrete ordinary encoding, actual execution model,
   and one uniform choice of runtime constants.
2. Follow the paper's immediate proof. Give each genuinely needed child a named,
   exact contract. Keep these as explicit parameters or provider-record fields,
   not custom axioms or `sorry` in the proof import graph.
3. Prove the parent from those contracts and check it immediately. If it needs
   another fact, add that fact as a child contract and recheck the parent before
   expanding descendants. Do not generate a large speculative dependency tree.
4. Record the checked source hashes, imported contract versions and status.
   A checked conditional implication is not an implemented provider. Distinguish
   `statement`, `conditional proof checked`, `provider checked`, and `final
   certificate checked` in the roadmap.
5. To implement a child, first look for an existing checked provider with the
   exact required type. Prove a narrow adapter where needed. Compare patching a
   stalled implementation with reconstructing that same component; do not
   silently change the manuscript's mathematical argument.
6. Construct providers one at a time. Recheck the parent after a type change.
   A proof-body change under a stable contract should not require caller redesign,
   although Lake may rebuild affected importers.
7. Once no open providers remain, run the complete paper target and endpoint
   audit in a clean server/CI build, then seal its release baseline.

## What an isolated check establishes

A parent checked against exact types cannot later discover an additional
mathematical premise without that premise having been hidden in an unfinished
child contract or the original encoding having changed. Type checking does
not establish that an unimplemented child is provable. Nor does checking source
against stale compiled imports validate the current source of those imports.

The development roadmap checker records successful source and artifact hashes
and rejects stale roadmap import closures. The future clean build remains the
assembly gate. Standard libraries can supply a fixed checked foundation, while
new provider implementations remain explicitly open until actually checked.

## Avoiding an import-driven roadmap

A missing compiled import is not a new mathematical premise. If a classification
statement imports a library module that also proves normalized circuit reduction
theorems, split its exact definitions into a narrow owner or keep the definition
service explicitly pending. Do not repair hundreds of implementation modules
merely to obtain names for an empty top-level contract. Preserve the meaning and
prove an equivalence when moving between representations.
