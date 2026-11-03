import FairDivision.BF.MainTheorems
import FairDivision.BF.Existence
import FairDivision.BF.MonotoneFairness
import FairDivision.BF.SwapThreshold
import FairDivision.BF.ReplacementFairnessExistence
import FairDivision.BF.Applications.Capacities
import FairDivision.BF.Applications.DensityExistence
import FairDivision.BF.Applications.Coverage
import FairDivision.BF.Applications.EqualParametersGraphs

/-!
# Balanced-EF1 manuscript certificate source

The BF reader target covers the existence results, sharp swap threshold and
supporting applications of the Balanced Fair Division manuscript. Imports
contain the BF proofs and their shared mathematics.

Principal final theorem types are collected in `BF/MainTheorems`. The
remaining imported facades expose the exact swap threshold, monotonicity
corollaries, replacement fairness, saturated equal capacities, sharp density
partitions, nonlinear discrepancy, sparse coverage, and equal-parameter
induced-subgraph results. Shared proofs occur once in the import closure.

The complete assembled target has passed the certificate build and endpoint
axiom audit. Challenge placeholders and axiom-printing modules are separate
from its imports. Human semantic review concerns final types and their
interpreting definitions; intermediate encodings and proof agreement are
not additional correctness-review obligations.
-/
