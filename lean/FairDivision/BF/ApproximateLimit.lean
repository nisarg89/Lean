import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The manuscript's compact subsequence limit

Choose tolerance 1/(k+1), retain the actual approximate auxiliary points,
and take one convergent subsequence in their compact finite-coordinate
space. Every continuous owner/position value converges along that SAME
subsequence, its tolerances tend to zero, and closed inequalities give all
exact comparisons at its limit. No maximum-gap minimization is used.
-/

set_option autoImplicit false

namespace FairDivision.BF

open Filter
open scoped Topology BigOperators Classical

/-- Uniformly approximate envy comparisons on a compact set imply exact
comparisons at one point. -/
theorem exists_exact_comparisons_of_approximate
    {n : ℕ} (hn : 0 < n)
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    (K : Set X) (hK : IsCompact K)
    (value : X → Fin n → Fin n → ℝ)
    (hval : ∀ i j : Fin n, Continuous (fun x => value x i j))
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ x ∈ K, ∀ i j : Fin n,
        value x i j - ε < value x i i) :
    ∃ x ∈ K, ∀ i j : Fin n, value x i j ≤ value x i i := by
  classical
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hεPositive (k : ℕ) : 0 < ε k := by
    have hDenominator : 0 < (k : ℝ) + 1 :=
      add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) zero_lt_one
    exact one_div_pos.mpr hDenominator
  have hChoose : ∀ k : ℕ, ∃ x ∈ K, ∀ i j : Fin n,
      value x i j - ε k < value x i i := by
    intro k
    exact happrox (ε k) (hεPositive k)
  choose x hx hNear using hChoose
  obtain ⟨x₀, hx₀, φ, hφ, hConverges⟩ := hK.tendsto_subseq hx
  have hεZero : Tendsto ε atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hεSubsequence : Tendsto (fun k => ε (φ k)) atTop (𝓝 (0 : ℝ)) :=
    hεZero.comp hφ.tendsto_atTop
  refine ⟨x₀, hx₀, ?_⟩
  intro i j
  have hComparisonValue : Tendsto (fun k => value (x (φ k)) i j)
      atTop (𝓝 (value x₀ i j)) :=
    ((hval i j).tendsto x₀).comp hConverges
  have hOwnerValue : Tendsto (fun k => value (x (φ k)) i i)
      atTop (𝓝 (value x₀ i i)) :=
    ((hval i i).tendsto x₀).comp hConverges
  have hLowerLimit : Tendsto (fun k => value (x (φ k)) i j - ε (φ k))
      atTop (𝓝 (value x₀ i j)) := by
    simpa only [sub_zero] using hComparisonValue.sub hεSubsequence
  exact le_of_tendsto_of_tendsto hLowerLimit hOwnerValue
    (Eventually.of_forall (fun k => (hNear (φ k) i j).le))

end FairDivision.BF
