import FairDivision.BF.AlmostEnvyFreeScoresTopology
import FairDivision.BF.AlmostEnvyFreeScoresEquivariance
import FairDivision.BF.ApproximateLimit

/-!
# BF Section 5: equalized scores give exact envy comparisons

This is the manuscript's preference-score and compactness pipeline, stated
independently of the particular auxiliary complex. The topological zero
argument must supply an equal-score point for every positive tolerance;
the compact domain and permutation action then give exact comparisons.
-/

set_option autoImplicit false

namespace FairDivision.BF

open scoped BigOperators Classical

/-- Equalization of the manuscript's preference scores for every positive
tolerance yields one point with exact owner-versus-position comparisons. -/
theorem exists_exact_comparisons_of_equalized_scores
    {n : ℕ} (hn : 0 < n)
    {X Z : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    (K : Set X) (hK : IsCompact K)
    (v : Fin n → Z → ℝ)
    (bundle : X → Fin n → Z)
    (hval : ∀ i s : Fin n,
      Continuous (fun x => v i (bundle x s)))
    (relabel : Equiv.Perm (Fin n) → X → X)
    (hKrelabel : ∀ σ x, x ∈ K → relabel σ x ∈ K)
    (hBundle : ∀ σ x s,
      bundle (relabel σ x) s = bundle x (σ s))
    (hEqual : ∀ ε : ℝ, 0 < ε →
      ∃ x ∈ K, ∀ s t : Fin n,
        positionScore hn v ε (bundle x) s =
          positionScore hn v ε (bundle x) t) :
    ∃ x ∈ K, ∀ i j : Fin n,
      v i (bundle x j) ≤ v i (bundle x i) := by
  apply exists_exact_comparisons_of_approximate hn K hK
    (fun x i j => v i (bundle x j)) hval
  intro ε hε
  obtain ⟨x, hx, heq⟩ := hEqual ε hε
  obtain ⟨σ, hσ⟩ :=
    exists_approxEnvyFree_of_equalized_scores hn v ε hε (bundle x) heq
  refine ⟨relabel σ x, hKrelabel σ x hx, ?_⟩
  intro i j
  simpa only [hBundle σ x i, hBundle σ x j] using hσ i j

end FairDivision.BF
