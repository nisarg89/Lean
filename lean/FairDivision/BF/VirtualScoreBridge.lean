import FairDivision.BF.VirtualValuationSpec
import FairDivision.Topology.UnlabeledReducedMarginal
import FairDivision.BF.AuxiliaryCompactness
import FairDivision.BF.ApproximateScoresToExact

/-!
# BF Section 5: virtual valuations and preference scores on the auxiliary complex

The corrected unlabeled-dummy auxiliary point has one finite-coordinate
marginal lottery at each position. Composing those marginals with a virtual
valuation gives the manuscript's agent-by-position values. The already
proved preference-score and compactness lemmas turn equalized scores at
all positive tolerances into exact virtual envy comparisons.
-/

set_option autoImplicit false

namespace FairDivision.BF

open scoped BigOperators Classical

open FairDivision.Topology

/-- If the topological step equalizes the manuscript's preference scores
for every positive tolerance, some auxiliary point satisfies every exact
owner-versus-position virtual-value comparison. -/
theorem exists_virtualEnvyFree_of_equalized_scores
    {n N q : ℕ} (hn : 0 < n) (D : Finset (Fin N))
    (v : Fin n → Finset (Fin (N - D.card)) → ℝ)
    (spec : VirtualValuationSpec (q := q) v)
    (hEqual : ∀ ε : ℝ, 0 < ε →
      ∃ x : unlabeledLotterySpace n N (q - 1) 1 D,
        ∀ s t : Fin n,
          positionScore hn
            (fun i z => spec.score z i) ε
            (fun a => unlabeledReducedMarginal a x) s =
          positionScore hn
            (fun i z => spec.score z i) ε
            (fun a => unlabeledReducedMarginal a x) t) :
    ∃ x : unlabeledLotterySpace n N (q - 1) 1 D,
      ∀ i j : Fin n,
        spec.score (unlabeledReducedMarginal j x) i ≤
          spec.score (unlabeledReducedMarginal i x) i := by
  letI : CompactSpace (unlabeledLotterySpace n N (q - 1) 1 D) :=
    isCompact_iff_compactSpace.mp (unlabeledLotterySpace_isCompact D)
  -- This is a subtype of a finite real-coordinate simplex, so Mathlib's
  -- compact-subsequence theorem needs no additional manuscript premise.
  letI : FirstCountableTopology (unlabeledLotterySpace n N (q - 1) 1 D) := inferInstance
  obtain ⟨x, _, hx⟩ :=
    exists_exact_comparisons_of_equalized_scores
      hn (Set.univ : Set (unlabeledLotterySpace n N (q - 1) 1 D))
      isCompact_univ
      (fun i z => spec.score z i)
      (fun x s => unlabeledReducedMarginal s x)
      (by
        intro i s
        exact (continuous_apply i).comp
          (spec.continuous_score.comp
            (unlabeledReducedMarginal_continuous s)))
      (fun σ x => auxiliaryRelabel σ.symm x)
      (by simp)
      (by
        intro σ x s
        simpa only [Equiv.symm_apply_apply] using
          unlabeledReducedMarginal_relabel σ.symm x (σ s))
      (by
        intro ε hε
        obtain ⟨x, hx⟩ := hEqual ε hε
        exact ⟨x, Set.mem_univ x, hx⟩)
  exact ⟨x, hx⟩

end FairDivision.BF
