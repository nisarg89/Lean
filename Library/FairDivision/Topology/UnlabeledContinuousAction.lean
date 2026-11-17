import FairDivision.Topology.UnlabeledPositionEquiv

/-!
# Continuous relabeling of the BF auxiliary lottery space

The finite vertex permutation acts continuously on the probability simplex
and preserves the auxiliary subspace. This is the topological action used by
the equalizing-scores argument.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- Relabel positions of one auxiliary lottery, retaining its face proof. -/
noncomputable def auxiliaryRelabel {k m r c : ℕ}
    {D : Finset (Fin m)} (σ : Equiv.Perm (Fin k)) :
    unlabeledLotterySpace k m r c D →
      unlabeledLotterySpace k m r c D :=
  fun x => ⟨stdSimplex.map (relabelUnlabeledVertex σ) x.1,
    relabeledLottery_mem σ x.1 x.2⟩

/-- Every position permutation acts continuously on the realization. -/
theorem auxiliaryRelabel_continuous {k m r c : ℕ}
    {D : Finset (Fin m)} (σ : Equiv.Perm (Fin k)) :
    Continuous (auxiliaryRelabel (D := D) (r := r) (c := c) σ) := by
  apply Continuous.subtype_mk
  · exact (stdSimplex.continuous_map
      (relabelUnlabeledVertex (D := D) (r := r) (c := c) σ)).comp
        continuous_subtype_val

/-- The expected-value score transforms by the same position permutation. -/
theorem auxiliaryRelabel_score {k m r c : ℕ}
    {D : Finset (Fin m)} (σ : Equiv.Perm (Fin k))
    (v : Finset (Fin m) → ℝ)
    (x : unlabeledLotterySpace k m r c D) (i : Fin k) :
    unlabeledExpectedValue v (auxiliaryRelabel σ x).1 (σ i) =
      unlabeledExpectedValue v x.1 i :=
  relabeledLottery_score σ v x.1 i

end FairDivision.Topology
