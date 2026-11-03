import FairDivision.Topology.UnlabeledContinuousAction

/-!
# Centered expected-value scores

Subtracting the average score puts the score vector in the reduced regular
representation. It vanishes exactly when all position scores are equal. The
construction is continuous and commutes with position relabeling.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- Mean of the position scores on the unlabeled auxiliary simplex. -/
noncomputable def auxiliaryAverageScore {k m r c : ℕ}
    {D : Finset (Fin m)}
    (v : Finset (Fin m) → ℝ)
    (lot : stdSimplex ℝ (UnlabeledDummyVertex k m r c D)) : ℝ :=
  (∑ i : Fin k, unlabeledExpectedValue v lot i) / (k : ℝ)

/-- Score at `i` after subtracting the common position average. -/
noncomputable def auxiliaryCenteredScore {k m r c : ℕ}
    {D : Finset (Fin m)}
    (v : Finset (Fin m) → ℝ)
    (lot : stdSimplex ℝ (UnlabeledDummyVertex k m r c D))
    (i : Fin k) : ℝ :=
  unlabeledExpectedValue v lot i - auxiliaryAverageScore v lot

/-- The average is continuous in the lottery weights. -/
theorem auxiliaryAverageScore_continuous {k m r c : ℕ}
    {D : Finset (Fin m)} (v : Finset (Fin m) → ℝ) :
    Continuous (fun lot : stdSimplex ℝ
      (UnlabeledDummyVertex k m r c D) =>
      auxiliaryAverageScore v lot) := by
  unfold auxiliaryAverageScore
  exact (continuous_finset_sum _ (fun i _ =>
    unlabeledExpectedValue_continuous v i)).div_const _

/-- Every centered coordinate is continuous. -/
theorem auxiliaryCenteredScore_continuous {k m r c : ℕ}
    {D : Finset (Fin m)} (v : Finset (Fin m) → ℝ)
    (i : Fin k) :
    Continuous (fun lot : stdSimplex ℝ
      (UnlabeledDummyVertex k m r c D) =>
      auxiliaryCenteredScore v lot i) := by
  unfold auxiliaryCenteredScore
  exact (unlabeledExpectedValue_continuous v i).sub
    (auxiliaryAverageScore_continuous v)

/-- The sum of the centered coordinates is zero for positive `k`. -/
theorem auxiliaryCenteredScore_sum_zero {k m r c : ℕ}
    {D : Finset (Fin m)} (hk : 0 < k)
    (v : Finset (Fin m) → ℝ)
    (lot : stdSimplex ℝ (UnlabeledDummyVertex k m r c D)) :
    (∑ i : Fin k, auxiliaryCenteredScore v lot i) = 0 := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  unfold auxiliaryCenteredScore auxiliaryAverageScore
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  field_simp [hkR]
  ring

/-- Relabeling positions leaves the average score unchanged. -/
theorem auxiliaryAverageScore_relabel {k m r c : ℕ}
    {D : Finset (Fin m)}
    (σ : Equiv.Perm (Fin k)) (v : Finset (Fin m) → ℝ)
    (lot : stdSimplex ℝ (UnlabeledDummyVertex k m r c D)) :
    auxiliaryAverageScore v
      (stdSimplex.map (relabelUnlabeledVertex σ) lot) =
      auxiliaryAverageScore v lot := by
  unfold auxiliaryAverageScore
  congr 1
  calc
    (∑ j : Fin k,
      unlabeledExpectedValue v
        (stdSimplex.map (relabelUnlabeledVertex σ) lot) j) =
      ∑ i : Fin k,
        unlabeledExpectedValue v
          (stdSimplex.map (relabelUnlabeledVertex σ) lot) (σ i) := by
      exact (Equiv.sum_comp σ _).symm
    _ = ∑ i : Fin k, unlabeledExpectedValue v lot i := by
      apply Finset.sum_congr rfl
      intro i _
      exact relabeledLottery_score σ v lot i

/-- Centered scores transform equivariantly under position relabeling. -/
theorem auxiliaryCenteredScore_relabel {k m r c : ℕ}
    {D : Finset (Fin m)}
    (σ : Equiv.Perm (Fin k)) (v : Finset (Fin m) → ℝ)
    (lot : stdSimplex ℝ (UnlabeledDummyVertex k m r c D))
    (i : Fin k) :
    auxiliaryCenteredScore v
      (stdSimplex.map (relabelUnlabeledVertex σ) lot) (σ i) =
      auxiliaryCenteredScore v lot i := by
  unfold auxiliaryCenteredScore
  rw [relabeledLottery_score, auxiliaryAverageScore_relabel]

/-- All centered scores vanish exactly when all position scores equal the
common average. -/
theorem auxiliaryCenteredScore_zero_iff {k m r c : ℕ}
    {D : Finset (Fin m)}
    (v : Finset (Fin m) → ℝ)
    (lot : stdSimplex ℝ (UnlabeledDummyVertex k m r c D)) :
    (∀ i : Fin k, auxiliaryCenteredScore v lot i = 0) ↔
      ∀ i : Fin k,
        unlabeledExpectedValue v lot i =
          auxiliaryAverageScore v lot := by
  simp only [auxiliaryCenteredScore, sub_eq_zero]

end FairDivision.Topology
