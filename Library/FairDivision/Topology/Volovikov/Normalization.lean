import FairDivision.Topology.Volovikov.ReducedSphere

/-!
# Normalizing a nonzero centered score vector

A nowhere-zero centered score map gives a map to the reduced representation
sphere. This is the analytic part of the Volovikov reduction. The topological
obstruction itself is a separate theorem and is not assumed here.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

/-- Euclidean radius, expressed directly in finite coordinates. -/
noncomputable def centeredRadius {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, (z i) ^ 2)

private theorem sum_sq_nonneg {n : ℕ} (z : Fin n → ℝ) :
    0 ≤ ∑ i : Fin n, (z i) ^ 2 :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (z i))

theorem centeredRadius_pos_of_ne_zero {n : ℕ} (z : Fin n → ℝ)
    (hz : z ≠ 0) : 0 < centeredRadius z := by
  apply Real.sqrt_pos.2
  have hne : (∑ i : Fin n, (z i) ^ 2) ≠ 0 := by
    intro hsum
    apply hz
    funext i
    have hi : (z i) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (z j))).mp
        hsum i (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp hi
  rcases lt_or_eq_of_le (sum_sq_nonneg z) with hpos | hzero
  · exact hpos
  · exact False.elim (hne hzero.symm)

/-- The open part of the centered hyperplane where normalization is defined. -/
def CenteredNonzero (n : ℕ) :=
  {z : Fin n → ℝ // (∑ i : Fin n, z i) = 0 ∧ z ≠ 0}

instance (n : ℕ) : TopologicalSpace (CenteredNonzero n) := inferInstanceAs
  (TopologicalSpace {z : Fin n → ℝ // (∑ i : Fin n, z i) = 0 ∧ z ≠ 0})

/-- Normalize a centered nonzero vector to the round unit sphere. -/
noncomputable def normalizeCentered {n : ℕ}
    (z : CenteredNonzero n) : ReducedSphere n := by
  let r := centeredRadius z.1
  have hr : r ≠ 0 := (centeredRadius_pos_of_ne_zero z.1 z.2.2).ne'
  have hsumNonneg := sum_sq_nonneg z.1
  refine ⟨fun i => z.1 i / r, ?_⟩
  constructor
  · calc
      (∑ i : Fin n, z.1 i / r) =
          (∑ i : Fin n, z.1 i) / r := by rw [Finset.sum_div]
      _ = 0 := by rw [z.2.1, zero_div]
  · calc
      (∑ i : Fin n, (z.1 i / r) ^ 2) =
          (∑ i : Fin n, (z.1 i) ^ 2 / r ^ 2) := by simp_rw [div_pow]
      _ = (∑ i : Fin n, (z.1 i) ^ 2) / r ^ 2 := by rw [Finset.sum_div]
      _ = 1 := by
        dsimp [r, centeredRadius]
        rw [Real.sq_sqrt hsumNonneg]
        have hsumPos : 0 < ∑ i : Fin n, (z.1 i) ^ 2 :=
          Real.sqrt_pos.mp (centeredRadius_pos_of_ne_zero z.1 z.2.2)
        exact div_self (ne_of_gt hsumPos)


/-- Normalization is continuous on the centered nonzero locus. -/
theorem normalizeCentered_continuous {n : ℕ} :
    Continuous (normalizeCentered : CenteredNonzero n → ReducedSphere n) := by
  have hval : Continuous (fun z : CenteredNonzero n => z.1) := continuous_subtype_val
  have hrad : Continuous (fun z : CenteredNonzero n => centeredRadius z.1) := by
    unfold centeredRadius
    apply Real.continuous_sqrt.comp
    exact continuous_finsetSum _ (fun i _ =>
      ((continuous_apply i).comp hval).pow 2)
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact ((continuous_apply i).comp hval).div hrad
    (fun z => (centeredRadius_pos_of_ne_zero z.1 z.2.2).ne')

end FairDivision.Topology.Volovikov
