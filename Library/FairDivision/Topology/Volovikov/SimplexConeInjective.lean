import FairDivision.Topology.Volovikov.SimplexCone

/-!
# Uniqueness of radial coordinates in a finite simplex

A segment from a boundary point to the barycenter has a unique time and,
except at the apex, a unique boundary starting point. This is the injective
half of the simplex-as-cone homeomorphism.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity
open scoped unitInterval

theorem barycenter_coordinate_pos (j : ℕ) :
    0 < ((j + 2 : ℕ) : ℝ)⁻¹ := by
  apply inv_pos.mpr
  positivity

theorem segment_barycenter_coordinate (j : ℕ)
    (b : finiteStandardSimplexBoundary j) (t : I) (i : Fin (j + 2)) :
    (finiteSimplexSegment b.1
      (stdSimplex.barycenter : stdSimplex ℝ (Fin (j + 2))) t).1 i =
      (1 - (t : ℝ)) * b.1.1 i + (t : ℝ) * ((j + 2 : ℕ) : ℝ)⁻¹ := by
  simp [finiteSimplexSegment, stdSimplex.barycenter, smul_eq_mul]

private theorem radial_time_unique (j : ℕ)
    (b c : finiteStandardSimplexBoundary j) (t u : I)
    (h : finiteSimplexSegment b.1
          (stdSimplex.barycenter : stdSimplex ℝ (Fin (j + 2))) t =
        finiteSimplexSegment c.1
          (stdSimplex.barycenter : stdSimplex ℝ (Fin (j + 2))) u) :
    t = u := by
  let q : ℝ := ((j + 2 : ℕ) : ℝ)⁻¹
  have hq : 0 < q := barycenter_coordinate_pos j
  obtain ⟨i, hbi⟩ := b.2
  obtain ⟨l, hcl⟩ := c.2
  have hi := congrArg (fun z : stdSimplex ℝ (Fin (j + 2)) => z.1 i) h
  have hl := congrArg (fun z : stdSimplex ℝ (Fin (j + 2)) => z.1 l) h
  rw [segment_barycenter_coordinate, segment_barycenter_coordinate] at hi hl
  have hu_nonneg : 0 ≤ (1 - (u : ℝ)) * c.1.1 i :=
    mul_nonneg (sub_nonneg.mpr u.2.2) (c.1.2.1 i)
  have ht_nonneg : 0 ≤ (1 - (t : ℝ)) * b.1.1 l :=
    mul_nonneg (sub_nonneg.mpr t.2.2) (b.1.2.1 l)
  have hut : (u : ℝ) * q ≤ (t : ℝ) * q := by
    rw [hbi] at hi
    nlinarith
  have htu : (t : ℝ) * q ≤ (u : ℝ) * q := by
    rw [hcl] at hl
    nlinarith
  apply Subtype.ext
  exact le_antisymm (le_of_mul_le_mul_right htu hq)
    (le_of_mul_le_mul_right hut hq)

/-- Radial parametrization of the simplex is one-to-one after time-one
points are collapsed in the cone. -/
theorem finiteSimplexConeMap_injective (j : ℕ) :
    Function.Injective (finiteSimplexConeMap j) := by
  intro x y hxy
  revert hxy
  refine Quotient.inductionOn₂ x y ?_
  intro a b hab
  have hseg : finiteSimplexSegment a.2.1
        (stdSimplex.barycenter : stdSimplex ℝ (Fin (j + 2))) a.1 =
      finiteSimplexSegment b.2.1
        (stdSimplex.barycenter : stdSimplex ℝ (Fin (j + 2))) b.1 := by
    exact hab
  have ht : a.1 = b.1 :=
    radial_time_unique j a.2 b.2 a.1 b.1 hseg
  by_cases ha : a.1 = 1
  · apply Quot.sound
    exact Or.inr ⟨ha, ht ▸ ha⟩
  · have hcoeff : 1 - (a.1 : ℝ) ≠ 0 := by
      intro hz
      apply ha
      apply Subtype.ext
      simpa using (sub_eq_zero.mp hz).symm
    have hbnd : a.2 = b.2 := by
      apply Subtype.ext
      apply Subtype.ext
      funext i
      have hi := congrArg (fun z : stdSimplex ℝ (Fin (j + 2)) => z.1 i) hseg
      rw [segment_barycenter_coordinate, segment_barycenter_coordinate, ← ht] at hi
      have hmul : (1 - (a.1 : ℝ)) * a.2.1.1 i =
          (1 - (a.1 : ℝ)) * b.2.1.1 i := by
        nlinarith
      exact mul_left_cancel₀ hcoeff hmul
    apply Quot.sound
    exact Or.inl (Prod.ext ht hbnd)

end FairDivision.Topology.Volovikov
