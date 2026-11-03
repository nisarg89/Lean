import FairDivision.Topology.Volovikov.SimplexConeInjective
import Mathlib.Data.Fintype.Lattice
import Mathlib.Algebra.BigOperators.Field

/-!
# Existence of radial coordinates in a finite simplex

Subtract the least barycentric coordinate from every coordinate, then
renormalize. This yields a point on the boundary, and the removed uniform
mass is exactly the time spent moving toward the barycenter.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity
open scoped unitInterval

/-- Every finite simplex point lies on a segment from some boundary point
to the barycenter. Equivalently, the radial cone map is onto. -/
theorem finiteSimplexConeMap_surjective (j : ℕ) :
    Function.Surjective (finiteSimplexConeMap j) := by
  intro x
  obtain ⟨i, hmin⟩ :=
    Finite.exists_min (fun i : Fin (j + 2) => x.1 i)
  let m : ℝ := x.1 i
  let d : ℝ := ((j + 2 : ℕ) : ℝ)
  have hdpos : 0 < d := by
    dsimp [d]
    positivity
  have hmnonneg : 0 ≤ m := x.2.1 i
  have hsumconst : (∑ _ : Fin (j + 2), m) = d * m := by
    simp [d, nsmul_eq_mul]
  have hsumdiff : (∑ l : Fin (j + 2), (x.1 l - m)) = 1 - d * m := by
    calc
      (∑ l : Fin (j + 2), (x.1 l - m)) =
          (∑ l : Fin (j + 2), x.1 l) -
            (∑ _ : Fin (j + 2), m) := by rw [Finset.sum_sub_distrib]
      _ = 1 - d * m := by rw [x.2.2, hsumconst]
  have hdm : d * m ≤ 1 := by
    calc
      d * m = ∑ _ : Fin (j + 2), m := hsumconst.symm
      _ ≤ ∑ l : Fin (j + 2), x.1 l :=
        Finset.sum_le_sum (fun l _ => hmin l)
      _ = 1 := x.2.2
  let t : I := ⟨d * m, mul_nonneg hdpos.le hmnonneg, hdm⟩
  by_cases ht : t = 1
  · have hdmone : d * m = 1 := by
      simpa [t] using congrArg Subtype.val ht
    have hsumzero : (∑ l : Fin (j + 2), (x.1 l - m)) = 0 := by
      rw [hsumdiff]
      linarith
    have hxcoord (l : Fin (j + 2)) : x.1 l = m := by
      have hle : x.1 l - m ≤ ∑ q : Fin (j + 2), (x.1 q - m) :=
        Finset.single_le_sum
          (fun q _ => sub_nonneg.mpr (hmin q))
          (Finset.mem_univ l)
      rw [hsumzero] at hle
      exact le_antisymm (by linarith) (hmin l)
    have hm : m = d⁻¹ := by
      apply mul_left_cancel₀ (ne_of_gt hdpos)
      rw [hdmone, mul_inv_cancel₀ (ne_of_gt hdpos)]
    have hxcenter : x =
        (stdSimplex.barycenter : stdSimplex ℝ (Fin (j + 2))) := by
      apply Subtype.ext
      funext l
      rw [hxcoord l, hm]
      simp [stdSimplex.barycenter, d]
    let b : finiteStandardSimplexBoundary j :=
      Classical.choice (finiteStandardSimplexBoundary_nonempty j)
    refine ⟨Quot.mk (coneSetoid _) ((1 : I), b), ?_⟩
    change finiteSimplexSegment b.1
      (stdSimplex.barycenter : stdSimplex ℝ (Fin (j + 2))) 1 = x
    rw [finiteSimplexSegment_one, hxcenter]
  · have hdmne : d * m ≠ 1 := by
      intro h
      apply ht
      apply Subtype.ext
      simpa [t] using h
    have hdenpos : 0 < 1 - d * m := by
      have hnonneg : 0 ≤ 1 - d * m := sub_nonneg.mpr hdm
      have hne : 1 - d * m ≠ 0 := sub_ne_zero.mpr (Ne.symm hdmne)
      exact lt_of_le_of_ne hnonneg (Ne.symm hne)
    have hdenne : 1 - d * m ≠ 0 := ne_of_gt hdenpos
    let bfun : Fin (j + 2) → ℝ :=
      fun l => (x.1 l - m) / (1 - d * m)
    have hbnonneg (l : Fin (j + 2)) : 0 ≤ bfun l :=
      div_nonneg (sub_nonneg.mpr (hmin l)) hdenpos.le
    have hbsum : (∑ l : Fin (j + 2), bfun l) = 1 := by
      change (∑ l : Fin (j + 2), (x.1 l - m) / (1 - d * m)) = 1
      rw [← Finset.sum_div, hsumdiff, div_self hdenne]
    let bpoint : stdSimplex ℝ (Fin (j + 2)) :=
      ⟨bfun, ⟨hbnonneg, hbsum⟩⟩
    have hbzero : bpoint.1 i = 0 := by
      simp [bpoint, bfun, m]
    let b : finiteStandardSimplexBoundary j := ⟨bpoint, i, hbzero⟩
    refine ⟨Quot.mk (coneSetoid _) (t, b), ?_⟩
    change finiteSimplexSegment b.1
      (stdSimplex.barycenter : stdSimplex ℝ (Fin (j + 2))) t = x
    apply Subtype.ext
    funext l
    rw [segment_barycenter_coordinate]
    change (1 - d * m) * ((x.1 l - m) / (1 - d * m)) +
      (d * m) * d⁻¹ = x.1 l
    field_simp [ne_of_gt hdpos, hdenne]
    ring

end FairDivision.Topology.Volovikov
