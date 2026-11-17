import FairDivision.Topology.NerveConnectivity.BarycentricLayerBridge

/-!
# Inverse barycentric simplex coordinates

The candidate weight at a positive attained coordinate level is the
cardinality of its upper face times the finite predecessor gap. After
multiplying by the uniform face barycenter, its contribution to a vertex
is precisely that gap when the vertex belongs to the upper face.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe v

/-- The contribution of one positive coordinate level to the forward
image of the candidate inverse. -/
theorem faceInverseWeight_upper_mul_bary {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) (t : ℝ) (v : V)
    (htLevel : t ∈ coordinateLevels x) (htPos : 0 < t) :
    faceInverseWeight (upperCoordinateFace x t) x *
      faceBaryWeight (upperCoordinateFace x t) v =
        if v ∈ upperCoordinateFace x t then
          t - finiteLevelPred (coordinateLevels x) t else 0 := by
  classical
  let F := upperCoordinateFace x t
  have hatt : ∃ w : V, x.1 w = t := (mem_coordinateLevels_iff x t).1 htLevel
  obtain ⟨w, hw⟩ := hatt
  have hwF : w ∈ F := (mem_upperCoordinateFace_iff x t w).2 hw.ge
  have hcard : (F.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨w, hwF⟩
  have hgap : 0 ≤ t - finiteLevelPred (coordinateLevels x) t :=
    (sub_pos.mpr (finiteLevelPred_lt_of_pos (coordinateLevels x) t htPos)).le
  rw [faceInverseWeight_upper_eq_gap x t ⟨w, hw⟩, max_eq_right hgap]
  by_cases hv : v ∈ F
  · have hv' : v ∈ upperCoordinateFace x t := hv
    simp only [faceBaryWeight, hv', ↓reduceIte]
    calc
      ((F.card : ℝ) * (t - finiteLevelPred (coordinateLevels x) t)) *
          (F.card : ℝ)⁻¹ =
        (t - finiteLevelPred (coordinateLevels x) t) *
          ((F.card : ℝ) * (F.card : ℝ)⁻¹) := by ring
      _ = t - finiteLevelPred (coordinateLevels x) t := by
        rw [mul_inv_cancel₀ hcard, mul_one]
  · have hv' : v ∉ upperCoordinateFace x t := hv
    simp [faceBaryWeight, hv']

/-- Forward coordinate obtained from the candidate inverse face weights. -/
noncomputable def candidateForwardWeight {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) (v : V) : ℝ :=
  ∑ F : Finset V, faceInverseWeight F x * faceBaryWeight F v

/-- The candidate inverse weights recover every original coordinate
under the forward barycentric formula. -/
theorem candidateForwardWeight_eq {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) (v : V) : candidateForwardWeight x v = x.1 v := by
  classical
  let T := (coordinateLevels x).filter (0 < ·)
  let term : Finset V → ℝ := fun F =>
    faceInverseWeight F x * faceBaryWeight F v
  have hrestrict : (Finset.univ : Finset (Finset V)).sum term =
      (faceInverseSupport x).sum term := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro F _ hF
    have hnot : ¬ 0 < faceInverseWeight F x := by
      intro hpos
      exact hF ((mem_faceInverseSupport_iff x F).2 hpos)
    have hzero : faceInverseWeight F x = 0 :=
      le_antisymm (le_of_not_gt hnot) (faceInverseWeight_nonneg F x)
    simp [term, hzero]
  have hinj : Set.InjOn (upperCoordinateFace x) (T : Set ℝ) := by
    intro s hs t ht heq
    exact upperCoordinateFace_injective_on_levels x
      ((mem_coordinateLevels_iff x s).1 (Finset.mem_filter.mp hs).1)
      ((mem_coordinateLevels_iff x t).1 (Finset.mem_filter.mp ht).1) heq
  calc
    candidateForwardWeight x v = (Finset.univ : Finset (Finset V)).sum term := rfl
    _ = (faceInverseSupport x).sum term := hrestrict
    _ = (T.image (upperCoordinateFace x)).sum term := by
      rw [faceInverseSupport_eq_upper_levels x]
    _ = T.sum (fun t => term (upperCoordinateFace x t)) :=
      Finset.sum_image hinj
    _ = T.sum (fun t => if v ∈ upperCoordinateFace x t then
          t - finiteLevelPred (coordinateLevels x) t else 0) := by
      apply Finset.sum_congr rfl
      intro t ht
      have htLevel : t ∈ coordinateLevels x := (Finset.mem_filter.mp ht).1
      have htPos : 0 < t := (Finset.mem_filter.mp ht).2
      exact faceInverseWeight_upper_mul_bary x t v htLevel htPos
    _ = x.1 v := positiveUpperGap_sum_coordinate x v

/-- Candidate inverse weights sum to one. -/
theorem faceInverseWeight_sum_eq_one {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) :
    ∑ F : Finset V, faceInverseWeight F x = 1 := by
  classical
  calc
    (∑ F : Finset V, faceInverseWeight F x) =
      ∑ F : Finset V, faceInverseWeight F x *
        (∑ v : V, faceBaryWeight F v) := by
          apply Finset.sum_congr rfl
          intro F _
          by_cases hpos : 0 < faceInverseWeight F x
          · have hFn : F.Nonempty := by
              by_contra h
              have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
              subst F
              simp at hpos
            rw [faceBaryWeight_sum F hFn, mul_one]
          · have hzero : faceInverseWeight F x = 0 :=
              le_antisymm (le_of_not_gt hpos) (faceInverseWeight_nonneg F x)
            simp [hzero]
    _ = ∑ v : V, candidateForwardWeight x v := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          rfl
    _ = ∑ v : V, x.1 v := by
          apply Finset.sum_congr rfl
          intro v _
          exact candidateForwardWeight_eq x v
    _ = 1 := x.2.2

/-- A candidate inverse point in the ambient simplex of original faces. -/
noncomputable def barycentricInverseSimplex {V : Type v} [Fintype V]
    (x : stdSimplex ℝ V) : stdSimplex ℝ (Finset V) :=
  ⟨fun F => faceInverseWeight F x,
    fun F => faceInverseWeight_nonneg F x,
    faceInverseWeight_sum_eq_one x⟩

/-- The candidate inverse point is supported on a simplex of the
barycentric subdivision. -/
theorem barycentricInverseSimplex_mem {V : Type v} [Fintype V]
    (K : PreAbstractSimplicialComplex V) (x : simplicialRealization K) :
    barycentricInverseSimplex x.1 ∈
      simplicialRealization (barycentricSubdivision K) := by
  have hsupport : FairDivision.Topology.finiteSimplexSupport
      (barycentricInverseSimplex x.1) = faceInverseSupport x.1 := by
    ext F
    rw [FairDivision.Topology.mem_finiteSimplexSupport_iff,
      mem_faceInverseSupport_iff]
    rfl
  change FairDivision.Topology.finiteSimplexSupport
    (barycentricInverseSimplex x.1) ∈ barycentricSubdivision K
  rw [hsupport]
  exact ⟨faceInverseSupport_nonempty x.1,
    fun F hF => faceInverseSupport_mem_complex K x F hF,
    faceInverseSupport_chain x.1⟩

/-- The inverse coordinates vary continuously on the original complex. -/
theorem barycentricInverseSimplex_continuous {V : Type v} [Fintype V]
    (K : PreAbstractSimplicialComplex V) :
    Continuous (fun x : simplicialRealization K =>
      barycentricInverseSimplex x.1) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro F
  exact (faceInverseWeight_continuous F).comp continuous_subtype_val

/-- Continuous candidate inverse of the forward barycentric map. -/
noncomputable def barycentricInverseMap {V : Type v} [Fintype V]
    (K : PreAbstractSimplicialComplex V) :
    C(simplicialRealization K,
      simplicialRealization (barycentricSubdivision K)) :=
  ⟨fun x => ⟨barycentricInverseSimplex x.1,
      barycentricInverseSimplex_mem K x⟩,
    Continuous.subtype_mk (barycentricInverseSimplex_continuous K) _⟩

/-- Forward subdivision coordinates recover the original point after the
candidate inverse. -/
theorem barycentricForward_comp_inverse {V : Type v} [Fintype V]
    (K : PreAbstractSimplicialComplex V)
    (x : simplicialRealization K) :
    barycentricForwardMap K (barycentricInverseMap K x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  funext v
  exact candidateForwardWeight_eq x.1 v

end FairDivision.Topology.NerveConnectivity
