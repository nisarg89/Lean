import FairDivision.Topology.SimplexAffineHyperplaneBall
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Probability-simplex and relative-boundary affine models

Translation by the uniform barycenter identifies the probability simplex
with the centered coordinate body in its sum-zero hyperplane. Coordinate
projections on that hyperplane are open when there are at least two vertices;
this identifies its frontier with the union of proper simplex faces.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open scoped BigOperators

/-- Boundary of an arbitrary finite probability simplex: at least one
barycentric coordinate vanishes. -/
abbrev SimplexBoundary (V : Type*) [Fintype V] :=
  {x : stdSimplex ℝ V // ∃ v : V,x.1 v=0}

theorem simplexBarycentricCoordinate_sum (V : Type*) [Fintype V] [Nonempty V] :
    (∑ _v : V,simplexBarycentricCoordinate V)=1 := by
  have h : (Fintype.card V : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  simp [simplexBarycentricCoordinate,h]

/-- Literal translation into the correct affine hyperplane. -/
noncomputable def simplexCenteredHomeomorph (V : Type*) [Fintype V] [Nonempty V] :
    stdSimplex ℝ V ≃ₜ centeredSimplex V where
  toFun x := ⟨⟨(fun v => x.1 v-simplexBarycentricCoordinate V),by
      change (∑ v : V, (x.1 v - simplexBarycentricCoordinate V)) = 0
      rw [Finset.sum_sub_distrib,x.2.2,simplexBarycentricCoordinate_sum]
      exact sub_self 1⟩,by
    intro v
    have h := x.2.1 v
    dsimp
    linarith⟩
  invFun z := ⟨(fun v => z.1.1 v+simplexBarycentricCoordinate V),by
    constructor
    · intro v
      have h := z.2 v
      linarith
    · rw [Finset.sum_add_distrib,z.1.2,simplexBarycentricCoordinate_sum]
      simp⟩
  left_inv x := by
    apply Subtype.ext
    funext v
    dsimp
    ring
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    funext v
    dsimp
    ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply continuous_pi
    intro v
    exact ((continuous_apply v).comp continuous_subtype_val).sub continuous_const
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro v
    exact ((continuous_apply v).comp
      (continuous_subtype_val.comp continuous_subtype_val)).add continuous_const

@[simp] theorem simplexCenteredHomeomorph_apply (V : Type*) [Fintype V] [Nonempty V]
    (x : stdSimplex ℝ V) (v : V) :
    (simplexCenteredHomeomorph V x).1.1 v=x.1 v-simplexBarycentricCoordinate V := rfl

/-- A coordinate functional restricted to the sum-zero hyperplane. -/
def centeredSimplexCoordinate {V : Type*} [Fintype V] (v : V) : simplexZeroSum V →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj v).comp (simplexZeroSum V).subtypeL

theorem centeredSimplexCoordinate_surjective {V : Type*} [Fintype V] [Nontrivial V]
    (v : V) : Function.Surjective (centeredSimplexCoordinate v) := by
  classical
  obtain ⟨w,hw⟩ := exists_ne v
  intro t
  refine ⟨⟨Pi.single v t-Pi.single w t,by simp⟩,?_⟩
  simp [centeredSimplexCoordinate,hw,hw.symm]

/-- The relative interior consists exactly of strictly positive translated
barycentric coordinates. The ambient space is the affine hyperplane. -/
theorem centeredSimplex_interior {V : Type*} [Fintype V] [Nontrivial V] :
    interior (centeredSimplex V)=
      {z : simplexZeroSum V | ∀ v : V,-simplexBarycentricCoordinate V<z.1 v} := by
  letI : CompleteSpace (simplexZeroSum V) :=
    FiniteDimensional.complete ℝ (simplexZeroSum V)
  have hSet : centeredSimplex V=⋂ v : V,
      (centeredSimplexCoordinate v) ⁻¹' Set.Ici (-simplexBarycentricCoordinate V) := by
    ext z
    simp [centeredSimplex,centeredSimplexCoordinate]
  have hInterior (v : V) :
      interior ((centeredSimplexCoordinate v) ⁻¹'
        Set.Ici (-simplexBarycentricCoordinate V)) =
      (centeredSimplexCoordinate v) ⁻¹'
        Set.Ioi (-simplexBarycentricCoordinate V) := by
    simpa only [interior_Ici] using
      (ContinuousLinearMap.interior_preimage
        (centeredSimplexCoordinate v)
        (centeredSimplexCoordinate_surjective v)
        (Set.Ici (-simplexBarycentricCoordinate V)))
  rw [hSet,interior_iInter_of_finite]
  simp_rw [hInterior]
  ext z
  simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_Ioi, Set.mem_setOf_eq]
  rfl

theorem mem_frontier_centeredSimplex_iff {V : Type*} [Fintype V] [Nontrivial V]
    (z : simplexZeroSum V) :
    z∈frontier (centeredSimplex V) ↔
      z∈centeredSimplex V ∧ ∃ v : V,z.1 v= -simplexBarycentricCoordinate V := by
  rw [(centeredSimplex_isClosed V).frontier_eq,centeredSimplex_interior]
  constructor
  · rintro ⟨hz,hNot⟩
    have hNot' : ¬∀v : V,-simplexBarycentricCoordinate V<z.1 v := hNot
    obtain ⟨v,hv⟩ := not_forall.mp hNot'
    exact ⟨hz,v,le_antisymm (le_of_not_gt hv) (hz v)⟩
  · rintro ⟨hz,v,hv⟩
    refine ⟨hz,?_⟩
    intro h
    have hStrict := h v
    rw [hv] at hStrict
    exact lt_irrefl _ hStrict

/-- Exact relative-boundary match, not a claim about the empty ambient
interior of the simplex inside all unrestricted coordinate vectors. -/
theorem simplexCenteredHomeomorph_boundary_iff {V : Type*}
    [Fintype V] [Nonempty V] [Nontrivial V] (x : stdSimplex ℝ V) :
    (simplexCenteredHomeomorph V x).1∈frontier (centeredSimplex V) ↔
      ∃ v : V,x.1 v=0 := by
  rw [mem_frontier_centeredSimplex_iff]
  constructor
  · rintro ⟨_,v,hv⟩
    refine ⟨v,?_⟩
    change x.1 v-simplexBarycentricCoordinate V= -simplexBarycentricCoordinate V at hv
    linarith
  · rintro ⟨v,hv⟩
    refine ⟨(simplexCenteredHomeomorph V x).2,v,?_⟩
    simp [hv]

end FairDivision.Topology
