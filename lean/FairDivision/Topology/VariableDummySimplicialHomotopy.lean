import FairDivision.Topology.VariableDummyContiguity
import FairDivision.Topology.NerveConnectivity.SimplicialCover
import Mathlib.Topology.Homotopy.Basic

/-!
# Geometric homotopy from simplicial contiguity

A face-wise vertex map whose image is contiguous to the identity induces a
continuous self-map of the probability-simplex realization. Straight-line
interpolation is a homotopy from the identity to this map. The BF saturation
and forced-item retractions both use this shared lemma.
-/

set_option autoImplicit false

open scoped unitInterval Topology

namespace FairDivision.Topology

open NerveConnectivity

/-- Straight-line interpolation of two finite probability vectors is
continuous in the interpolation parameter and both endpoints. -/
theorem variableLotterySegment_continuous {V : Type*} [Fintype V] :
    Continuous (fun z : Set.Icc (0 : ℝ) 1 ×
      (stdSimplex ℝ V × stdSimplex ℝ V) =>
      variableLotterySegment z.2.1 z.2.2 z.1) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  change Continuous (fun z : Set.Icc (0 : ℝ) 1 ×
    (stdSimplex ℝ V × stdSimplex ℝ V) =>
      (1 - (z.1 : ℝ)) * z.2.1.1 v + (z.1 : ℝ) * z.2.2.1 v)
  have ht : Continuous (fun z : Set.Icc (0 : ℝ) 1 ×
      (stdSimplex ℝ V × stdSimplex ℝ V) => (z.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun z : Set.Icc (0 : ℝ) 1 ×
      (stdSimplex ℝ V × stdSimplex ℝ V) => z.2.1.1 v) :=
    (continuous_apply v).comp
      (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
  have hy : Continuous (fun z : Set.Icc (0 : ℝ) 1 ×
      (stdSimplex ℝ V × stdSimplex ℝ V) => z.2.2.1 v) :=
    (continuous_apply v).comp
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  exact ((continuous_const.sub ht).mul hx).add (ht.mul hy)

/-- The segment starts at its first endpoint. -/
theorem variableLotterySegment_zero {V : Type*} [Fintype V]
    (x y : stdSimplex ℝ V) :
    variableLotterySegment x y (0 : Set.Icc (0 : ℝ) 1) = x := by
  apply Subtype.ext
  funext v
  simp [variableLotterySegment]

/-- The segment ends at its second endpoint. -/
theorem variableLotterySegment_one {V : Type*} [Fintype V]
    (x y : stdSimplex ℝ V) :
    variableLotterySegment x y (1 : Set.Icc (0 : ℝ) 1) = y := by
  apply Subtype.ext
  funext v
  simp [variableLotterySegment]

/-- Contiguity ensures that the straight segment remains in the realization
of the same simplicial complex. -/
theorem variableLotterySegment_mem_of_complex_contiguity {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (K : PreAbstractSimplicialComplex
      (VariableUnlabeledVertex k m D r c))
    (f : VariableUnlabeledVertex k m D r c →
      VariableUnlabeledVertex k m D r c)
    (hContig : ∀ S : Finset (VariableUnlabeledVertex k m D r c),
      S ∈ K → S ∪ S.image f ∈ K)
    (lot : stdSimplex ℝ (VariableUnlabeledVertex k m D r c))
    (hlot : lot ∈ simplicialRealization K)
    (t : Set.Icc (0 : ℝ) 1) :
    variableLotterySegment lot (stdSimplex.map f lot) t ∈
      simplicialRealization K := by
  change variableLotterySupport lot ∈ K at hlot
  change variableLotterySupport
    (variableLotterySegment lot (stdSimplex.map f lot) t) ∈ K
  have hFace := hContig (variableLotterySupport lot) hlot
  have hSub : variableLotterySupport
      (variableLotterySegment lot (stdSimplex.map f lot) t) ⊆
      variableLotterySupport lot ∪
        (variableLotterySupport lot).image f := by
    intro p hp
    rcases Finset.mem_union.mp
      (variableLotterySegment_support_subset lot (stdSimplex.map f lot) t hp)
      with hp | hp
    · exact Finset.mem_union_left _ hp
    · exact Finset.mem_union_right _
        (variableLotterySupport_map_subset f lot hp)
  exact (K.isRelLowerSet_faces hFace).2 hSub
    (variableLotterySupport_nonempty _)

/-- A contiguous vertex map induces a continuous map on the realized
subcomplex. -/
noncomputable def variableRealizationMapOfContiguity {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (K : PreAbstractSimplicialComplex
      (VariableUnlabeledVertex k m D r c))
    (f : VariableUnlabeledVertex k m D r c →
      VariableUnlabeledVertex k m D r c)
    (hContig : ∀ S : Finset (VariableUnlabeledVertex k m D r c),
      S ∈ K → S ∪ S.image f ∈ K) :
    C(simplicialRealization K, simplicialRealization K) where
  toFun lot := ⟨stdSimplex.map f lot.1, by
    have h := variableLotterySegment_mem_of_complex_contiguity
      K f hContig lot.1 lot.2 (1 : Set.Icc (0 : ℝ) 1)
    rwa [variableLotterySegment_one] at h⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (stdSimplex.continuous_map f).comp continuous_subtype_val

/-- Simplicial contiguity produces the homotopy used for the BF deformation
retractions. -/
theorem variableRealizationMapOfContiguity_homotopic_id {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (K : PreAbstractSimplicialComplex
      (VariableUnlabeledVertex k m D r c))
    (f : VariableUnlabeledVertex k m D r c →
      VariableUnlabeledVertex k m D r c)
    (hContig : ∀ S : Finset (VariableUnlabeledVertex k m D r c),
      S ∈ K → S ∪ S.image f ∈ K) :
    (ContinuousMap.id (simplicialRealization K)).Homotopic
      (variableRealizationMapOfContiguity K f hContig) := by
  refine ⟨{
    toFun := fun z => ⟨variableLotterySegment z.2.1
      (stdSimplex.map f z.2.1) z.1,
      variableLotterySegment_mem_of_complex_contiguity
        K f hContig z.2.1 z.2.2 z.1⟩
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · apply Continuous.subtype_mk
    have hpair : Continuous (fun z : Set.Icc (0 : ℝ) 1 ×
        simplicialRealization K =>
        (z.1, (z.2.1, stdSimplex.map f z.2.1))) := by
      exact continuous_fst.prodMk
        ((continuous_subtype_val.comp continuous_snd).prodMk
          ((stdSimplex.continuous_map f).comp
            (continuous_subtype_val.comp continuous_snd)))
    exact variableLotterySegment_continuous.comp hpair
  · intro x
    apply Subtype.ext
    exact variableLotterySegment_zero x.1 (stdSimplex.map f x.1)
  · intro x
    apply Subtype.ext
    exact variableLotterySegment_one x.1 (stdSimplex.map f x.1)

end FairDivision.Topology
