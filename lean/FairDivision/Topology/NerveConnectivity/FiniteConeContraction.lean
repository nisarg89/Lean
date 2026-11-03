import FairDivision.Topology.NerveConnectivity.FiniteConeBaseRealization
import FairDivision.Topology.FiniteSimplexSegment

/-!
# Contraction of a finite simplicial cone

A straight segment from any cone point to the apex stays in the cone.
Consequently any map defined on a cone restricts to a nullhomotopic map
on its base. This is the final geometric step in the direct gluing proof.
-/

set_option autoImplicit false

open scoped unitInterval Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- The distinguished apex point in a finite cone realization. -/
noncomputable def finiteConeApex {V : Type u} [Fintype V]
    (K : PreAbstractSimplicialComplex V) :
    simplicialRealization (finiteConeComplex K) := by
  classical
  refine ⟨stdSimplex.vertex (S := ℝ) none, ?_⟩
  change FairDivision.Topology.finiteSimplexSupport
    (stdSimplex.vertex (S := ℝ) (none : Option V)) ∈ finiteConeComplex K
  rw [FairDivision.Topology.finiteSimplexSupport_vertex]
  exact finiteConeComplex_apex K

/-- Straight-line contraction to the cone apex, staying inside the cone. -/
noncomputable def finiteConeSegment {V : Type u} [Fintype V]
    (K : PreAbstractSimplicialComplex V)
    (x : simplicialRealization (finiteConeComplex K)) (t : I) :
    simplicialRealization (finiteConeComplex K) := by
  classical
  let y : stdSimplex ℝ (Option V) := stdSimplex.vertex (S := ℝ) none
  let s := FairDivision.Topology.finiteSimplexSegment x.1 y t
  have hs : FairDivision.Topology.finiteSimplexSupport s ⊆
      insert none (FairDivision.Topology.finiteSimplexSupport x.1) := by
    intro w hw
    have hxy := FairDivision.Topology.finiteSimplexSegment_support_subset x.1 y t hw
    simp only [Finset.mem_union] at hxy
    rcases hxy with hw | hw
    · exact Finset.mem_insert_of_mem hw
    · have hy : FairDivision.Topology.finiteSimplexSupport y = {none} := by
        exact FairDivision.Topology.finiteSimplexSupport_vertex none
      rw [hy] at hw
      exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hw))
  exact ⟨s, ((finiteConeComplex K).isRelLowerSet_faces
    (finiteConeComplex_insert_apex K x.2)).2 hs
      (FairDivision.Topology.finiteSimplexSupport_nonempty s)⟩

/-- The cone contraction is continuous jointly in time and source. -/
theorem finiteConeSegment_continuous {V : Type u} [Fintype V]
    (K : PreAbstractSimplicialComplex V) :
    Continuous (fun z : I × simplicialRealization (finiteConeComplex K) =>
      finiteConeSegment K z.2 z.1) := by
  apply Continuous.subtype_mk
  have hargs : Continuous (fun z : I × simplicialRealization (finiteConeComplex K) =>
      (z.1, (z.2.1, stdSimplex.vertex (S := ℝ) (none : Option V)))) :=
    continuous_fst.prodMk
      ((continuous_subtype_val.comp continuous_snd).prodMk continuous_const)
  exact FairDivision.Topology.finiteSimplexSegment_continuous.comp hargs

/-- A finite cone contracts linearly to its apex. -/
noncomputable def finiteConeContraction {V : Type u} [Fintype V]
    (K : PreAbstractSimplicialComplex V) :
    (ContinuousMap.id (simplicialRealization (finiteConeComplex K))).Homotopy
      (ContinuousMap.const _ (finiteConeApex K)) where
  toFun z := finiteConeSegment K z.2 z.1
  continuous_toFun := finiteConeSegment_continuous K
  map_zero_left := by
    intro x
    apply Subtype.ext
    exact FairDivision.Topology.finiteSimplexSegment_zero x.1
      (stdSimplex.vertex (S := ℝ) none)
  map_one_left := by
    intro x
    apply Subtype.ext
    exact FairDivision.Topology.finiteSimplexSegment_one x.1
      (stdSimplex.vertex (S := ℝ) none)

/-- Any map from a finite cone is nullhomotopic on the cone base. -/
theorem finiteConeMap_base_nullhomotopic
    {V : Type u} [Fintype V] [Nonempty V]
    {X : Type v} [TopologicalSpace X]
    (K : PreAbstractSimplicialComplex V)
    (f : C(simplicialRealization (finiteConeComplex K), X)) :
    (f.comp (finiteConeBaseMap K)).Homotopic
      (ContinuousMap.const _ (f (finiteConeApex K))) := by
  have hc :
      (ContinuousMap.id (simplicialRealization (finiteConeComplex K))).Homotopic
        (ContinuousMap.const _ (finiteConeApex K)) :=
    ⟨finiteConeContraction K⟩
  have hbase := ContinuousMap.Homotopic.comp hc
    (ContinuousMap.Homotopic.refl (finiteConeBaseMap K))
  have hout := ContinuousMap.Homotopic.comp
    (ContinuousMap.Homotopic.refl f) hbase
  simpa [ContinuousMap.comp_assoc] using hout

end FairDivision.Topology.NerveConnectivity
