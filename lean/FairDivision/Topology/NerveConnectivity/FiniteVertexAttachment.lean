import FairDivision.Topology.NerveConnectivity.FiniteCellAttachment

/-!
# Attaching a new vertex

A new vertex is disjoint from the previously realized subcomplex. A chosen
point of the target therefore gives its extension, with no connectivity
assumption beyond nonemptiness.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- A map extends across a newly added isolated vertex by choosing its
value there. -/
theorem exists_attachVertexMap
    {V : Type v} [Fintype V]
    {X : Type u} [TopologicalSpace X]
    (A : PreAbstractSimplicialComplex V) (v : V)
    (hv : ({v} : Finset V) ∉ A)
    (x : X) (f : C(simplicialRealization A, X)) :
    ∃ f' : C(simplicialRealization
        (A ⊔ fullFaceComplex ({v} : Finset V)), X),
      ∀ w : simplicialRealization A,
        f' ⟨w.1, (simplicialRealization_mono le_sup_left) w.2⟩ = f w := by
  let g : C(simplicialRealization (fullFaceComplex ({v} : Finset V)), X) :=
    ContinuousMap.const _ x
  have hfg : ∀ (w : stdSimplex ℝ V)
      (hwA : w ∈ simplicialRealization A)
      (hwV : w ∈ simplicialRealization (fullFaceComplex ({v} : Finset V))),
        f ⟨w, hwA⟩ = g ⟨w, hwV⟩ := by
    intro w hwA hwV
    have hsupport : FairDivision.Topology.finiteSimplexSupport w = {v} :=
      (FairDivision.Topology.finiteSimplexSupport_nonempty w).subset_singleton_iff.mp
        hwV.2
    exact (hv (hsupport ▸ hwA)).elim
  refine ⟨attachOneFaceMap A {v} f g hfg, ?_⟩
  exact attachOneFaceMap_old A {v} f g hfg

end FairDivision.Topology.NerveConnectivity
