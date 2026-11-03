import FairDivision.Topology.NerveConnectivity.PrismBoundaryPasting
import FairDivision.Topology.NerveConnectivity.FinitePrismPasting

/-!
# Boundary data for attaching a finite-face homotopy

An old-complex homotopy and two maps on the enlarged complex prescribe
compatible data on the proper-face side and the two time ends of the new
face prism. Closed-family pasting assembles a continuous boundary map.
-/

set_option autoImplicit false

open scoped unitInterval Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- The proper-face boundary, viewed as a closed subset of the full-face realization. -/
def fullFaceBoundarySet {V : Type v} [Fintype V] (F : Finset V) :
    Set (simplicialRealization (fullFaceComplex F)) :=
  {w | w.1 ∈ simplicialRealization (boundaryFaceComplex F)}

theorem fullFaceBoundarySet_isClosed {V : Type v} [Fintype V]
    (F : Finset V) : IsClosed (fullFaceBoundarySet F) := by
  change IsClosed ((Subtype.val : simplicialRealization (fullFaceComplex F) →
    stdSimplex ℝ V) ⁻¹' simplicialRealization (boundaryFaceComplex F))
  exact (simplicialRealization_isClosed (boundaryFaceComplex F)).preimage
    continuous_subtype_val

/-- Prescribed side and endpoint maps on a new finite-face prism paste to
one map on its entire natural boundary. -/
theorem exists_fullFacePrismBoundary_paste
    {V : Type v} [Fintype V] {X : Type u} [TopologicalSpace X]
    (A : PreAbstractSimplicialComplex V) (F : Finset V)
    (hproper : ∀ G : Finset V, G.Nonempty → G ⊂ F → G ∈ A)
    (HOld : C(simplicialRealization A × I, X))
    (f0 f1 : C(simplicialRealization (A ⊔ fullFaceComplex F), X))
    (h0 : ∀ w : simplicialRealization A,
      HOld (w, 0) = f0 ⟨w.1, simplicialRealization_mono le_sup_left w.2⟩)
    (h1 : ∀ w : simplicialRealization A,
      HOld (w, 1) = f1 ⟨w.1, simplicialRealization_mono le_sup_left w.2⟩) :
    ∃ b : C(FullFacePrismBoundary F, X),
      (∀ (w : simplicialRealization (fullFaceComplex F))
        (hwB : w.1 ∈ simplicialRealization (boundaryFaceComplex F))
        (t : I),
        b ⟨(w, t), Or.inl hwB⟩ =
          HOld (⟨w.1, (simplicialRealization_mono
            (boundaryFaceComplex_le_of_proper A F hproper)) hwB⟩, t)) ∧
      (∀ w : simplicialRealization (fullFaceComplex F),
        b ⟨(w, 0), Or.inr (Or.inl rfl)⟩ =
          f0 ⟨w.1, simplicialRealization_mono le_sup_right w.2⟩) ∧
      (∀ w : simplicialRealization (fullFaceComplex F),
        b ⟨(w, 1), Or.inr (Or.inr rfl)⟩ =
          f1 ⟨w.1, simplicialRealization_mono le_sup_right w.2⟩) := by
  let B := fullFaceBoundarySet F
  let fSide : C(B × I, X) :=
    HOld.comp ⟨fun z =>
      (⟨z.1.1.1, (simplicialRealization_mono
        (boundaryFaceComplex_le_of_proper A F hproper)) z.1.2⟩, z.2), by
      apply Continuous.prodMk
      · apply Continuous.subtype_mk
        exact continuous_subtype_val.comp
          (continuous_subtype_val.comp continuous_fst)
      · exact continuous_snd⟩
  let g0 : C(simplicialRealization (fullFaceComplex F), X) :=
    f0.comp (ContinuousMap.inclusion (simplicialRealization_mono le_sup_right))
  let g1 : C(simplicialRealization (fullFaceComplex F), X) :=
    f1.comp (ContinuousMap.inclusion (simplicialRealization_mono le_sup_right))
  have hg0 : ∀ a : B, fSide (a, 0) = g0 a.1 := by
    intro a
    simpa [fSide, g0, ContinuousMap.inclusion] using h0
      ⟨a.1.1, (simplicialRealization_mono
        (boundaryFaceComplex_le_of_proper A F hproper)) a.2⟩
  have hg1 : ∀ a : B, fSide (a, 1) = g1 a.1 := by
    intro a
    simpa [fSide, g1, ContinuousMap.inclusion] using h1
      ⟨a.1.1, (simplicialRealization_mono
        (boundaryFaceComplex_le_of_proper A F hproper)) a.2⟩
  obtain ⟨b, hbS, hb0, hb1⟩ :=
    exists_relativePrismBoundary_paste B (fullFaceBoundarySet_isClosed F)
      fSide g0 g1 hg0 hg1
  refine ⟨b, ?_, ?_, ?_⟩
  · intro w hwB t
    exact hbS ⟨w, hwB⟩ t
  · intro w
    exact hb0 w
  · intro w
    exact hb1 w

end FairDivision.Topology.NerveConnectivity
