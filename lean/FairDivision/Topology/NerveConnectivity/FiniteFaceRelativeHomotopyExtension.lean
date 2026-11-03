import FairDivision.Topology.NerveConnectivity.FiniteFacePrismBoundaryPaste

/-!
# Relative homotopy extension across one finite simplex

A homotopy on an old subcomplex and two maps on the enlarged complex
prescribe the side and end faces of the new simplex prism. If the target
is connected through the boundary dimension, the prism cell fills and
pastes to the old homotopy. All three restrictions remain exact.
-/

set_option autoImplicit false

open scoped unitInterval Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- Extend a homotopy across one positive-dimensional face while preserving
its prescribed time-zero and time-one maps. -/
theorem exists_attachOneFaceHomotopy_of_nullConnected
    {V : Type v} [Fintype V] {X : Type u} [TopologicalSpace X]
    (A : PreAbstractSimplicialComplex V)
    (F : Finset V) (hF : F.Nonempty)
    (hproper : ∀ G : Finset V, G.Nonempty → G ⊂ F → G ∈ A)
    (hFnot : F ∉ A)
    (j : ℕ) (hcard : F.card = j + 2)
    {k : ℕ} (hX : NullConnectedSpace k X) (hj : j + 1 ≤ k)
    (HOld : C(simplicialRealization A × I, X))
    (f0 f1 : C(simplicialRealization (A ⊔ fullFaceComplex F), X))
    (h0 : ∀ w : simplicialRealization A,
      HOld (w, 0) = f0 ⟨w.1, simplicialRealization_mono le_sup_left w.2⟩)
    (h1 : ∀ w : simplicialRealization A,
      HOld (w, 1) = f1 ⟨w.1, simplicialRealization_mono le_sup_left w.2⟩) :
    ∃ H : C(simplicialRealization (A ⊔ fullFaceComplex F) × I, X),
      (∀ (w : simplicialRealization A) (t : I),
        H (⟨w.1, simplicialRealization_mono le_sup_left w.2⟩, t) =
          HOld (w, t)) ∧
      (∀ w : simplicialRealization (A ⊔ fullFaceComplex F), H (w, 0) = f0 w) ∧
      (∀ w : simplicialRealization (A ⊔ fullFaceComplex F), H (w, 1) = f1 w) := by
  obtain ⟨b, hbSide, hb0, hb1⟩ :=
    exists_fullFacePrismBoundary_paste A F hproper HOld f0 f1 h0 h1
  obtain ⟨HFace, hHFace⟩ :=
    exists_fullFacePrism_cellFilling F hF j hcard hX hj b
  have hcompat : ∀ (w : stdSimplex ℝ V) (t : I)
      (hwA : w ∈ simplicialRealization A)
      (hwF : w ∈ simplicialRealization (fullFaceComplex F)),
      HOld (⟨w, hwA⟩, t) = HFace (⟨w, hwF⟩, t) := by
    intro w t hwA hwF
    have hwB : w ∈ simplicialRealization (boundaryFaceComplex F) := by
      have hwI : w ∈ simplicialRealization (A ⊓ fullFaceComplex F) :=
        ⟨hwA, hwF⟩
      rwa [inf_fullFaceComplex_eq_boundary A F hproper hFnot] at hwI
    have hface := congrArg (fun q : C(FullFacePrismBoundary F, X) =>
      q ⟨(⟨w, hwF⟩, t), Or.inl hwB⟩) hHFace
    have hside := hbSide ⟨w, hwF⟩ hwB t
    exact hside.symm.trans hface.symm
  let H := simplicialPrismPaste A (fullFaceComplex F) HOld HFace hcompat
  refine ⟨H, ?_, ?_, ?_⟩
  · intro w t
    exact simplicialPrismPaste_left A (fullFaceComplex F)
      HOld HFace hcompat w t
  · intro w
    have hwUnion : w.1 ∈ simplicialRealization A ∪
        simplicialRealization (fullFaceComplex F) := by
      simpa only [simplicialRealization_sup] using w.2
    rcases hwUnion with hwA | hwF
    · let a : simplicialRealization A := ⟨w.1, hwA⟩
      calc
        H (w, 0) = HOld (a, 0) := by
          exact simplicialPrismPaste_left A (fullFaceComplex F)
            HOld HFace hcompat a 0
        _ = f0 w := by simpa [a] using h0 a
    · let z : simplicialRealization (fullFaceComplex F) := ⟨w.1, hwF⟩
      have heq := congrArg (fun q : C(FullFacePrismBoundary F, X) =>
        q ⟨(z, 0), Or.inr (Or.inl rfl)⟩) hHFace
      calc
        H (w, 0) = HFace (z, 0) := by
          exact simplicialPrismPaste_right A (fullFaceComplex F)
            HOld HFace hcompat z 0
        _ = b ⟨(z, 0), Or.inr (Or.inl rfl)⟩ := heq
        _ = f0 w := by simpa [z] using hb0 z
  · intro w
    have hwUnion : w.1 ∈ simplicialRealization A ∪
        simplicialRealization (fullFaceComplex F) := by
      simpa only [simplicialRealization_sup] using w.2
    rcases hwUnion with hwA | hwF
    · let a : simplicialRealization A := ⟨w.1, hwA⟩
      calc
        H (w, 1) = HOld (a, 1) := by
          exact simplicialPrismPaste_left A (fullFaceComplex F)
            HOld HFace hcompat a 1
        _ = f1 w := by simpa [a] using h1 a
    · let z : simplicialRealization (fullFaceComplex F) := ⟨w.1, hwF⟩
      have heq := congrArg (fun q : C(FullFacePrismBoundary F, X) =>
        q ⟨(z, 1), Or.inr (Or.inr rfl)⟩) hHFace
      calc
        H (w, 1) = HFace (z, 1) := by
          exact simplicialPrismPaste_right A (fullFaceComplex F)
            HOld HFace hcompat z 1
        _ = b ⟨(z, 1), Or.inr (Or.inr rfl)⟩ := heq
        _ = f1 w := by simpa [z] using hb1 z

end FairDivision.Topology.NerveConnectivity
