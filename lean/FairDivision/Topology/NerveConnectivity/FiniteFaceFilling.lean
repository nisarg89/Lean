import FairDivision.Topology.NerveConnectivity.FiniteFaceFiniteBoundary
import FairDivision.Topology.Volovikov.SimplexConeHomeomorph

/-!
# Filling an arbitrary finite simplex face

The standard-simplex cell filling theorem transfers to an arbitrary finite
face through the compiled full-face and boundary homeomorphisms. The resulting
map can then be pasted to a map on an existing subcomplex when the new face's
proper boundary is already present.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- A finite face of `j + 2` vertices is a standard `(j + 1)`-simplex. -/
noncomputable def fullFaceFinHomeomorph {V : Type v} [Fintype V]
    (F : Finset V) (hF : F.Nonempty) (j : ℕ)
    (hcard : F.card = j + 2) :
    simplicialRealization (fullFaceComplex F) ≃ₜ
      stdSimplex ℝ (Fin (j + 2)) :=
  (fullFaceRealizationHomeomorph F hF).trans
    (simplexIndexHomeomorph (faceVertexFinEquiv F j hcard))

/-- The corresponding boundary homeomorphism. -/
noncomputable def boundaryFaceFinHomeomorph {V : Type v} [Fintype V]
    (F : Finset V) (hF : F.Nonempty) (j : ℕ)
    (hcard : F.card = j + 2) :
    simplicialRealization (boundaryFaceComplex F) ≃ₜ
      FairDivision.Topology.finiteStandardSimplexBoundary j :=
  (boundaryFaceRealizationHomeomorph F hF).trans
    (finiteFaceBoundaryFinHomeomorph F j hcard)

/-- The full-face and boundary homeomorphisms commute with inclusion. -/
theorem fullFaceFinHomeomorph_boundary {V : Type v} [Fintype V]
    (F : Finset V) (hF : F.Nonempty) (j : ℕ)
    (hcard : F.card = j + 2)
    (w : simplicialRealization (boundaryFaceComplex F)) :
    fullFaceFinHomeomorph F hF j hcard
      ⟨w.1, (simplicialRealization_mono
        (boundaryFaceComplex_le_fullFaceComplex F)) w.2⟩ =
      (boundaryFaceFinHomeomorph F hF j hcard w).1 := rfl

/-- Any boundary map on an arbitrary `(j + 1)`-face extends over that face
when the target is operationally connected through dimension `j`. -/
theorem exists_fullFace_cellFilling
    {V : Type v} [Fintype V]
    {X : Type u} [TopologicalSpace X]
    (F : Finset V) (hF : F.Nonempty) (j : ℕ)
    (hcard : F.card = j + 2) {k : ℕ}
    (hX : NullConnectedSpace k X) (hj : j ≤ k)
    (f : C(simplicialRealization (boundaryFaceComplex F), X)) :
    ∃ g : C(simplicialRealization (fullFaceComplex F), X),
      ∀ w : simplicialRealization (boundaryFaceComplex F),
        g ⟨w.1, (simplicialRealization_mono
          (boundaryFaceComplex_le_fullFaceComplex F)) w.2⟩ = f w := by
  let eB := boundaryFaceFinHomeomorph F hF j hcard
  let eF := fullFaceFinHomeomorph F hF j hcard
  let fStd : C(FairDivision.Topology.finiteStandardSimplexBoundary j, X) :=
    f.comp ⟨eB.symm, eB.symm.continuous⟩
  obtain ⟨gStd, hgStd⟩ :=
    FairDivision.Topology.Volovikov.exists_finiteSimplex_cellFilling hX hj fStd
  let g : C(simplicialRealization (fullFaceComplex F), X) :=
    gStd.comp ⟨eF, eF.continuous⟩
  refine ⟨g, ?_⟩
  intro w
  have hboundary := fullFaceFinHomeomorph_boundary F hF j hcard w
  have hfill := congrArg
    (fun q : C(FairDivision.Topology.finiteStandardSimplexBoundary j, X) => q (eB w))
    hgStd
  change gStd (eF ⟨w.1, _⟩) = f w
  rw [hboundary]
  simpa [fStd] using hfill

/-- Attach one new face using operational connectivity of the target. -/
theorem exists_attachOneFaceMap_of_nullConnected
    {V : Type v} [Fintype V]
    {X : Type u} [TopologicalSpace X]
    (A : PreAbstractSimplicialComplex V)
    (F : Finset V) (hF : F.Nonempty)
    (hproper : ∀ G : Finset V, G.Nonempty → G ⊂ F → G ∈ A)
    (hFnot : F ∉ A)
    (j : ℕ) (hcard : F.card = j + 2)
    {k : ℕ} (hX : NullConnectedSpace k X) (hj : j ≤ k)
    (f : C(simplicialRealization A, X)) :
    ∃ f' : C(simplicialRealization (A ⊔ fullFaceComplex F), X),
      ∀ w : simplicialRealization A,
        f' ⟨w.1, (simplicialRealization_mono le_sup_left) w.2⟩ = f w := by
  let bInc : C(simplicialRealization (boundaryFaceComplex F),
      simplicialRealization A) :=
    ContinuousMap.inclusion
      (simplicialRealization_mono
        (boundaryFaceComplex_le_of_proper A F hproper))
  obtain ⟨g, hg⟩ := exists_fullFace_cellFilling F hF j hcard hX hj
    (f.comp bInc)
  have hfg : ∀ (w : stdSimplex ℝ V)
      (hwA : w ∈ simplicialRealization A)
      (hwF : w ∈ simplicialRealization (fullFaceComplex F)),
        f ⟨w, hwA⟩ = g ⟨w, hwF⟩ := by
    intro w hwA hwF
    have hwB : w ∈ simplicialRealization (boundaryFaceComplex F) := by
      have hwI : w ∈ simplicialRealization (A ⊓ fullFaceComplex F) :=
        ⟨hwA, hwF⟩
      rwa [inf_fullFaceComplex_eq_boundary A F hproper hFnot] at hwI
    have h := hg ⟨w, hwB⟩
    exact h.symm
  refine ⟨attachOneFaceMap A F f g hfg, ?_⟩
  exact attachOneFaceMap_old A F f g hfg

end FairDivision.Topology.NerveConnectivity
