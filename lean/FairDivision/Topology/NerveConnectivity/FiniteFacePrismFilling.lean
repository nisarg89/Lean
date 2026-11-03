import FairDivision.Topology.NerveConnectivity.PrismCellFilling
import FairDivision.Topology.NerveConnectivity.FiniteFaceFilling

/-!
# Prism filling for an arbitrary finite simplicial face

The full realization of a finite face, multiplied by a time interval, is
identified with the standard-simplex prism. Its side boundary consists of
proper faces, and the two time ends are included explicitly. This transfers
the compiled standard prism filling to the cells in a finite complex.
-/

set_option autoImplicit false

open scoped unitInterval Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- The natural side-and-end boundary of a full finite-face prism. -/
abbrev FullFacePrismBoundary {V : Type v} [Fintype V] (F : Finset V) :=
  {z : simplicialRealization (fullFaceComplex F) × I //
    z.1.1 ∈ simplicialRealization (boundaryFaceComplex F) ∨
      z.2 = 0 ∨ z.2 = 1}

/-- A point of a full face lies on its proper-face boundary exactly when
its standard-simplex coordinates have a zero entry. -/
theorem fullFaceFinHomeomorph_boundary_iff {V : Type v} [Fintype V]
    (F : Finset V) (hF : F.Nonempty) (j : ℕ)
    (hcard : F.card = j + 2)
    (w : simplicialRealization (fullFaceComplex F)) :
    w.1 ∈ simplicialRealization (boundaryFaceComplex F) ↔
      ∃ i : Fin (j + 2), (fullFaceFinHomeomorph F hF j hcard w).1 i = 0 := by
  constructor
  · intro hw
    let b : simplicialRealization (boundaryFaceComplex F) := ⟨w.1, hw⟩
    have heq : w = ⟨b.1, (simplicialRealization_mono
        (boundaryFaceComplex_le_fullFaceComplex F)) b.2⟩ := by
      apply Subtype.ext
      rfl
    rw [heq, fullFaceFinHomeomorph_boundary]
    exact (boundaryFaceFinHomeomorph F hF j hcard b).2
  · intro hw
    let b : FairDivision.Topology.finiteStandardSimplexBoundary j :=
      ⟨fullFaceFinHomeomorph F hF j hcard w, hw⟩
    let old := (boundaryFaceFinHomeomorph F hF j hcard).symm b
    have heq :
        fullFaceFinHomeomorph F hF j hcard
          ⟨old.1, (simplicialRealization_mono
            (boundaryFaceComplex_le_fullFaceComplex F)) old.2⟩ =
        fullFaceFinHomeomorph F hF j hcard w := by
      rw [fullFaceFinHomeomorph_boundary]
      exact congrArg Subtype.val
        ((boundaryFaceFinHomeomorph F hF j hcard).apply_symm_apply b)
    have hsame := (fullFaceFinHomeomorph F hF j hcard).injective heq
    have hval := congrArg Subtype.val hsame
    exact hval ▸ old.2

/-- The arbitrary-face prism pair is the standard-simplex prism pair. -/
noncomputable def fullFacePrismBoundaryHomeomorph {V : Type v} [Fintype V]
    (F : Finset V) (hF : F.Nonempty) (j : ℕ)
    (hcard : F.card = j + 2) :
    FullFacePrismBoundary F ≃ₜ SimplexPrismBoundary j :=
  Homeomorph.subtype
    ((fullFaceFinHomeomorph F hF j hcard).prodCongr (Homeomorph.refl I))
    (fun z => or_congr (fullFaceFinHomeomorph_boundary_iff F hF j hcard z.1) Iff.rfl)

/-- A boundary map on any finite-face prism extends over that prism when
the target is operationally connected in the boundary dimension. -/
theorem exists_fullFacePrism_cellFilling
    {V : Type v} [Fintype V] {X : Type u} [TopologicalSpace X]
    (F : Finset V) (hF : F.Nonempty) (j : ℕ)
    (hcard : F.card = j + 2) {k : ℕ}
    (hX : NullConnectedSpace k X) (hj : j + 1 ≤ k)
    (f : C(FullFacePrismBoundary F, X)) :
    ∃ H : C(simplicialRealization (fullFaceComplex F) × I, X),
      H.comp (⟨Subtype.val, continuous_subtype_val⟩ :
        C(FullFacePrismBoundary F,
          simplicialRealization (fullFaceComplex F) × I)) = f := by
  let eB := fullFacePrismBoundaryHomeomorph F hF j hcard
  let eF := (fullFaceFinHomeomorph F hF j hcard).prodCongr (Homeomorph.refl I)
  let fStd : C(SimplexPrismBoundary j, X) :=
    f.comp ⟨eB.symm, eB.symm.continuous⟩
  obtain ⟨HStd, hHStd⟩ := exists_finiteSimplexPrism_cellFilling hX hj fStd
  let H : C(simplicialRealization (fullFaceComplex F) × I, X) :=
    HStd.comp ⟨eF, eF.continuous⟩
  refine ⟨H, ?_⟩
  apply ContinuousMap.ext
  intro b
  have hb := congrArg (fun q : C(SimplexPrismBoundary j, X) => q (eB b)) hHStd
  change HStd (eF b.1) = f b
  change HStd (eB b).1 = f b
  simpa [fStd, eB] using hb

end FairDivision.Topology.NerveConnectivity
