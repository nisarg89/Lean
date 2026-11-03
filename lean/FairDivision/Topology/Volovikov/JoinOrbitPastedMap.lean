import FairDivision.Topology.Volovikov.JoinOrbitPasting

/-!
# The orbitwise paste as a map on a simplicial realization

The finite closed cover used for pasting is identified with the realization
of the old complex joined with one face orbit. Exact restriction equations
carry across that identification.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity
open scoped Classical

/-- Restrict the closed-cover paste along its equality with the attached
simplicial realization. -/
noncomputable def joinOrbitPastedMap
    {m : ℕ} {G X : Type*}
    [AddGroup G] [Fintype G] [TopologicalSpace X]
    (A : PreAbstractSimplicialComplex (Fin m × G))
    (R : Finset (Fin m × G))
    (H : C(joinOrbitClosedUnion A R, X)) :
    C(simplicialRealization (A ⊔ joinFaceOrbitComplex R), X) :=
  H.comp (ContinuousMap.inclusion (by
    rw [joinOrbitClosedUnion_eq_realization A R]))

/-- On the old complex, the attached map has the old value. -/
theorem joinOrbitPastedMap_old
    {m : ℕ} {G X : Type*}
    [AddGroup G] [Fintype G] [TopologicalSpace X]
    (A : PreAbstractSimplicialComplex (Fin m × G))
    (R : Finset (Fin m × G))
    (f : C(simplicialRealization A, X))
    (g : ∀ a : G, C(joinOrbitCellSet R a, X))
    (H : C(joinOrbitClosedUnion A R, X))
    (hH : ClosedFamilyPasteSpec (simplicialRealization A)
      (joinOrbitCellSet R) Finset.univ f g H)
    (x : simplicialRealization A) :
    joinOrbitPastedMap A R H
      ⟨x.1, (simplicialRealization_mono le_sup_left) x.2⟩ = f x := by
  change H ⟨x.1, _⟩ = f x
  exact hH.1 x

/-- On each translated full cell, the attached map has the prescribed
transported value. -/
theorem joinOrbitPastedMap_cell
    {m : ℕ} {G X : Type*}
    [AddGroup G] [Fintype G] [TopologicalSpace X]
    (A : PreAbstractSimplicialComplex (Fin m × G))
    (R : Finset (Fin m × G))
    (f : C(simplicialRealization A, X))
    (g : ∀ a : G, C(joinOrbitCellSet R a, X))
    (H : C(joinOrbitClosedUnion A R, X))
    (hH : ClosedFamilyPasteSpec (simplicialRealization A)
      (joinOrbitCellSet R) Finset.univ f g H)
    (a : G) (x : joinOrbitCellSet R a) :
    joinOrbitPastedMap A R H
      ⟨x.1, (simplicialRealization_mono
        ((fullFaceComplex_le_joinFaceOrbitComplex R a).trans
          le_sup_right)) x.2⟩ = g a x := by
  change H ⟨x.1, _⟩ = g a x
  exact hH.2 a (Finset.mem_univ a) x

/-- The old-map restriction can be used at any point of the attached
realization whose support belongs to the old complex. -/
theorem joinOrbitPastedMap_old_at
    {m : ℕ} {G X : Type*}
    [AddGroup G] [Fintype G] [TopologicalSpace X]
    (A : PreAbstractSimplicialComplex (Fin m × G))
    (R : Finset (Fin m × G))
    (f : C(simplicialRealization A, X))
    (g : ∀ a : G, C(joinOrbitCellSet R a, X))
    (H : C(joinOrbitClosedUnion A R, X))
    (hH : ClosedFamilyPasteSpec (simplicialRealization A)
      (joinOrbitCellSet R) Finset.univ f g H)
    (w : simplicialRealization (A ⊔ joinFaceOrbitComplex R))
    (hwA : w.1 ∈ simplicialRealization A) :
    joinOrbitPastedMap A R H w = f ⟨w.1, hwA⟩ := by
  change H ⟨w.1, _⟩ = f ⟨w.1, hwA⟩
  exact hH.1 ⟨w.1, hwA⟩

/-- The cell-map restriction can be used at any point supported in a
translated full cell. -/
theorem joinOrbitPastedMap_cell_at
    {m : ℕ} {G X : Type*}
    [AddGroup G] [Fintype G] [TopologicalSpace X]
    (A : PreAbstractSimplicialComplex (Fin m × G))
    (R : Finset (Fin m × G))
    (f : C(simplicialRealization A, X))
    (g : ∀ a : G, C(joinOrbitCellSet R a, X))
    (H : C(joinOrbitClosedUnion A R, X))
    (hH : ClosedFamilyPasteSpec (simplicialRealization A)
      (joinOrbitCellSet R) Finset.univ f g H)
    (a : G)
    (w : simplicialRealization (A ⊔ joinFaceOrbitComplex R))
    (hwCell : w.1 ∈ joinOrbitCellSet R a) :
    joinOrbitPastedMap A R H w = g a ⟨w.1, hwCell⟩ := by
  change H ⟨w.1, _⟩ = g a ⟨w.1, hwCell⟩
  exact hH.2 a (Finset.mem_univ a) ⟨w.1, hwCell⟩

end FairDivision.Topology.Volovikov
