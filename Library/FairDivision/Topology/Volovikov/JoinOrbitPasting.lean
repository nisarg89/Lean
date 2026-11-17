import FairDivision.Topology.Volovikov.JoinOrbitRepresentativeFilling
import FairDivision.Topology.NerveConnectivity.FiniteClosedFamilyPasting

/-!
# Simultaneous pasting over one free orbit of simplex cells

The old realization and every translated full cell form a finite closed
cover. The representative filling and its translates agree with the old map
on all overlaps; different translated cells intersect only inside the old
skeleton. Generic finite closed-family pasting therefore produces one
continuous map over the entire attached orbit.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity
open scoped Classical

/-- The realized full cell at one translated face. -/
def joinOrbitCellSet {m : ℕ} {G : Type*}
    [AddGroup G] [Fintype G]
    (R : Finset (Fin m × G)) (a : G) :
    Set (stdSimplex ℝ (Fin m × G)) :=
  simplicialRealization (fullFaceComplex (translateJoinFace a R))

/-- The closed cover formed by the old complex and the whole face orbit. -/
def joinOrbitClosedUnion {m : ℕ} {G : Type*}
    [AddGroup G] [Fintype G]
    (A : PreAbstractSimplicialComplex (Fin m × G))
    (R : Finset (Fin m × G)) :
    Set (stdSimplex ℝ (Fin m × G)) :=
  closedFamilyUnion (simplicialRealization A)
    (joinOrbitCellSet R) Finset.univ

/-- The finite closed-cover domain is exactly the realization obtained by
adjoining the orbit subcomplex. -/
theorem joinOrbitClosedUnion_eq_realization {m : ℕ} {G : Type*}
    [AddGroup G] [Fintype G]
    (A : PreAbstractSimplicialComplex (Fin m × G))
    (R : Finset (Fin m × G)) :
    joinOrbitClosedUnion A R =
      simplicialRealization (A ⊔ joinFaceOrbitComplex R) := by
  ext w
  simp only [joinOrbitClosedUnion, mem_closedFamilyUnion_iff,
    Finset.mem_univ, true_and, joinOrbitCellSet,
    simplicialRealization_sup, Set.mem_union,
    mem_joinFaceOrbitRealization_iff]

/-- The old map and all transported cell maps admit one continuous paste
on the finite closed family. The exact restriction equations are retained
in `ClosedFamilyPasteSpec`. -/
theorem exists_joinOrbitClosedFamilyPaste
    {m d : ℕ} {G X : Type*}
    [AddGroup G] [Fintype G] [TopologicalSpace X]
    (A : PreAbstractSimplicialComplex (Fin m × G))
    (hA : IsJoinTranslationInvariant A)
    (hOld : universalJoinSkeleton m G d ≤ A)
    (R : Finset (Fin m × G)) (hR : IsUniversalJoinFace R)
    (hcard : R.card = d + 1)
    (targetAction : G → X ≃ₜ X)
    (f : C(simplicialRealization A, X))
    (hf : IsEquivariantJoinMap A hA targetAction f)
    (g : C(simplicialRealization (fullFaceComplex R), X))
    (hfg : ∀ (xA : simplicialRealization A)
      (xR : simplicialRealization (fullFaceComplex R)),
        xA.1 = xR.1 → f xA = g xR) :
    ∃ H : C(joinOrbitClosedUnion A R, X),
      ClosedFamilyPasteSpec (simplicialRealization A)
        (joinOrbitCellSet R) Finset.univ f
        (fun a => translateCellMap targetAction a R g) H := by
  have hB : ∀ a : G, IsClosed (joinOrbitCellSet R a) := by
    intro a
    exact simplicialRealization_isClosed _
  have hcomp : ClosedFamilyCompatible (simplicialRealization A)
      (joinOrbitCellSet R) Finset.univ f
      (fun a => translateCellMap targetAction a R g) := by
    constructor
    · intro a _ w hwA hwB
      exact translateCellMap_agrees_old A hA targetAction f hf R g hfg
        a w hwA hwB
    · intro a _ b _ hab w hwa hwb
      have hwA : w ∈ simplicialRealization A :=
        translatedFullCells_inter_old A hOld R hR hcard a b hab
          w hwa hwb
      calc
        translateCellMap targetAction a R g ⟨w, hwa⟩ =
            f ⟨w, hwA⟩ :=
          (translateCellMap_agrees_old A hA targetAction f hf R g
            hfg a w hwA hwa).symm
        _ = translateCellMap targetAction b R g ⟨w, hwb⟩ :=
          translateCellMap_agrees_old A hA targetAction f hf R g
            hfg b w hwA hwb
  exact exists_closedFamilyPaste
    (simplicialRealization A) (joinOrbitCellSet R)
    (simplicialRealization_isClosed A) hB f
    (fun a => translateCellMap targetAction a R g) Finset.univ hcomp

/-- Connectivity supplies a representative filling, and the free-orbit
overlap laws paste all its translates into a continuous map. -/
theorem exists_joinOrbitClosedFamilyPaste_of_nullConnected
    {m j k : ℕ} {G X : Type*}
    [AddGroup G] [Fintype G] [TopologicalSpace X]
    (A : PreAbstractSimplicialComplex (Fin m × G))
    (hA : IsJoinTranslationInvariant A)
    (hOld : universalJoinSkeleton m G (j + 1) ≤ A)
    (R : Finset (Fin m × G)) (hR : IsUniversalJoinFace R)
    (hcard : R.card = j + 2) (hRnot : R ∉ A)
    (hX : NullConnectedSpace k X) (hj : j ≤ k)
    (targetAction : G → X ≃ₜ X)
    (f : C(simplicialRealization A, X))
    (hf : IsEquivariantJoinMap A hA targetAction f) :
    ∃ g : C(simplicialRealization (fullFaceComplex R), X),
      ∃ H : C(joinOrbitClosedUnion A R, X),
        ClosedFamilyPasteSpec (simplicialRealization A)
          (joinOrbitCellSet R) Finset.univ f
          (fun a => translateCellMap targetAction a R g) H := by
  obtain ⟨g, hfg⟩ := exists_joinOrbitRepresentativeFilling
    A hOld R hR hcard hRnot hX hj f
  have hcard' : R.card = (j + 1) + 1 := by omega
  obtain ⟨H, hH⟩ := exists_joinOrbitClosedFamilyPaste
    A hA hOld R hR hcard' targetAction f hf g hfg
  exact ⟨g, H, hH⟩

end FairDivision.Topology.Volovikov
