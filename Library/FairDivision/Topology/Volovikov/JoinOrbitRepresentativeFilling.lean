import FairDivision.Topology.Volovikov.JoinOrbitBoundaryCompatibility
import FairDivision.Topology.NerveConnectivity.FiniteFaceFilling

/-!
# Filling a representative new join cell

When an invariant old complex contains the preceding cardinality skeleton,
the full boundary of a new join face is already mapped. Operational
connectivity fills that boundary. The resulting map agrees with the old map
on the entire overlap, so it can be translated over the face orbit.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity
open scoped Classical

/-- Fill one representative new join face and retain exact compatibility
with the old map on their overlap. -/
theorem exists_joinOrbitRepresentativeFilling
    {m j k : ℕ} {G X : Type*}
    [AddGroup G] [Fintype G] [TopologicalSpace X]
    (A : PreAbstractSimplicialComplex (Fin m × G))
    (hOld : universalJoinSkeleton m G (j + 1) ≤ A)
    (R : Finset (Fin m × G))
    (hR : IsUniversalJoinFace R)
    (hcard : R.card = j + 2)
    (hRnot : R ∉ A)
    (hX : NullConnectedSpace k X)
    (hj : j ≤ k)
    (f : C(simplicialRealization A, X)) :
    ∃ g : C(simplicialRealization (fullFaceComplex R), X),
      ∀ (xA : simplicialRealization A)
        (xR : simplicialRealization (fullFaceComplex R)),
          xA.1 = xR.1 → f xA = g xR := by
  have hproper : ∀ T : Finset (Fin m × G),
      T.Nonempty → T ⊂ R → T ∈ A := by
    intro T hT hTR
    have hface : IsUniversalJoinFace T := by
      refine ⟨hT, ?_⟩
      intro i g h hgi hhi
      exact hR.2 i g h (hTR.subset hgi) (hTR.subset hhi)
    have hlt : T.card < R.card := Finset.card_lt_card hTR
    have hle : T.card ≤ j + 1 := by omega
    exact hOld ⟨hface, hle⟩
  let boundaryInA : C(simplicialRealization (boundaryFaceComplex R),
      simplicialRealization A) :=
    ContinuousMap.inclusion
      (simplicialRealization_mono
        (boundaryFaceComplex_le_of_proper A R hproper))
  obtain ⟨g, hg⟩ := exists_fullFace_cellFilling R hR.1 j hcard
    hX hj (f.comp boundaryInA)
  refine ⟨g, ?_⟩
  intro xA xR heq
  have hA : xR.1 ∈ simplicialRealization A := heq ▸ xA.2
  have hB : xR.1 ∈ simplicialRealization (boundaryFaceComplex R) := by
    have hI : xR.1 ∈ simplicialRealization
        (A ⊓ fullFaceComplex R) := ⟨hA, xR.2⟩
    rwa [inf_fullFaceComplex_eq_boundary A R hproper hRnot] at hI
  have hfill := hg ⟨xR.1, hB⟩
  have hcellEq :
      (⟨xR.1, (simplicialRealization_mono
        (boundaryFaceComplex_le_fullFaceComplex R)) hB⟩ :
          simplicialRealization (fullFaceComplex R)) = xR := rfl
  rw [hcellEq] at hfill
  calc
    f xA = f ⟨xR.1, hA⟩ := by
      congr 1
      exact Subtype.ext heq
    _ = (f.comp boundaryInA) ⟨xR.1, hB⟩ := rfl
    _ = g xR := hfill.symm

end FairDivision.Topology.Volovikov
