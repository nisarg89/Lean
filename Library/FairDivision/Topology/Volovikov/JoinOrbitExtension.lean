import FairDivision.Topology.Volovikov.JoinOrbitPasteEquivariant

/-!
# One equivariant orbit attachment

A connected target fills one representative new simplex. Translation gives
the other cell maps, finite closed-cover pasting makes them continuous on
the whole attached orbit, and the restriction equations prove equivariance.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity
open scoped Classical

/-- Extend an equivariant map across one free orbit of new simplex cells. -/
theorem exists_equivariant_joinOrbitExtension
    {m j k : ℕ} {G X : Type*}
    [AddGroup G] [Fintype G] [TopologicalSpace X]
    (A : PreAbstractSimplicialComplex (Fin m × G))
    (hA : IsJoinTranslationInvariant A)
    (hOld : universalJoinSkeleton m G (j + 1) ≤ A)
    (R : Finset (Fin m × G)) (hR : IsUniversalJoinFace R)
    (hcard : R.card = j + 2) (hRnot : R ∉ A)
    (hX : NullConnectedSpace k X) (hj : j ≤ k)
    (targetAction : G → X ≃ₜ X)
    (hAction : IsContinuousAddAction targetAction)
    (f : C(simplicialRealization A, X))
    (hf : IsEquivariantJoinMap A hA targetAction f) :
    ∃ f' : C(simplicialRealization
        (A ⊔ joinFaceOrbitComplex R), X),
      (∀ w : simplicialRealization A,
        f' ⟨w.1, (simplicialRealization_mono le_sup_left) w.2⟩ = f w) ∧
      IsEquivariantJoinMap (A ⊔ joinFaceOrbitComplex R)
        (joinOrbitAttach_invariant A hA R) targetAction f' := by
  obtain ⟨g, H, hH⟩ :=
    exists_joinOrbitClosedFamilyPaste_of_nullConnected
      A hA hOld R hR hcard hRnot hX hj targetAction f hf
  refine ⟨joinOrbitPastedMap A R H, ?_, ?_⟩
  · exact joinOrbitPastedMap_old A R f
      (fun a => translateCellMap targetAction a R g) H hH
  · exact joinOrbitPastedMap_equivariant A hA targetAction
      hAction f hf R g H hH

end FairDivision.Topology.Volovikov
