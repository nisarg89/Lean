import FairDivision.Topology.Volovikov.JoinOrbitComplex

/-!
# Compatibility of translated cell fillings with an old equivariant map

A filling on one representative cell that agrees with the old map on the
intersection can be translated to every cell in its orbit. Equivariance of
the old map proves that each transported filling still agrees with it on
the corresponding intersection.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity
open scoped Classical

/-- Equivariance carries compatibility on one cell to compatibility on
every translated cell. -/
theorem translateCellMap_agrees_old
    {m : ℕ} {G X : Type*}
    [AddGroup G] [Fintype G] [TopologicalSpace X]
    (A : PreAbstractSimplicialComplex (Fin m × G))
    (hA : IsJoinTranslationInvariant A)
    (targetAction : G → X ≃ₜ X)
    (f : C(simplicialRealization A, X))
    (hf : IsEquivariantJoinMap A hA targetAction f)
    (R : Finset (Fin m × G))
    (g : C(simplicialRealization (fullFaceComplex R), X))
    (hfg : ∀ (xA : simplicialRealization A)
      (xR : simplicialRealization (fullFaceComplex R)),
        xA.1 = xR.1 → f xA = g xR)
    (a : G) (w : stdSimplex ℝ (Fin m × G))
    (hwA : w ∈ simplicialRealization A)
    (hwCell : w ∈ simplicialRealization
      (fullFaceComplex (translateJoinFace a R))) :
    f ⟨w, hwA⟩ =
      translateCellMap targetAction a R g ⟨w, hwCell⟩ := by
  let oldPoint : simplicialRealization A := ⟨w, hwA⟩
  let cellPoint : simplicialRealization
      (fullFaceComplex (translateJoinFace a R)) := ⟨w, hwCell⟩
  let pulledOld : simplicialRealization A :=
    translateInvariantRealization A hA (-a) oldPoint
  let pulledCell : simplicialRealization (fullFaceComplex R) :=
    (translateJoinFaceCell a R).symm cellPoint
  have hpull : pulledOld.1 = pulledCell.1 := rfl
  have hboundary := hfg pulledOld pulledCell hpull
  have hreturn :
      translateInvariantRealization A hA a pulledOld = oldPoint := by
    change translateInvariantRealization A hA a
      (translateInvariantRealization A hA (-a) oldPoint) = oldPoint
    calc
      translateInvariantRealization A hA a
          (translateInvariantRealization A hA (-a) oldPoint) =
          translateInvariantRealization A hA (a + -a) oldPoint :=
        (translateInvariantRealization_add A hA a (-a) oldPoint).symm
      _ = oldPoint := by
        rw [add_neg_cancel, translateInvariantRealization_zero]
  calc
    f ⟨w, hwA⟩ = f oldPoint := rfl
    _ = targetAction a (f pulledOld) := by
      rw [← hreturn]
      exact hf a pulledOld
    _ = targetAction a (g pulledCell) := congrArg (targetAction a) hboundary
    _ = translateCellMap targetAction a R g cellPoint := rfl

/-- Translated cell maps obey the target action law on corresponding
translated points. -/
theorem translateCellMap_comp
    {m : ℕ} {G X : Type*}
    [AddGroup G] [Fintype G] [TopologicalSpace X]
    (targetAction : G → X ≃ₜ X)
    (hAction : IsContinuousAddAction targetAction)
    (c a : G) (R : Finset (Fin m × G))
    (g : C(simplicialRealization (fullFaceComplex R), X))
    (y : simplicialRealization (fullFaceComplex R)) :
    translateCellMap targetAction (c + a) R g
        (translateJoinFaceCell (c + a) R y) =
      targetAction c
        (translateCellMap targetAction a R g
          (translateJoinFaceCell a R y)) := by
  rw [translateCellMap_apply_translated,
    translateCellMap_apply_translated]
  exact hAction.2 c a (g y)

end FairDivision.Topology.Volovikov
