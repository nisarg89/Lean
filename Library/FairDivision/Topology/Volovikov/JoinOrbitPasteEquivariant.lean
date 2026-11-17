import FairDivision.Topology.Volovikov.JoinOrbitRepresentativesFinite

/-!
# Equivariance of an orbitwise pasted cell filling

The finite closed-family paste has exact old-complex and cell restrictions.
On the old complex, equivariance is inherited. On a translated cell, the
translator-composition law and the target action law prove equivariance.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity
open scoped Classical

/-- A paste of translated cell maps is equivariant whenever the old map is
equivariant and the target homeomorphisms satisfy the group law. -/
theorem joinOrbitPastedMap_equivariant
    {m : ℕ} {G X : Type*}
    [AddGroup G] [Fintype G] [TopologicalSpace X]
    (A : PreAbstractSimplicialComplex (Fin m × G))
    (hA : IsJoinTranslationInvariant A)
    (targetAction : G → X ≃ₜ X)
    (hAction : IsContinuousAddAction targetAction)
    (f : C(simplicialRealization A, X))
    (hf : IsEquivariantJoinMap A hA targetAction f)
    (R : Finset (Fin m × G))
    (g : C(simplicialRealization (fullFaceComplex R), X))
    (H : C(joinOrbitClosedUnion A R, X))
    (hH : ClosedFamilyPasteSpec (simplicialRealization A)
      (joinOrbitCellSet R) Finset.univ f
      (fun a => translateCellMap targetAction a R g) H) :
    IsEquivariantJoinMap (A ⊔ joinFaceOrbitComplex R)
      (joinOrbitAttach_invariant A hA R)
      targetAction (joinOrbitPastedMap A R H) := by
  let K := A ⊔ joinFaceOrbitComplex R
  let hK : IsJoinTranslationInvariant K :=
    joinOrbitAttach_invariant A hA R
  let F := joinOrbitPastedMap A R H
  intro c w
  have hcases : w.1 ∈ simplicialRealization A ∨
      w.1 ∈ simplicialRealization (joinFaceOrbitComplex R) := by
    exact w.2
  rcases hcases with hwA | hwOrbit
  · let xA : simplicialRealization A := ⟨w.1, hwA⟩
    let xA' : simplicialRealization A :=
      translateInvariantRealization A hA c xA
    have hval :
        (translateInvariantRealization K hK c w).1 = xA'.1 := rfl
    have hwA' :
        (translateInvariantRealization K hK c w).1 ∈
          simplicialRealization A := hval.symm ▸ xA'.2
    have hFw := joinOrbitPastedMap_old_at A R f
      (fun a => translateCellMap targetAction a R g)
      H hH w hwA
    have hFw' := joinOrbitPastedMap_old_at A R f
      (fun a => translateCellMap targetAction a R g)
      H hH (translateInvariantRealization K hK c w) hwA'
    calc
      F (translateInvariantRealization K hK c w) =
          f ⟨(translateInvariantRealization K hK c w).1, hwA'⟩ := hFw'
      _ = f xA' := congrArg f (Subtype.ext hval)
      _ = targetAction c (f xA) := hf c xA
      _ = targetAction c (F w) := by rw [hFw]
  · obtain ⟨a, hwa⟩ :=
      (mem_joinFaceOrbitRealization_iff R w.1).1 hwOrbit
    let xCell : joinOrbitCellSet R a := ⟨w.1, hwa⟩
    let y : simplicialRealization (fullFaceComplex R) :=
      (translateJoinFaceCell a R).symm xCell
    have hxCell : translateJoinFaceCell a R y = xCell :=
      (translateJoinFaceCell a R).apply_symm_apply xCell
    have hval :
        (translateInvariantRealization K hK c w).1 =
          (translateJoinFaceCell (c + a) R y).1 := by
      calc
        (translateInvariantRealization K hK c w).1 =
            stdSimplex.map (translateJoinVertex c) w.1 := rfl
        _ = stdSimplex.map (translateJoinVertex c)
            (translateJoinFaceCell a R y).1 := by rw [hxCell]
        _ = (translateJoinFaceCell (c + a) R y).1 :=
          (translateJoinFaceCell_add c a R y).symm
    have hwb : (translateInvariantRealization K hK c w).1 ∈
        joinOrbitCellSet R (c + a) :=
      hval.symm ▸ (translateJoinFaceCell (c + a) R y).2
    have hFw := joinOrbitPastedMap_cell_at A R f
      (fun a => translateCellMap targetAction a R g)
      H hH a w hwa
    have hFw' := joinOrbitPastedMap_cell_at A R f
      (fun a => translateCellMap targetAction a R g)
      H hH (c + a) (translateInvariantRealization K hK c w) hwb
    calc
      F (translateInvariantRealization K hK c w) =
          translateCellMap targetAction (c + a) R g
            ⟨(translateInvariantRealization K hK c w).1, hwb⟩ := hFw'
      _ = translateCellMap targetAction (c + a) R g
            (translateJoinFaceCell (c + a) R y) :=
        congrArg _ (Subtype.ext hval)
      _ = targetAction c
            (translateCellMap targetAction a R g
              (translateJoinFaceCell a R y)) :=
        translateCellMap_comp targetAction hAction c a R g y
      _ = targetAction c (translateCellMap targetAction a R g xCell) := by
        rw [hxCell]
      _ = targetAction c (F w) := by
        exact congrArg (targetAction c) hFw.symm

end FairDivision.Topology.Volovikov
