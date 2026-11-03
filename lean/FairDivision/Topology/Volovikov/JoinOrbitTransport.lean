import FairDivision.Topology.Volovikov.JoinFaceCellAction

/-!
# Transporting a simplex-cell map across a free join-face orbit

A nonempty join face has a unique translator from its chosen orbit
representative. The corresponding homeomorphism of full simplex cells allows
one prescribed filling to be reused on every face of that orbit.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity
open scoped Classical

/-- The cell of the chosen orbit representative is homeomorphic to the cell
of a given join face, via its unique translator. -/
noncomputable def orbitRepToFaceCell {m : ℕ} {G : Type*}
    [AddGroup G] [Fintype G]
    (S : UniversalJoinFace m G) :
    simplicialRealization (fullFaceComplex
      (universalJoinFaceOrbitRep S).1) ≃ₜ
      simplicialRealization (fullFaceComplex S.1) := by
  rw [← universalJoinFaceTranslator_spec S]
  exact translateJoinFaceCell (universalJoinFaceTranslator S)
    (universalJoinFaceOrbitRep S).1

/-- Transport a continuous map from a chosen cell to another cell in its
orbit, applying the corresponding target homeomorphism. -/
noncomputable def transportOrbitCellMap {m : ℕ} {G X : Type*}
    [AddGroup G] [Fintype G] [TopologicalSpace X]
    (targetAction : G → X ≃ₜ X)
    (S : UniversalJoinFace m G)
    (representativeMap : C(simplicialRealization
      (fullFaceComplex (universalJoinFaceOrbitRep S).1), X)) :
    C(simplicialRealization (fullFaceComplex S.1), X) :=
  (⟨targetAction (universalJoinFaceTranslator S),
    (targetAction (universalJoinFaceTranslator S)).continuous⟩ : C(X, X)).comp
    (representativeMap.comp
      ⟨(orbitRepToFaceCell S).symm, (orbitRepToFaceCell S).symm.continuous⟩)

/-- The transported cell map has the expected pointwise formula. -/
theorem transportOrbitCellMap_apply {m : ℕ} {G X : Type*}
    [AddGroup G] [Fintype G] [TopologicalSpace X]
    (targetAction : G → X ≃ₜ X)
    (S : UniversalJoinFace m G)
    (representativeMap : C(simplicialRealization
      (fullFaceComplex (universalJoinFaceOrbitRep S).1), X))
    (x : simplicialRealization (fullFaceComplex S.1)) :
    transportOrbitCellMap targetAction S representativeMap x =
      targetAction (universalJoinFaceTranslator S)
        (representativeMap ((orbitRepToFaceCell S).symm x)) := by
  rfl

/-- Transport one prescribed cell map by a specified group element. This
nondependent form makes the equivariance calculation immediate. -/
noncomputable def translateCellMap {m : ℕ} {G X : Type*}
    [AddGroup G] [Fintype G] [TopologicalSpace X]
    (targetAction : G → X ≃ₜ X)
    (a : G) (S : Finset (Fin m × G))
    (f : C(simplicialRealization (fullFaceComplex S), X)) :
    C(simplicialRealization
      (fullFaceComplex (translateJoinFace a S)), X) :=
  (⟨targetAction a, (targetAction a).continuous⟩ : C(X, X)).comp
    (f.comp ⟨(translateJoinFaceCell a S).symm,
      (translateJoinFaceCell a S).symm.continuous⟩)

/-- At a translated point, the transported map has precisely the translated
target value. -/
theorem translateCellMap_apply_translated {m : ℕ} {G X : Type*}
    [AddGroup G] [Fintype G] [TopologicalSpace X]
    (targetAction : G → X ≃ₜ X)
    (a : G) (S : Finset (Fin m × G))
    (f : C(simplicialRealization (fullFaceComplex S), X))
    (x : simplicialRealization (fullFaceComplex S)) :
    translateCellMap targetAction a S f (translateJoinFaceCell a S x) =
      targetAction a (f x) := by
  simp [translateCellMap]

end FairDivision.Topology.Volovikov
