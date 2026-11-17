import FairDivision.Topology.Volovikov.JoinOrbitPasteEquivariant
import Mathlib.Topology.CompactOpen

/-! Pointwise action on actual continuous interval paths. This is only
currying/postcomposition transport: existing free-orbit closed pasting is
reused with codomain C(I,X) for the manuscript's equivariant prism fills. -/

set_option autoImplicit false

open scoped unitInterval Topology

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity

/-- Postcompose each path by the target homeomorphism. -/
def joinPathAction {G X:Type*} [AddGroup G] [TopologicalSpace X]
    (action:G→X≃ₜX) (g:G):C(I,X)≃ₜC(I,X):=
  (Homeomorph.refl I).arrowCongr (action g)

@[simp] theorem joinPathAction_apply {G X:Type*} [AddGroup G] [TopologicalSpace X]
    (action:G→X≃ₜX) (g:G) (γ:C(I,X)) (t:I):
    joinPathAction action g γ t=action g (γ t):=rfl

theorem joinPathAction_laws {G X:Type*} [AddGroup G] [TopologicalSpace X]
    (action:G→X≃ₜX) (hAction:IsContinuousAddAction action):
    IsContinuousAddAction (joinPathAction action):=by
  constructor
  ·intro γ
   ext t
   exact hAction.1 (γ t)
  ·intro g h γ
   ext t
   exact hAction.2 g h (γ t)

/-- An orbit paste of path-valued maps retains any fixed-time endpoint
map on the whole attached orbit, provided that map is equivariant. -/
theorem joinOrbitPastedMap_at_time
    {m:ℕ}{G X:Type*} [AddGroup G] [Fintype G] [TopologicalSpace X]
    (K A:PreAbstractSimplicialComplex (Fin m×G))
    (hA:IsJoinTranslationInvariant A) (hK:IsJoinTranslationInvariant K)
    (hAK:A≤K) (R:Finset (Fin m×G)) (hRK:fullFaceComplex R≤K)
    (action:G→X≃ₜX) (hAction:IsContinuousAddAction action)
    (q:C(simplicialRealization A,C(I,X)))
    (g:C(simplicialRealization (fullFaceComplex R),C(I,X)))
    (H:C(joinOrbitClosedUnion A R,C(I,X)))
    (hH:ClosedFamilyPasteSpec (simplicialRealization A) (joinOrbitCellSet R)
      Finset.univ q (fun a=>translateCellMap (joinPathAction action) a R g) H)
    (f:C(simplicialRealization K,X)) (hf:IsEquivariantJoinMap K hK action f)
    (t:I)
    (hq:∀w:simplicialRealization A,q w t=f ⟨w.1,simplicialRealization_mono hAK w.2⟩)
    (hg:∀w:simplicialRealization (fullFaceComplex R),
      g w t=f ⟨w.1,simplicialRealization_mono hRK w.2⟩)
    (hNew:A⊔joinFaceOrbitComplex R≤K)
    (w:simplicialRealization (A⊔joinFaceOrbitComplex R)):
    joinOrbitPastedMap A R H w t=f ⟨w.1,simplicialRealization_mono hNew w.2⟩:=by
  rcases w.2 with hwA|hwOrbit
  ·rw [joinOrbitPastedMap_old_at A R q _ H hH w hwA]
   exact hq ⟨w.1,hwA⟩
  ·obtain ⟨a,hwa⟩:=(mem_joinFaceOrbitRealization_iff R w.1).mp hwOrbit
   let cell:joinOrbitCellSet R a:=⟨w.1,hwa⟩
   let y:simplicialRealization (fullFaceComplex R):=(translateJoinFaceCell a R).symm cell
   let yK:simplicialRealization K:=⟨y.1,simplicialRealization_mono hRK y.2⟩
   have hReturn:(translateJoinFaceCell a R y).1=w.1:=
     congrArg Subtype.val ((translateJoinFaceCell a R).apply_symm_apply cell)
   have hSource:translateInvariantRealization K hK a yK=
       ⟨w.1,simplicialRealization_mono hNew w.2⟩:=by
     apply Subtype.ext
     exact hReturn
   rw [joinOrbitPastedMap_cell_at A R q _ H hH a w hwa]
   change action a (g y t)=_
   rw [hg y,←hf a yK,hSource]

end FairDivision.Topology.Volovikov
