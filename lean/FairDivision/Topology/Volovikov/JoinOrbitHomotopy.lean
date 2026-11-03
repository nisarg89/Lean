import FairDivision.Topology.Volovikov.JoinPathSpaceAction
import FairDivision.Topology.NerveConnectivity.FiniteFaceRelativeHomotopyExtension

/-!
# One free orbit of actual simplex-prism homotopy fills

Use the existing one-face prism extension for a representative face, curry
its actual continuous homotopy, and reuse the existing orbitwise paste and
equivariance proof with codomain C(I,X). Endpoint conservation is proved by
the endpoint maps' equivariance. No connectivity assertion for path spaces
and no new homotopy oracle is assumed.
-/

set_option autoImplicit false

open scoped unitInterval Topology Classical

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity

/-- The manuscript's equivariant one-orbit homotopy attachment, retaining
the two prescribed endpoint maps and the old homotopy exactly. -/
theorem exists_equivariant_joinOrbitHomotopy
    {m j k:ℕ}{G X:Type*} [AddGroup G] [Fintype G] [TopologicalSpace X]
    (K A:PreAbstractSimplicialComplex (Fin m×G))
    (hK:IsJoinTranslationInvariant K) (hA:IsJoinTranslationInvariant A)
    (hAK:A≤K) (hOld:universalJoinSkeleton m G (j+1)≤A)
    (R:Finset (Fin m×G)) (hR:IsUniversalJoinFace R)
    (hRK:R∈K) (hCard:R.card=j+2) (hAbsent:R∉A)
    (hX:NullConnectedSpace k X) (hj:j+1≤k)
    (action:G→X≃ₜX) (hAction:IsContinuousAddAction action)
    (f0 f1:C(simplicialRealization K,X))
    (hf0:IsEquivariantJoinMap K hK action f0)
    (hf1:IsEquivariantJoinMap K hK action f1)
    (q:C(simplicialRealization A,C(I,X)))
    (hq:IsEquivariantJoinMap A hA (joinPathAction action) q)
    (h0:∀w:simplicialRealization A,q w 0=f0 ⟨w.1,simplicialRealization_mono hAK w.2⟩)
    (h1:∀w:simplicialRealization A,q w 1=f1 ⟨w.1,simplicialRealization_mono hAK w.2⟩):
    ∃q':C(simplicialRealization (A⊔joinFaceOrbitComplex R),C(I,X)),
      (∀w:simplicialRealization A,
        q' ⟨w.1,simplicialRealization_mono le_sup_left w.2⟩=q w) ∧
      IsEquivariantJoinMap (A⊔joinFaceOrbitComplex R)
        (joinOrbitAttach_invariant A hA R) (joinPathAction action) q' ∧
      (∀w:simplicialRealization (A⊔joinFaceOrbitComplex R),
        q' w 0=f0 ⟨w.1,simplicialRealization_mono
          (sup_le hAK (joinFaceOrbitComplex_le_of_representative_mem K hK R hRK)) w.2⟩) ∧
      ∀w:simplicialRealization (A⊔joinFaceOrbitComplex R),
        q' w 1=f1 ⟨w.1,simplicialRealization_mono
          (sup_le hAK (joinFaceOrbitComplex_le_of_representative_mem K hK R hRK)) w.2⟩:=by
  have hProper:∀S:Finset (Fin m×G),S.Nonempty→S⊂R→S∈A:=by
    intro S hS hSR
    have hFace:IsUniversalJoinFace S:=⟨hS,fun i g h hgi hhi=>
      hR.2 i g h (hSR.subset hgi) (hSR.subset hhi)⟩
    apply hOld
    exact ⟨hFace,by have hc:=Finset.card_lt_card hSR;omega⟩
  have hFaceK:fullFaceComplex R≤K:=fullFaceComplex_le_of_mem K R hRK
  have hSingle:A⊔fullFaceComplex R≤K:=sup_le hAK hFaceK
  let f0S:=f0.comp (ContinuousMap.inclusion (simplicialRealization_mono hSingle))
  let f1S:=f1.comp (ContinuousMap.inclusion (simplicialRealization_mono hSingle))
  obtain ⟨HSingle,hSingleOld,hSingle0,hSingle1⟩:=
    exists_attachOneFaceHomotopy_of_nullConnected A R hR.1 hProper hAbsent j hCard hX hj
      q.uncurry f0S f1S h0 h1
  let g:C(simplicialRealization (fullFaceComplex R),C(I,X)):=
    (HSingle.comp {
      toFun:=fun z=>(⟨z.1.1,simplicialRealization_mono le_sup_right z.1.2⟩,z.2)
      continuous_toFun:=by
        apply Continuous.prodMk
        ·exact (continuous_subtype_val.comp continuous_fst).subtype_mk _
        ·exact continuous_snd }).curry
  have hCompatible:∀(xA:simplicialRealization A)
      (xR:simplicialRealization (fullFaceComplex R)),xA.1=xR.1→q xA=g xR:=by
    intro xA xR hEq
    ext t
    exact (hSingleOld xA t).symm.trans (by
      change HSingle (⟨xA.1,_⟩,t)=HSingle (⟨xR.1,_⟩,t)
      congr 1
      exact Prod.ext (Subtype.ext hEq) rfl)
  obtain ⟨HPaste,hHPaste⟩:=exists_joinOrbitClosedFamilyPaste A hA hOld R hR
    (by omega) (joinPathAction action) q hq g hCompatible
  let q':=joinOrbitPastedMap A R HPaste
  have hNew:A⊔joinFaceOrbitComplex R≤K:=
    sup_le hAK (joinFaceOrbitComplex_le_of_representative_mem K hK R hRK)
  refine ⟨q',joinOrbitPastedMap_old A R q _ HPaste hHPaste,?_,?_,?_⟩
  ·exact joinOrbitPastedMap_equivariant A hA (joinPathAction action)
      (joinPathAction_laws action hAction) q hq R g HPaste hHPaste
  ·intro w
   apply joinOrbitPastedMap_at_time K A hA hK hAK R hFaceK action hAction q g
     HPaste hHPaste f0 hf0 0 h0 _ hNew w
   intro y
   exact hSingle0 ⟨y.1,simplicialRealization_mono le_sup_right y.2⟩
  ·intro w
   apply joinOrbitPastedMap_at_time K A hA hK hAK R hFaceK action hAction q g
     HPaste hHPaste f1 hf1 1 h1 _ hNew w
   intro y
   exact hSingle1 ⟨y.1,simplicialRealization_mono le_sup_right y.2⟩

end FairDivision.Topology.Volovikov
