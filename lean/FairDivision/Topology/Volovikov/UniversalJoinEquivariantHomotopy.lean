import FairDivision.Topology.Volovikov.JoinOrbitHomotopy
import FairDivision.Topology.Volovikov.UniversalJoinEquivariantExtension
import FairDivision.Topology.Volovikov.JoinVertexSkeleton
import FairDivision.Topology.NerveConnectivity.NullHomotopyZero

/-!
# Equivariant homotopy on the same finite universal join

The manuscript uses one extra degree of connectivity for an edge family.
Choose a path between the two endpoint images at one vertex in each color,
translate it over its free vertex orbit, and attach free orbits of actual
simplex prisms. Every prism fill and every closed-family paste reuses the
existing source construction. The resulting homotopy keeps both original
endpoint maps; it is not a replacement of them by newly chosen maps.
-/

set_option autoImplicit false

open scoped unitInterval Topology Classical

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity

/-- A deterministic point of the full universal join, using the same vertex
constructor as its existing one-vertex skeleton. -/
noncomputable def joinVertexPoint {m:ℕ}{G:Type*} [Fintype G] (v:Fin m×G):
    simplicialRealization (universalJoinComplex m G):=
  ⟨(oneSkeletonVertex v).1,(simplicialRealization_mono
    (show universalJoinSkeleton m G 1≤universalJoinComplex m G from fun _ h=>h.1))
    (oneSkeletonVertex v).2⟩

theorem joinVertexPoint_translate {m:ℕ}{G:Type*} [AddGroup G] [Fintype G]
    (g:G) (v:Fin m×G):
    translateInvariantRealization (universalJoinComplex m G)
      universalJoinComplex_invariant g (joinVertexPoint v)=
      joinVertexPoint (translateJoinVertex g v):=by
  apply Subtype.ext
  exact stdSimplex.map_vertex _ _

/-- The vertex base of the actual equivariant homotopy. -/
theorem exists_equivariant_joinVertexHomotopy
    {m k:ℕ}{G X:Type*} [AddGroup G] [Fintype G] [TopologicalSpace X]
    (hX:NullConnectedSpace k X)
    (action:G→X≃ₜX) (hAction:IsContinuousAddAction action)
    (f0 f1:C(simplicialRealization (universalJoinComplex m G),X))
    (hf0:IsEquivariantJoinMap (universalJoinComplex m G) universalJoinComplex_invariant action f0)
    (hf1:IsEquivariantJoinMap (universalJoinComplex m G) universalJoinComplex_invariant action f1):
    ∃q:C(simplicialRealization (universalJoinSkeleton m G 1),C(I,X)),
      IsEquivariantJoinMap (universalJoinSkeleton m G 1) universalJoinSkeleton_invariant
        (joinPathAction action) q ∧
      (∀w:simplicialRealization (universalJoinSkeleton m G 1),
        q w 0=f0 ⟨w.1,(simplicialRealization_mono
          (show universalJoinSkeleton m G 1≤universalJoinComplex m G from fun _ h=>h.1)) w.2⟩) ∧
      ∀w:simplicialRealization (universalJoinSkeleton m G 1),
        q w 1=f1 ⟨w.1,(simplicialRealization_mono
          (show universalJoinSkeleton m G 1≤universalJoinComplex m G from fun _ h=>h.1)) w.2⟩:=by
  have hPath:IsPathConnected (Set.univ:Set X):=
    nullConnectedSpace_zero_iff_pathConnected.mp (hX.mono (Nat.zero_le k))
  let γ:∀i:Fin m,Path (f0 (joinVertexPoint (i,(0:G)))) (f1 (joinVertexPoint (i,(0:G)))):=
    fun i=>(hPath.joinedIn _ (Set.mem_univ _) _ (Set.mem_univ _)).somePath
  letI : DiscreteTopology (simplicialRealization (universalJoinSkeleton m G 1)):=
    oneSkeleton_discreteTopology
  let q:C(simplicialRealization (universalJoinSkeleton m G 1),C(I,X)):=
    ⟨fun w=>(action (oneSkeletonVertexOfPoint w).2 : C(X,X)).comp
      (γ (oneSkeletonVertexOfPoint w).1).toContinuousMap,continuous_of_discreteTopology⟩
  have hVertexValue:∀w:simplicialRealization (universalJoinSkeleton m G 1),
      (joinVertexPoint (oneSkeletonVertexOfPoint w)).1=w.1:=by
    intro w
    exact congrArg Subtype.val (oneSkeletonVertexOfPoint_spec w)
  have hAt:∀(f:C(simplicialRealization (universalJoinComplex m G),X)),
      IsEquivariantJoinMap (universalJoinComplex m G) universalJoinComplex_invariant action f→
      ∀w:simplicialRealization (universalJoinSkeleton m G 1),
      action (oneSkeletonVertexOfPoint w).2
        (f (joinVertexPoint ((oneSkeletonVertexOfPoint w).1,(0:G))))=
      f ⟨w.1,(simplicialRealization_mono
        (show universalJoinSkeleton m G 1≤universalJoinComplex m G from fun _ h=>h.1)) w.2⟩:=by
    intro f hf w
    rw [←hf,joinVertexPoint_translate]
    have he:translateJoinVertex (oneSkeletonVertexOfPoint w).2
        ((oneSkeletonVertexOfPoint w).1,(0:G))=oneSkeletonVertexOfPoint w:=by
      simp [translateJoinVertex]
    rw [he]
    congr 1
    exact Subtype.ext (hVertexValue w)
  refine ⟨q,?_,?_,?_⟩
  ·intro g w
   ext t
   change action (oneSkeletonVertexOfPoint
     (translateInvariantRealization _ _ g w)).2
       (γ (oneSkeletonVertexOfPoint (translateInvariantRealization _ _ g w)).1 t)=
     action g (action (oneSkeletonVertexOfPoint w).2 (γ (oneSkeletonVertexOfPoint w).1 t))
   rw [oneSkeletonVertexOfPoint_translate]
   exact hAction.2 g (oneSkeletonVertexOfPoint w).2 _
  ·intro w
   change action (oneSkeletonVertexOfPoint w).2 (γ (oneSkeletonVertexOfPoint w).1 0)=_
   rw [(γ _).source]
   exact hAt f0 hf0 w
  ·intro w
   change action (oneSkeletonVertexOfPoint w).2 (γ (oneSkeletonVertexOfPoint w).1 1)=_
   rw [(γ _).target]
   exact hAt f1 hf1 w

/-- The fixed universal join has dimension m−1. Connectivity through
m−1, rather than the m−2 needed for a map, joins ANY two existing
continuous equivariant maps by an actual equivariant homotopy. -/
theorem exists_equivariant_universalJoinHomotopy
    {m k:ℕ}{G X:Type*} [AddGroup G] [Fintype G] [TopologicalSpace X]
    (hm:m≤k+1) (hX:NullConnectedSpace k X)
    (action:G→X≃ₜX) (hAction:IsContinuousAddAction action)
    (f0 f1:C(simplicialRealization (universalJoinComplex m G),X))
    (hf0:IsEquivariantJoinMap (universalJoinComplex m G) universalJoinComplex_invariant action f0)
    (hf1:IsEquivariantJoinMap (universalJoinComplex m G) universalJoinComplex_invariant action f1):
    ∃H:C(simplicialRealization (universalJoinComplex m G)×I,X),
      (∀x,H (x,0)=f0 x) ∧(∀x,H (x,1)=f1 x) ∧
      ∀g x t,H (translateInvariantRealization (universalJoinComplex m G)
        universalJoinComplex_invariant g x,t)=action g (H (x,t)):=by
  let K:=universalJoinComplex m G
  let V:=universalJoinSkeleton m G 1
  have hVK:V≤K:=fun _ h=>h.1
  obtain ⟨qV,hqV,hqV0,hqV1⟩:=exists_equivariant_joinVertexHomotopy hX action hAction f0 f1 hf0 hf1
  have aux:∀s:ℕ,∀(B:PreAbstractSimplicialComplex (Fin m×G))
      (hBK:B≤K)(hVB:V≤B)(hB:IsJoinTranslationInvariant B),
      (missingFaces B K).card=s→
      ∀q:C(simplicialRealization B,C(I,X)),
      IsEquivariantJoinMap B hB (joinPathAction action) q→
      (∀w:simplicialRealization B,q w 0=f0 ⟨w.1,simplicialRealization_mono hBK w.2⟩)→
      (∀w:simplicialRealization B,q w 1=f1 ⟨w.1,simplicialRealization_mono hBK w.2⟩)→
      ∃q':C(simplicialRealization K,C(I,X)),
        IsEquivariantJoinMap K universalJoinComplex_invariant (joinPathAction action) q' ∧
        (∀w,q' w 0=f0 w) ∧∀w,q' w 1=f1 w:=by
    intro s
    induction s using Nat.strong_induction_on with
    |h s ih=>
      intro B hBK hVB hB hCount q hq h0 h1
      by_cases hKB:K≤B
      ·have hEq:B=K:=le_antisymm hBK hKB
       subst B
       exact ⟨q,hq,h0,h1⟩
      ·obtain ⟨R,hRK,hAbsent,hRne,hMinimal⟩:=exists_minimal_missing_face_global B K hKB
       have hR:IsUniversalJoinFace R:=hRK
       have hTwo:2≤R.card:=by
         by_contra hNot
         exact hAbsent (hVB ⟨hR,by omega⟩)
       let j:=R.card-2
       have hCard:R.card=j+2:=by dsimp [j];omega
       have hj:j+1≤k:=by
         have hRm:=universalJoinFace_card_le hR
         dsimp [j]
         omega
       have hOld:universalJoinSkeleton m G (j+1)≤B:=by
         intro S hS
         apply hMinimal S hS.1
         have hSc:=hS.2
         omega
       let B':=B⊔joinFaceOrbitComplex R
       have hB'K:B'≤K:=sup_le hBK (joinFaceOrbitComplex_le_universalJoinComplex R hR)
       have hVB':V≤B':=le_trans hVB le_sup_left
       have hB':IsJoinTranslationInvariant B':=joinOrbitAttach_invariant B hB R
       have hSmaller:(missingFaces B' K).card<s:=by
         rw [←hCount]
         exact Finset.card_lt_card (missingFaces_joinOrbitAttach_ssubset B R hR hAbsent)
       obtain ⟨q',hOldQ,hEquiv,hNew0,hNew1⟩:=exists_equivariant_joinOrbitHomotopy
         K B universalJoinComplex_invariant hB hBK hOld R hR hRK hCard hAbsent
         hX hj action hAction f0 f1 hf0 hf1 q hq h0 h1
       exact ih (missingFaces B' K).card hSmaller B' hB'K hVB' hB' rfl
         q' hEquiv hNew0 hNew1
  obtain ⟨q,hq,h0,h1⟩:=aux (missingFaces V K).card V hVK le_rfl
    universalJoinSkeleton_invariant rfl qV hqV hqV0 hqV1
  refine ⟨q.uncurry,h0,h1,?_⟩
  intro g x t
  exact congrArg (fun γ:C(I,X)=>γ t) (hq g x)

end FairDivision.Topology.Volovikov
