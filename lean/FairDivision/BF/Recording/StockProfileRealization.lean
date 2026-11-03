import FairDivision.BF.Recording.ChildProfiles
import FairDivision.BF.Recording.RealItemCoordinates
import FairDivision.Topology.VariableDummyVertexBuild
import FairDivision.Topology.VariableDummyForcedVertex
import FairDivision.Topology.VariableDummyStockRealization
import FairDivision.Topology.NerveConnectivity.RealizationEquiv

/-!
# Exact local-stock auxiliary realization in common child-profile coordinates

The source is the EXISTING corrected variable-stock complex on real labels
and d local dummy labels. Forget the labels and keep each real bundle and
its dummy count. The inverse uses the existing proved profile reconstruction.
Its arbitrary fallback is used only on invalid ambient tuples, never on a
realized support. Both simplex maps retain the literal probability weights.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

namespace FairDivision.BF.Recording

open FairDivision.Topology FairDivision.Topology.NerveConnectivity

abbrev LocalVertex (p a q m d:ℕ):=
  VariableUnlabeledVertex p (m+d) (dummyLabels m d) (fun _=>a*q-1) (fun _=>a)

def localStockComplex (p a q m:ℕ) (E:Finset (Fin m)) (d:ℕ):
    PreAbstractSimplicialComplex (LocalVertex p a q m d):=
  variableStockComplex (dummyLabels m d) (E.map (realEmbedding m d))
    (fun _:Fin p=>a*q-1) (fun _=>a)

/-- Same real bundle and dummy count, now in the fixed finite coordinates. -/
def localToChild {p a q m d:ℕ} (u:LocalVertex p a q m d):ChildProfile p a q m:=
  fun i=>⟨(realPart (u.1 i).1,⟨(u.1 i).2,by
    have h:=variableProfile_dummy_le_cap u i;omega⟩),by
      rw [card_realPart_of_disjoint _ (variableProfile_real_disjoint_dummy u i)]
      exact variableProfile_card u i⟩

@[simp] theorem localToChild_dummy {p a q m d:ℕ} (u:LocalVertex p a q m d) (i:Fin p):
    dummyCount (localToChild u i)=(u.1 i).2:=rfl

theorem localToChild_realMap {p a q m d:ℕ} (u:LocalVertex p a q m d) (i:Fin p):
    (real (localToChild u i)).map (realEmbedding m d)=(u.1 i).1:=
  realMap_realPart_of_disjoint _ (variableProfile_real_disjoint_dummy u i)

/-- Precisely the singleton-profile conditions for the existing constructor. -/
def ChildAdmissible {p a q m:ℕ} (d:ℕ) (b:ChildProfile p a q m):Prop:=
  (∀i j:Fin p,i≠j→Disjoint (real (b i)) (real (b j))) ∧
  (∑i:Fin p,dummyCount (b i))≤d

theorem localToChild_admissible {p a q m d:ℕ} (u:LocalVertex p a q m d):
    ChildAdmissible d (localToChild u):=by
  constructor
  ·intro i j hij
   apply Finset.disjoint_left.mpr
   intro g hgi hgj
   have hi:realEmbedding m d g∈(u.1 i).1:=by
     rw [←localToChild_realMap u i]
     exact Finset.mem_map.mpr ⟨g,hgi,rfl⟩
   have hj:realEmbedding m d g∈(u.1 j).1:=by
     rw [←localToChild_realMap u j]
     exact Finset.mem_map.mpr ⟨g,hgj,rfl⟩
   exact (Finset.disjoint_left.mp (variableProfile_real_pairwise u i j hij)) hi hj
  ·simpa only [localToChild_dummy,card_dummyLabels] using variableProfile_dummy_budget u

/-- Existing exact dummy-reserve construction, with no new labeling proof. -/
theorem exists_local_of_child {p a q m d:ℕ} (b:ChildProfile p a q m)
    (hb:ChildAdmissible d b):
    ∃u:LocalVertex p a q m d,∀i:Fin p,
      u.1 i=((real (b i)).map (realEmbedding m d),dummyCount (b i)):=by
  apply exists_variable_vertex_of_profile
  ·intro i
   exact realImage_disjoint_dummies (real (b i))
  ·intro i j hij
   exact (Finset.disjoint_map (realEmbedding m d)).mpr (hb.1 i j hij)
  ·intro i
   simpa only [Finset.card_map] using vertex_card (b i)
  ·intro i
   exact dummyCount_le (b i)
  ·simpa only [card_dummyLabels] using hb.2

/-- Every tuple belonging to an actual face has valid singleton data. -/
theorem childAdmissible_of_face {p a q m d:ℕ} (E:Finset (Fin m))
    (T:Finset (ChildProfile p a q m))
    (hT:T∈availableAuxiliaryComplex p a q m E d) {b:ChildProfile p a q m} (hb:b∈T):
    ChildAdmissible d b:=by
  constructor
  ·intro i j hij
   apply (hT.2.1 i j hij).mono
   ·intro g hg
    exact Finset.mem_biUnion.mpr ⟨b,hb,hg⟩
   ·intro g hg
    exact Finset.mem_biUnion.mpr ⟨b,hb,hg⟩
  ·apply le_trans _ hT.2.2.1
   exact Finset.sum_le_sum (fun i _=>Finset.le_sup (f:=fun c=>dummyCount (c i)) hb)

/-- Numerical face transport for ANY tuple map preserving the literal real
images and dummy counts on the given support. -/
theorem localFace_to_childFace {p a q m d:ℕ} (E:Finset (Fin m))
    (S:Finset (LocalVertex p a q m d)) (hS:S∈localStockComplex p a q m E d):
    S.image localToChild∈availableAuxiliaryComplex p a q m E d:=by
  classical
  have hNum:=(variableFace_iff S).mp hS.1.2
  have hPool:∀i:Fin p,(childRealPool (S.image localToChild) i).map (realEmbedding m d)=
      variableRealPool S i:=by
    intro i
    ext z
    constructor
    ·intro hz
     obtain ⟨g,hg,rfl⟩:=Finset.mem_map.mp hz
     obtain ⟨b,hb,hgb⟩:=Finset.mem_biUnion.mp hg
     obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hb
     refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,u,hu,?_⟩
     rw [←localToChild_realMap u i]
     exact Finset.mem_map.mpr ⟨g,hgb,rfl⟩
    ·intro hz
     obtain ⟨_,u,hu,hzu⟩:=Finset.mem_filter.mp hz
     rw [←localToChild_realMap u i] at hzu
     obtain ⟨g,hg,rfl⟩:=Finset.mem_map.mp hzu
     exact Finset.mem_map.mpr ⟨g,Finset.mem_biUnion.mpr
       ⟨localToChild u,Finset.mem_image.mpr ⟨u,hu,rfl⟩,hg⟩,rfl⟩
  refine ⟨hS.1.1.image _,?_,?_,?_⟩
  ·intro i j hij
   apply Finset.disjoint_left.mpr
   intro g hgi hgj
   apply (Finset.disjoint_left.mp (hNum.1 i j hij))
   ·rw [←hPool i]
    exact Finset.mem_map.mpr ⟨g,hgi,rfl⟩
   ·rw [←hPool j]
    exact Finset.mem_map.mpr ⟨g,hgj,rfl⟩
  ·have hMax:∀i:Fin p,childDummyMax (S.image localToChild) i=variableDummyMax S i:=by
     intro i
     simp [childDummyMax,variableDummyMax,Finset.sup_image,localToChild_dummy,Function.comp_def]
   simpa only [hMax,card_dummyLabels] using hNum.2
  ·intro i g hg
   have hz:realEmbedding m d g∈variableRealPool S i:=by
     rw [←hPool i]
     exact Finset.mem_map.mpr ⟨g,hg,rfl⟩
   obtain ⟨_,u,hu,hzu⟩:=Finset.mem_filter.mp hz
   obtain ⟨h,hh,he⟩:=Finset.mem_map.mp (hS.2 u hu i hzu)
   exact (realEmbedding m d).injective he ▸hh

/-- The SAME exact profile matching gives a homeomorphism of realizations.
Nonemptiness supplies only an unused-vertex fallback, never a lottery or
map-existence oracle. It is supplied by the existing connectivity theorem. -/
def stockProfileHomeomorph {p a q m d:ℕ} (E:Finset (Fin m))
    (hNonempty:Nonempty (simplicialRealization (localStockComplex p a q m E d))):
    simplicialRealization (localStockComplex p a q m E d)≃ₜ
      simplicialRealization (availableAuxiliaryComplex p a q m E d):=by
  classical
  let x₀:=Classical.choice hNonempty
  let u₀ : LocalVertex p a q m d :=
    Classical.choose (finiteSimplexSupport_nonempty x₀.1)
  let back:ChildProfile p a q m→LocalVertex p a q m d:=fun b=>
    if hb:ChildAdmissible d b then Classical.choose (exists_local_of_child b hb) else u₀
  have hBack:∀b (hb:ChildAdmissible d b) (i:Fin p),
      (back b).1 i=((real (b i)).map (realEmbedding m d),dummyCount (b i)):=by
    intro b hb i
    simp only [back,dif_pos hb]
    exact Classical.choose_spec (exists_local_of_child b hb) i
  have hInverse:∀u:LocalVertex p a q m d,back (localToChild u)=u:=by
    intro u
    apply Subtype.ext
    funext i
    rw [hBack _ (localToChild_admissible u) i,localToChild_realMap,localToChild_dummy]
  have hInverse':∀b:ChildProfile p a q m,ChildAdmissible d b→localToChild (back b)=b:=by
    intro b hb
    funext i
    apply Subtype.ext
    apply Prod.ext
    ·change realPart ((back b).1 i).1=real (b i)
     rw [hBack b hb i,realPart_realMap]
    ·apply Fin.ext
     change ((back b).1 i).2=dummyCount (b i)
     rw [hBack b hb i]
  apply realizationHomeomorphOfVertexMaps (localStockComplex p a q m E d)
    (availableAuxiliaryComplex p a q m E d) localToChild back
  ·exact localFace_to_childFace E
  ·intro T hT
   have hGood:∀b∈T,ChildAdmissible d b:=fun b hb=>childAdmissible_of_face E T hT hb
   have hPool:∀i:Fin p,variableRealPool (T.image back) i=
       (childRealPool T i).map (realEmbedding m d):=by
     intro i
     ext z
     constructor
     ·intro hz
      obtain ⟨_,u,hu,hzu⟩:=Finset.mem_filter.mp hz
      obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp hu
      rw [hBack b (hGood b hb) i] at hzu
      obtain ⟨g,hg,rfl⟩:=Finset.mem_map.mp hzu
      exact Finset.mem_map.mpr ⟨g,Finset.mem_biUnion.mpr ⟨b,hb,hg⟩,rfl⟩
     ·intro hz
      obtain ⟨g,hg,rfl⟩:=Finset.mem_map.mp hz
      obtain ⟨b,hb,hgb⟩:=Finset.mem_biUnion.mp hg
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,back b,Finset.mem_image.mpr ⟨b,hb,rfl⟩,?_⟩
      rw [hBack b (hGood b hb) i]
      exact Finset.mem_map.mpr ⟨g,hgb,rfl⟩
   have hMax:∀i:Fin p,variableDummyMax (T.image back) i=childDummyMax T i:=by
     intro i
     apply le_antisymm
     ·apply Finset.sup_le
      intro u hu
      obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp hu
      change ((back b).1 i).2≤childDummyMax T i
      rw [hBack b (hGood b hb) i]
      exact Finset.le_sup (f:=fun c=>dummyCount (c i)) hb
     ·apply Finset.sup_le
      intro b hb
      have hLe:=Finset.le_sup (s:=T.image back) (f:=fun u=> (u.1 i).2)
        (Finset.mem_image.mpr ⟨b,hb,rfl⟩)
      simpa only [variableDummyMax,hBack b (hGood b hb) i] using hLe
   refine ⟨⟨hT.1.image _,(variableFace_iff _).mpr ⟨?_,?_⟩⟩,?_⟩
   ·intro i j hij
    rw [hPool i,hPool j]
    exact (Finset.disjoint_map (realEmbedding m d)).mpr (hT.2.1 i j hij)
   ·simpa only [hMax,card_dummyLabels] using hT.2.2.1
   ·intro u hu i z hz
    obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp hu
    rw [hBack b (hGood b hb) i] at hz
    obtain ⟨g,hg,rfl⟩:=Finset.mem_map.mp hz
    exact Finset.mem_map.mpr ⟨g,hT.2.2.2 i (Finset.mem_biUnion.mpr ⟨b,hb,hg⟩),rfl⟩
  ·intro S hS u hu
   exact hInverse u
  ·intro T hT b hb
   exact hInverse' b (childAdmissible_of_face E T hT hb)

end FairDivision.BF.Recording
