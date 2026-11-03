import FairDivision.BF.Recording.GraphFamily
import FairDivision.Topology.VariableDummySimplicialHomotopy

/-!
# The manuscript's nested-dummy exchange path inside the two-bundle union

Start at the endpoint with fewer dummies. While a dummy is missing, insert
its next canonical label and remove a real item absent from the destination.
Once the dummy counts agree, exchange the remaining real differences. Every
step is an ACTUAL edge of the recording graph. The count of real differences
strictly decreases, and no intermediate vertex or edge uses another item.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

open scoped unitInterval Topology

namespace FairDivision.BF.Recording

open FairDivision.Topology
open FairDivision.Topology.NerveConnectivity

private theorem vertexPoint_support {a q m:ℕ} (b:Vertex a q m):
    finiteSimplexSupport (vertexPoint b).1={b}:=by
  change finiteSimplexSupport (stdSimplex.vertex b)={b}
  exact finiteSimplexSupport_vertex b

/-- Stock restriction at the actual support of a graph point. -/
def stockSpace {a q m:ℕ} (E:Finset (Fin m)) (d:ℕ):Set (Space a q m):=
  {x|∀b∈finiteSimplexSupport x.1,real b⊆E ∧dummyCount b≤d}

@[simp] theorem vertexPoint_mem_stockSpace {a q m:ℕ}
    (E:Finset (Fin m)) (d:ℕ) (b:Vertex a q m):
    vertexPoint b∈stockSpace E d↔real b⊆E ∧dummyCount b≤d:=by
  change (∀c∈finiteSimplexSupport (vertexPoint b).1,real c⊆E ∧dummyCount c≤d)↔_
  rw [vertexPoint_support]
  simp only [Finset.mem_singleton,forall_eq]

/-- An actual graph edge, parameterized by its literal endpoint lottery. -/
def graphEdgePath {a q m:ℕ} (b c:Vertex a q m) (hbc:adjacent b c):
    Path (vertexPoint b) (vertexPoint c):=by
  classical
  have hPair:({b,c}:Finset (Vertex a q m))∈graphComplex a q m:=by
    refine ⟨Finset.insert_nonempty b {c},?_,?_⟩
    ·simpa only [Finset.card_singleton] using Finset.card_insert_le b {c}
    intro u hu w hw huw
    simp only [Finset.mem_insert,Finset.mem_singleton] at hu hw
    rcases hu with rfl|rfl <;>rcases hw with rfl|rfl
    ·exact False.elim (huw rfl)
    ·exact hbc
    ·exact adjacent_symm hbc
    ·exact False.elim (huw rfl)
  let segment:I→stdSimplex ℝ (Vertex a q m):=
    fun t=>variableLotterySegment (vertexPoint b).1 (vertexPoint c).1 t
  have hSupport:∀t,finiteSimplexSupport (segment t)⊆({b,c}:Finset (Vertex a q m)):=by
    intro t u hu
    have hUnion:=finiteSimplexSupport_variableLotterySegment_subset
      (vertexPoint b).1 (vertexPoint c).1 t hu
    simpa only [vertexPoint_support,Finset.mem_union,Finset.mem_singleton,
      Finset.mem_insert] using hUnion
  have hMem:∀t,segment t∈simplicialRealization (graphComplex a q m):=fun t=>
    ((graphComplex a q m).isRelLowerSet_faces hPair).2
      (hSupport t) (finiteSimplexSupport_nonempty _)
  refine ⟨⟨fun t=>⟨segment t,hMem t⟩,?_⟩,?_,?_⟩
  ·apply Continuous.subtype_mk
   exact variableLotterySegment_continuous.comp (continuous_id.prodMk
     (continuous_const.prodMk continuous_const))
  ·apply Subtype.ext
   exact variableLotterySegment_zero _ _
  ·apply Subtype.ext
   exact variableLotterySegment_one _ _

theorem graphEdgePath_mem_stock {a q m:ℕ} (E:Finset (Fin m)) (d:ℕ)
    (b c:Vertex a q m) (hbc:adjacent b c)
    (hb:real b⊆E ∧dummyCount b≤d) (hc:real c⊆E ∧dummyCount c≤d):
    ∀t,graphEdgePath b c hbc t∈stockSpace E d:=by
  intro t u hu
  have hSub:finiteSimplexSupport (graphEdgePath b c hbc t).1⊆({b,c}:Finset _):=by
    change finiteSimplexSupport
      (variableLotterySegment (vertexPoint b).1 (vertexPoint c).1 t)⊆_
    intro w hw
    have hUnion:=finiteSimplexSupport_variableLotterySegment_subset
      (vertexPoint b).1 (vertexPoint c).1 t hw
    simpa only [vertexPoint_support,Finset.mem_union,Finset.mem_singleton,
      Finset.mem_insert] using hUnion
  rcases Finset.mem_insert.mp (hSub hu) with he|he
  ·simpa only [he] using hb
  ·simpa only [Finset.mem_singleton.mp he] using hc

/-- With nondecreasing dummy counts, the manuscript's dummy-first/real-next
sequence gives a path confined to the prescribed real stock and dummy prefix. -/
theorem recordingVertices_joinedIn_nested {a q m:ℕ}
    (E:Finset (Fin m)) (d:ℕ) (b c:Vertex a q m)
    (hOrder:dummyCount b≤dummyCount c)
    (hb:real b⊆E ∧dummyCount b≤d) (hc:real c⊆E ∧dummyCount c≤d):
    JoinedIn (stockSpace E d) (vertexPoint b) (vertexPoint c):=by
  classical
  have aux:∀k:ℕ,∀b:Vertex a q m,dummyCount b≤dummyCount c→
      (real b⊆E ∧dummyCount b≤d)→(real b\real c).card=k→
      JoinedIn (stockSpace E d) (vertexPoint b) (vertexPoint c):=by
    intro k
    induction k using Nat.strong_induction_on with
    |h k ih=>
      intro b hOrder hb hDiff
      by_cases hEq:b=c
      ·subst b
       exact JoinedIn.refl ((vertexPoint_mem_stockSpace E d c).mpr hc)
      have hNotSubset:¬real b⊆real c:=by
        intro hSub
        have hCardB:=vertex_card b
        have hCardC:=vertex_card c
        have hCardLe:=Finset.card_le_card hSub
        have hCards:(real c).card≤(real b).card:=by omega
        have hReal:real b=real c:=Finset.eq_of_subset_of_card_le hSub hCards
        have hDummy:dummyCount b=dummyCount c:=by rw [hReal] at hCardB;omega
        apply hEq
        apply Subtype.ext
        apply Prod.ext hReal
        exact Fin.ext hDummy
      obtain ⟨x,hx⟩:=Finset.sdiff_nonempty.mpr hNotSubset
      have hxB:x∈real b:=(Finset.mem_sdiff.mp hx).1
      have hxC:x∉real c:=(Finset.mem_sdiff.mp hx).2
      by_cases hMore:dummyCount b<dummyCount c
      ·let u:Vertex a q m:=⟨((real b).erase x,
          ⟨dummyCount b+1,by have hCap:=dummyCount_le c;omega⟩),by
            have hOld:=vertex_card b
            have hErase:=Finset.card_erase_of_mem hxB
            have hPos:=Finset.card_pos.mpr ⟨x,hxB⟩
            change ((real b).erase x).card+(dummyCount b+1)=a*q-1
            omega⟩
       have hNe:b≠u:=by
         intro he
         have hCount:=congrArg dummyCount he
         change dummyCount b=dummyCount b+1 at hCount
         omega
       have hAdj:adjacent b u:=⟨hNe,Or.inr (Or.inr (Or.inl ⟨rfl,x,hxB,rfl⟩))⟩
       have hu:real u⊆E ∧dummyCount u≤d:=
         ⟨(Finset.erase_subset _ _).trans hb.1,by change dummyCount b+1≤d;omega⟩
       have hDiffU:real u\real c=(real b\real c).erase x:=by
         change (real b).erase x\real c=(real b\real c).erase x
         exact Finset.erase_sdiff_comm _ _ _
       have hSmaller:(real u\real c).card<k:=by
         rw [hDiffU,Finset.card_erase_of_mem hx,hDiff]
         have hPos:0<k:=by rw [←hDiff];exact Finset.card_pos.mpr ⟨x,hx⟩
         omega
       have hTail:=ih (real u\real c).card hSmaller u
         (by change dummyCount b+1≤dummyCount c;omega) hu rfl
       exact JoinedIn.trans
         (⟨graphEdgePath b u hAdj,graphEdgePath_mem_stock E d b u hAdj hb hu⟩:
           JoinedIn (stockSpace E d) (vertexPoint b) (vertexPoint u)) hTail
      ·have hSame:dummyCount b=dummyCount c:=by omega
       have hNotReverse:¬real c⊆real b:=by
         intro hSub
         have hCardB:=vertex_card b
         have hCardC:=vertex_card c
         have hEqualCard:(real b).card=(real c).card:=by omega
         exact hNotSubset (Finset.eq_of_subset_of_card_le hSub (by omega)).symm.subset
       obtain ⟨y,hy⟩:=Finset.sdiff_nonempty.mpr hNotReverse
       have hyC:y∈real c:=(Finset.mem_sdiff.mp hy).1
       have hyB:y∉real b:=(Finset.mem_sdiff.mp hy).2
       let u:Vertex a q m:=⟨(insert y ((real b).erase x),b.1.2),by
         have hOld:=vertex_card b
         have hErase:=Finset.card_erase_of_mem hxB
         have hPos:=Finset.card_pos.mpr ⟨x,hxB⟩
         have hyErase:y∉(real b).erase x:=fun h=>hyB (Finset.mem_of_mem_erase h)
         change (insert y ((real b).erase x)).card+dummyCount b=a*q-1
         rw [Finset.card_insert_of_notMem hyErase]
         omega⟩
       have hNe:b≠u:=by
         intro he
         have hReal:=congrArg real he
         have hyU:y∈real u:=Finset.mem_insert_self _ _
         exact hyB (hReal.symm▸hyU)
       have hAdj:adjacent b u:=⟨hNe,Or.inl ⟨rfl,x,hxB,y,hyB,rfl⟩⟩
       have hu:real u⊆E ∧dummyCount u≤d:=by
         refine ⟨?_,hb.2⟩
         intro z hz
         rcases Finset.mem_insert.mp hz with he|hz
         ·exact he.symm▸hc.1 hyC
         ·exact hb.1 (Finset.mem_of_mem_erase hz)
       have hDiffU:real u\real c=(real b\real c).erase x:=by
         change insert y ((real b).erase x)\real c=(real b\real c).erase x
         ext z
         simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_erase]
         constructor
         ·rintro ⟨he|⟨hzx,hzb⟩,hzc⟩
          ·exact False.elim (hzc (he.symm▸hyC))
          ·exact ⟨hzx,hzb,hzc⟩
         ·rintro ⟨hzx,hzb,hzc⟩
          exact ⟨Or.inr ⟨hzx,hzb⟩,hzc⟩
       have hSmaller:(real u\real c).card<k:=by
         rw [hDiffU,Finset.card_erase_of_mem hx,hDiff]
         have hPos:0<k:=by rw [←hDiff];exact Finset.card_pos.mpr ⟨x,hx⟩
         omega
       have hTail:=ih (real u\real c).card hSmaller u (by exact hSame.le) hu rfl
       exact JoinedIn.trans
         (⟨graphEdgePath b u hAdj,graphEdgePath_mem_stock E d b u hAdj hb hu⟩:
           JoinedIn (stockSpace E d) (vertexPoint b) (vertexPoint u)) hTail
  exact aux (real b\real c).card b hOrder hb rfl

/-- Start at the endpoint with fewer dummies, as in the manuscript. -/
theorem recordingVertices_joinedIn_stock {a q m:ℕ}
    (E:Finset (Fin m)) (d:ℕ) (b c:Vertex a q m)
    (hb:real b⊆E ∧dummyCount b≤d) (hc:real c⊆E ∧dummyCount c≤d):
    JoinedIn (stockSpace E d) (vertexPoint b) (vertexPoint c):=by
  rcases le_total (dummyCount b) (dummyCount c) with h|h
  ·exact recordingVertices_joinedIn_nested E d b c h hb hc
  ·exact (recordingVertices_joinedIn_nested E d c b h hc hb).symm

/-- The stock condition controls the LITERAL available item pool. -/
theorem available_subset_of_stock {a q m:ℕ} (E:Finset (Fin m)) (d:ℕ)
    (x:Space a q m) (hx:x∈stockSpace E d):
    available x⊆E.map (realEmbedding m a)∪initialDummies m a d:=by
  intro z hz
  obtain ⟨b,hb,hzb⟩:=Finset.mem_biUnion.mp hz
  rcases Finset.mem_union.mp hzb with hzReal|hzDummy
  ·exact Finset.mem_union_left _ (Finset.map_subset_map.mpr (hx b hb).1 hzReal)
  ·exact Finset.mem_union_right _ (initialDummies_mono (hx b hb).2 hzDummy)

end FairDivision.BF.Recording
