import FairDivision.BF.Applications.GraphDensityBasics
import Mathlib.Combinatorics.SimpleGraph.Star

/-!
# The manuscript's star-leaf transfer

Mathlib supplies the actual star graph. The density proof detects that
induced graph by its edge count and an edgeless deletion, then moves one
noncentral leaf between the two actual owner-map bundles. The finite
iteration using these identities is kept in the single-remainder proof.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.Applications

open FairDivision
open scoped Classical

variable {V:Type*} [Fintype V]

/-- Exactly the graph configuration detected in the paper's exceptional
case: s-1 edges, all incident with one vertex. -/
def IsDensityStar (G:SimpleGraph V) (S:Finset V):Prop:=
  ∃c∈S,inducedEdges G S=S.card-1 ∧inducedEdges G (S.erase c)=0

theorem internalGraph_eq_bot_of_edges_zero (G:SimpleGraph V) (S:Finset V)
    (h:inducedEdges G S=0):internalGraph G S=⊥:=by
  apply SimpleGraph.edgeFinset_eq_empty.mp
  exact Finset.card_eq_zero.mp h

/-- Detect all neighbors of the center using the imported incident-edge
formula and the equality case of finite subset cardinality. -/
theorem densityStar_center_neighbors (G:SimpleGraph V) (S:Finset V) (c:V)
    (hc:c∈S) (hEdges:inducedEdges G S=S.card-1)
    (hDelete:inducedEdges G (S.erase c)=0):
    (internalGraph G S).neighborFinset c=S.erase c:=by
  have hD:=inducedDegree_le_edges G S c
  have hErase:=inducedEdges_erase G S c
  have hDegree:inducedDegree G S c=S.card-1:=by omega
  have hSub:(internalGraph G S).neighborFinset c⊆S.erase c:=by
    intro y hy
    have hcy:=((internalGraph G S).mem_neighborFinset c y).mp hy
    exact Finset.mem_erase.mpr ⟨by intro he;subst y;exact G.irrefl hcy.2.2,hcy.2.1⟩
  apply Finset.eq_of_subset_of_card_le hSub
  rw [Finset.card_erase_of_mem hc]
  exact hDegree.ge

/-- This is the literal Mathlib star graph on the induced vertex set. -/
theorem densityStar_induce_eq_star (G:SimpleGraph V) (S:Finset V) (c:V)
    (hc:c∈S) (hEdges:inducedEdges G S=S.card-1)
    (hDelete:inducedEdges G (S.erase c)=0):
    G.induce (S:Set V)=SimpleGraph.starGraph (⟨c,hc⟩:↥(S:Set V)):=by
  have hNeighbors:=densityStar_center_neighbors G S c hc hEdges hDelete
  have hBot:=internalGraph_eq_bot_of_edges_zero G (S.erase c) hDelete
  ext x y
  rw [SimpleGraph.starGraph_adj]
  change G.Adj x.val y.val↔x≠y ∧(x=⟨c,hc⟩∨y=⟨c,hc⟩)
  constructor
  · intro hxy
    refine ⟨fun he=>G.irrefl (congrArg Subtype.val he ▸hxy),?_⟩
    by_cases hxc:x.val=c
    ·exact Or.inl (Subtype.ext hxc)
    ·right
     apply Subtype.ext
     by_contra hyc
     have hAdj:(internalGraph G (S.erase c)).Adj x.val y.val:=
       ⟨Finset.mem_erase.mpr ⟨hxc,x.property⟩,
        Finset.mem_erase.mpr ⟨hyc,y.property⟩,hxy⟩
     rw [hBot] at hAdj
     exact hAdj
  · rintro ⟨hne,hxc|hyc⟩
    ·have hyc:y.val≠c:=by intro he;exact hne (hxc.trans (Subtype.ext he).symm)
     have hy:y.val∈(internalGraph G S).neighborFinset c:=by
       rw [hNeighbors]
       exact Finset.mem_erase.mpr ⟨hyc,y.property⟩
     have hcy:=((internalGraph G S).mem_neighborFinset c y.val).mp hy
     simpa only [congrArg Subtype.val hxc] using hcy.2.2
    ·have hxc:x.val≠c:=by intro he;exact hne ((Subtype.ext he).trans hyc.symm)
     have hx:x.val∈(internalGraph G S).neighborFinset c:=by
       rw [hNeighbors]
       exact Finset.mem_erase.mpr ⟨hxc,x.property⟩
     have hcx:=((internalGraph G S).mem_neighborFinset c x.val).mp hx
     simpa only [congrArg Subtype.val hyc] using hcx.2.2.symm

/-- Every noncentral leaf has exactly the Mathlib star degree one. -/
theorem densityStar_leaf_degree (G:SimpleGraph V) (S:Finset V) (c z:V)
    (hc:c∈S) (hEdges:inducedEdges G S=S.card-1)
    (hDelete:inducedEdges G (S.erase c)=0) (hz:z∈S) (hzc:z≠c):
    inducedDegree G S z=1:=by
  have hNeighbors:=densityStar_center_neighbors G S c hc hEdges hDelete
  have hBot:=internalGraph_eq_bot_of_edges_zero G (S.erase c) hDelete
  have hEq:(internalGraph G S).neighborFinset z={c}:=by
    ext y
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_singleton]
    constructor
    · intro hzy
      by_contra hyc
      have hAdj:(internalGraph G (S.erase c)).Adj z y:=
        ⟨Finset.mem_erase.mpr ⟨hzc,hz⟩,
          Finset.mem_erase.mpr ⟨hyc,hzy.2.1⟩,hzy.2.2⟩
      rw [hBot] at hAdj
      exact hAdj
    · intro hy
      subst y
      have hzN:z∈(internalGraph G S).neighborFinset c:=by
        rw [hNeighbors]
        exact Finset.mem_erase.mpr ⟨hzc,hz⟩
      exact (((internalGraph G S).mem_neighborFinset c z).mp hzN).symm
  change ((internalGraph G S).neighborFinset z).card=1
  rw [hEq,Finset.card_singleton]

/-- Removing a leaf gives exactly one fewer edge. -/
theorem densityStar_erase_leaf_edges (G:SimpleGraph V) (S:Finset V) (c z:V)
    (hc:c∈S) (hEdges:inducedEdges G S=S.card-1)
    (hDelete:inducedEdges G (S.erase c)=0) (hz:z∈S) (hzc:z≠c):
    inducedEdges G (S.erase z)=S.card-2:=by
  rw [inducedEdges_erase,densityStar_leaf_degree G S c z hc hEdges hDelete hz hzc,hEdges]
  omega

/-- Add the donated leaf to an edgeless small part. Its new edge count is
exactly the new vertex's induced degree, at most the old part size. -/
theorem edges_insert_into_edgeless (G:SimpleGraph V) (S:Finset V) (z:V)
    (hz:z∉S) (hEmpty:inducedEdges G S=0):
    inducedEdges G (insert z S)=inducedDegree G (insert z S) z ∧
      inducedEdges G (insert z S)≤S.card:=by
  have hErase:=inducedEdges_erase G (insert z S) z
  have hLE:=inducedDegree_le_edges G (insert z S) z
  have hEq:inducedEdges G (insert z S)=inducedDegree G (insert z S) z:=by
    simp only [Finset.erase_insert hz,hEmpty] at hErase
    omega
  refine ⟨hEq,?_⟩
  rw [hEq]
  have h:=inducedDegree_le_card_sub_one G (insert z S) z (Finset.mem_insert_self _ _)
  simpa only [Finset.card_insert_of_notMem hz,Nat.add_sub_cancel] using h

/-- If the inserted vertex has all possible r edges, the new large part
is again the actual star, now centered at that inserted vertex. -/
theorem inserted_full_degree_is_densityStar (G:SimpleGraph V) (S:Finset V) (z:V)
    (hz:z∉S) (hEmpty:inducedEdges G S=0)
    (hFull:inducedEdges G (insert z S)=S.card):IsDensityStar G (insert z S):=by
  refine ⟨z,Finset.mem_insert_self _ _,?_,?_⟩
  · rw [hFull,Finset.card_insert_of_notMem hz]
    omega
  · simpa only [Finset.erase_insert hz] using hEmpty

/-- Literal owner change used for the leaf transfer. -/
def transferVertex {k m:ℕ} (A:Allocation k m) (z:Fin m) (i:Fin k):Allocation k m:=
  Function.update A z i

theorem transferVertex_recipient {k m:ℕ} (A:Allocation k m) (z:Fin m) (i:Fin k)
    (hi:A z≠i):bundle (transferVertex A z i) i=insert z (bundle A i):=by
  classical
  ext x
  simp only [bundle,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
  change Function.update A z i x=i ↔ x=z ∨ A x=i
  by_cases hx:x=z
  · subst x; simp
  · simp [Function.update_of_ne hx,hx]

theorem transferVertex_donor {k m:ℕ} (A:Allocation k m) (z:Fin m) (i j:Fin k)
    (hOwner:A z=j) (hij:i≠j):
    bundle (transferVertex A z i) j=(bundle A j).erase z:=by
  classical
  ext x
  simp only [bundle,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase]
  change Function.update A z i x=j ↔ x≠z ∧ A x=j
  by_cases hx:x=z
  · subst x; simp [hij]
  · simp [Function.update_of_ne hx,hx]

theorem transferVertex_other {k m:ℕ} (A:Allocation k m) (z:Fin m) (i j l:Fin k)
    (hOwner:A z=j) (hli:l≠i) (hlj:l≠j):
    bundle (transferVertex A z i) l=bundle A l:=by
  classical
  ext x
  simp only [bundle,Finset.mem_filter,Finset.mem_univ,true_and]
  change Function.update A z i x=l ↔ A x=l
  by_cases hx:x=z
  · subst x; simp [hOwner,Ne.symm hli,Ne.symm hlj]
  · rw [Function.update_of_ne hx]

end FairDivision.BF.Applications
