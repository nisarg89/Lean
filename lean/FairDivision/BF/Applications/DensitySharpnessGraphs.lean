import FairDivision.BF.Applications.DensityPartition
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Data.Nat.Choose.Cast

/-!
# Literal induced densities in the manuscript's sharpness graphs

Reuse Mathlib's actual `starGraph`, tree edge count, and complete-graph edge
count. The other example is exactly the complete graph with one isolated
vertex. These formulas are independent of the partition bookkeeping.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.Applications

open scoped Classical

variable {V : Type*} [Fintype V]

/-- K_(N−1) and one literal isolated vertex. -/
def cliqueWithIsolate (z : V) : SimpleGraph V where
  Adj x y:=x≠y ∧ x≠z ∧ y≠z
  symm:=⟨by intro x y h; exact ⟨Ne.symm h.1,h.2.2,h.2.1⟩⟩
  loopless:=⟨by intro x h; exact h.1 rfl⟩

/-- A star induced on a set containing its center is the SAME star on that
subtype, so the existing tree edge count gives exactly |S|−1 edges. -/
theorem inducedEdges_star_of_mem (z : V) (S : Finset V) (hz : z∈S) :
    inducedEdges (SimpleGraph.starGraph z) S=S.card-1 := by
  rw [inducedEdges_eq_induce]
  have hGraph : (SimpleGraph.starGraph z).induce (S:Set V)=
      SimpleGraph.starGraph (⟨z,hz⟩ : (S:Set V)) := by
    ext x y
    simp only [SimpleGraph.induce_adj,SimpleGraph.starGraph_adj]
    constructor
    · rintro ⟨hxy,hx|hy⟩
      · exact ⟨fun he=>hxy (congrArg Subtype.val he),Or.inl (Subtype.ext hx)⟩
      · exact ⟨fun he=>hxy (congrArg Subtype.val he),Or.inr (Subtype.ext hy)⟩
    · rintro ⟨hxy,hx|hy⟩
      · exact ⟨fun he=>hxy (Subtype.ext he),Or.inl (congrArg Subtype.val hx)⟩
      · exact ⟨fun he=>hxy (Subtype.ext he),Or.inr (congrArg Subtype.val hy)⟩
  -- Remove the graph-dependent finite edge enumeration before rewriting.
  simp only [SimpleGraph.edgeFinset,← Set.ncard_eq_toFinset_card']
  rw [hGraph]
  have hEdges:=(SimpleGraph.isTree_starGraph (⟨z,hz⟩ : (S:Set V))).card_edgeFinset
  simp only [SimpleGraph.edgeFinset,← Set.ncard_eq_toFinset_card'] at hEdges
  have hCard : Fintype.card (S:Set V)=S.card := by simp
  rw [hCard] at hEdges
  omega

/-- All star edges meet its center; a part without that center is edgeless. -/
theorem inducedEdges_star_of_not_mem (z : V) (S : Finset V) (hz : z∉S) :
    inducedEdges (SimpleGraph.starGraph z) S=0 := by
  have hGraph : internalGraph (SimpleGraph.starGraph z) S=⊥ := by
    ext x y
    simp only [internalGraph,SimpleGraph.starGraph_adj,SimpleGraph.bot_adj]
    constructor
    · rintro ⟨hx,hy,hxy,hxz|hyz⟩
      · exact hz (hxz ▸ hx)
      · exact hz (hyz ▸ hy)
    · exact False.elim
  unfold inducedEdges
  simp only [SimpleGraph.edgeFinset,← Set.ncard_eq_toFinset_card']
  rw [hGraph]
  simp

theorem graphDensity_star_of_mem (z : V) (S : Finset V) (hz : z∈S) :
    graphDensity (SimpleGraph.starGraph z) S=densityRadius S.card := by
  have hOne : 1≤S.card:=Finset.card_pos.mpr ⟨z,hz⟩
  unfold graphDensity densityRadius
  rw [inducedEdges_star_of_mem z S hz,Nat.cast_sub hOne,Nat.cast_one]

theorem graphDensity_star_of_not_mem (z : V) (S : Finset V) (hz : z∉S) :
    graphDensity (SimpleGraph.starGraph z) S=0 := by
  simp [graphDensity,inducedEdges_star_of_not_mem z S hz]

/-- This is Mathlib's complete-graph choose-two count on the induced subtype. -/
theorem inducedEdges_complete (S : Finset V) : inducedEdges (⊤ : SimpleGraph V) S=S.card.choose 2 := by
  rw [inducedEdges_eq_induce]
  have hGraph : (⊤ : SimpleGraph V).induce (S:Set V)=⊤ := by
    ext x y
    simp only [SimpleGraph.induce_adj,SimpleGraph.top_adj]
    constructor
    ·intro hNe hEq
     exact hNe (congrArg Subtype.val hEq)
    ·intro hNe hEq
     exact hNe (Subtype.ext hEq)
  simp only [SimpleGraph.edgeFinset,← Set.ncard_eq_toFinset_card']
  rw [hGraph]
  have hEdges:=SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V:=(S:Set V))
  simp only [SimpleGraph.edgeFinset,← Set.ncard_eq_toFinset_card'] at hEdges
  rw [hEdges]
  simp

theorem graphDensity_complete (S : Finset V) (hS : 0<S.card) :
    graphDensity (⊤ : SimpleGraph V) S=((S.card:ℝ)-1)/2 := by
  have hS' : (S.card:ℝ)≠0:=by exact_mod_cast hS.ne'
  unfold graphDensity
  rw [inducedEdges_complete,Nat.cast_choose_two]
  field_simp [hS']

/-- Isolating z is exactly the same as erasing it before counting clique edges. -/
theorem inducedEdges_cliqueWithIsolate (z : V) (S : Finset V) :
    inducedEdges (cliqueWithIsolate z) S=(S.erase z).card.choose 2 := by
  have hGraph : internalGraph (cliqueWithIsolate z) S=
      internalGraph (⊤ : SimpleGraph V) (S.erase z) := by
    ext x y
    simp only [internalGraph,cliqueWithIsolate,Finset.mem_erase,SimpleGraph.top_adj]
    tauto
  unfold inducedEdges
  simp only [SimpleGraph.edgeFinset,← Set.ncard_eq_toFinset_card']
  rw [hGraph]
  simpa only [inducedEdges,SimpleGraph.edgeFinset,← Set.ncard_eq_toFinset_card'] using
    inducedEdges_complete (S.erase z)

theorem graphDensity_cliqueWithIsolate_of_not_mem (z : V) (S : Finset V) (hz : z∉S)
    (hS : 0<S.card) : graphDensity (cliqueWithIsolate z) S=((S.card:ℝ)-1)/2 := by
  unfold graphDensity
  rw [inducedEdges_cliqueWithIsolate,Finset.erase_eq_of_notMem hz,Nat.cast_choose_two]
  have hS' : (S.card:ℝ)≠0:=by exact_mod_cast hS.ne'
  field_simp [hS'] <;> ring

/-- Exact isolate-part density, including the 2-vertex part whose sole
clique vertex is isolated inside that part. -/
theorem graphDensity_cliqueWithIsolate_of_mem (z : V) (S : Finset V) (hz : z∈S)
    (hS : 2≤S.card) :
    graphDensity (cliqueWithIsolate z) S=
      (((S.card:ℝ)-1)*((S.card:ℝ)-2))/(2*S.card) := by
  unfold graphDensity
  rw [inducedEdges_cliqueWithIsolate,Finset.card_erase_of_mem hz,Nat.cast_choose_two]
  have hOne : 1≤S.card := by omega
  simp only [Nat.cast_sub hOne,Nat.cast_one]
  have hS' : (S.card:ℝ)≠0:=by exact_mod_cast (show S.card≠0 by omega)
  field_simp [hS']
  ring

end FairDivision.BF.Applications
