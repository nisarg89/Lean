import FairDivision.Definitions
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# The literal induced-edge and deletion arithmetic for density partitions

Reuse Mathlib's incident-edge deletion formula and handshaking lemma.
`internalGraph` merely keeps isolated vertices outside S, so its edge count
is exactly that of the ordinary induced graph on S. This common ambient
vertex type makes the manuscript's real-vertex transfers literal set edits.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.Applications

open scoped BigOperators Classical

variable {V:Type*} [Fintype V]

/-- Induced graph on S, with all other ambient vertices isolated. -/
def internalGraph (G:SimpleGraph V) (S:Finset V):SimpleGraph V where
  Adj x y:=x∈S ∧y∈S ∧G.Adj x y
  symm:=⟨by intro x y h;exact ⟨h.2.1,h.1,h.2.2.symm⟩⟩
  loopless:=⟨by intro x h;exact G.irrefl h.2.2⟩

/-- Actual number of edges of the induced subgraph. -/
def inducedEdges (G:SimpleGraph V) (S:Finset V):ℕ:=
  (internalGraph G S).edgeFinset.card

/-- Degree inside the induced subgraph, on the ambient real labels. -/
def inducedDegree (G:SimpleGraph V) (S:Finset V) (x:V):ℕ:=
  (internalGraph G S).degree x

/-- Density, with the harmless total convention density(empty)=0. All
parts used by the density theorem itself are nonempty. -/
def graphDensity (G:SimpleGraph V) (S:Finset V):ℝ:=
  (inducedEdges G S:ℝ)/S.card

/-- The exact modified density in the manuscript. -/
def modifiedDensity (G:SimpleGraph V) (S:Finset V):ℝ:=
  (inducedEdges G S:ℝ)/((S.card:ℝ)+1)

theorem internalGraph_induce (G:SimpleGraph V) (S:Finset V):
    (internalGraph G S).induce (S:Set V)=G.induce (S:Set V):=by
  ext x y
  simp [SimpleGraph.induce_adj,internalGraph,x.property,y.property]

/-- The representation does not change the reader-facing edge count. -/
theorem inducedEdges_eq_induce (G:SimpleGraph V) (S:Finset V):
    inducedEdges G S=(G.induce (S:Set V)).edgeFinset.card:=by
  have hs:(internalGraph G S).support⊆(S:Set V):=by
    intro x hx
    obtain ⟨y,hxy⟩:=(internalGraph G S).mem_support.mp hx
    exact hxy.1
  have h:=(internalGraph G S).card_edgeFinset_induce_of_support_subset hs
  -- Normalize the finite enumerations before changing the induced graph.
  -- The support lemma and this statement synthesize different subtype Fintypes.
  simp only [SimpleGraph.edgeFinset,← Set.ncard_eq_toFinset_card'] at h
  rw [internalGraph_induce] at h
  simpa only [inducedEdges,SimpleGraph.edgeFinset,← Set.ncard_eq_toFinset_card'] using h.symm

theorem internalGraph_erase (G:SimpleGraph V) (S:Finset V) (x:V):
    internalGraph G (S.erase x)=(internalGraph G S).deleteIncidenceSet x:=by
  ext u v
  simp only [internalGraph,SimpleGraph.deleteIncidenceSet_adj,Finset.mem_erase]
  tauto

/-- Deleting x removes exactly its induced degree. -/
theorem inducedEdges_erase (G:SimpleGraph V) (S:Finset V) (x:V):
    inducedEdges G (S.erase x)=inducedEdges G S-inducedDegree G S x:=by
  unfold inducedEdges inducedDegree
  let e : internalGraph G (S.erase x) ≃g (internalGraph G S).deleteIncidenceSet x :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := by
        intro u v
        simp only [Equiv.refl_apply,internalGraph,
          SimpleGraph.deleteIncidenceSet_adj,Finset.mem_erase]
        tauto }
  exact e.card_edgeFinset_eq.trans
    (SimpleGraph.card_edgeFinset_deleteIncidenceSet (internalGraph G S) x)

theorem inducedDegree_le_edges (G:SimpleGraph V) (S:Finset V) (x:V):
    inducedDegree G S x≤ inducedEdges G S:=
  (internalGraph G S).degree_le_card_edgeFinset x

/-- At most all OTHER members of S can be neighbors of a vertex in S. -/
theorem inducedDegree_le_card_sub_one (G:SimpleGraph V) (S:Finset V)
    (x:V) (hx:x∈S):inducedDegree G S x≤S.card-1:=by
  have hs:(internalGraph G S).neighborFinset x⊆S.erase x:=by
    intro y hy
    have hxy:=(SimpleGraph.mem_neighborFinset _ _ _).mp hy
    exact Finset.mem_erase.mpr ⟨by intro he;subst y;exact G.irrefl hxy.2.2,hxy.2.1⟩
  calc
    inducedDegree G S x=((internalGraph G S).neighborFinset x).card:=rfl
    _≤(S.erase x).card:=Finset.card_le_card hs
    _=S.card-1:=Finset.card_erase_of_mem hx

/-- The standard simple-graph edge upper bound, from the imported
handshaking lemma and its existing degree bound on the induced graph. -/
theorem two_mul_inducedEdges_le (G:SimpleGraph V) (S:Finset V):
    2*inducedEdges G S≤S.card*(S.card-1):=by
  let H:=G.induce (S:Set V)
  have hc:Fintype.card ↥(S:Set V)=S.card:=by simp
  have hsum:(∑x:↥(S:Set V),H.degree x)≤∑_x:↥(S:Set V),(S.card-1):=by
    apply Finset.sum_le_sum
    intro x hx
    have h:=H.degree_lt_card_verts x
    rw [hc] at h
    omega
  rw [H.sum_degrees_eq_twice_card_edges] at hsum
  simpa only [inducedEdges_eq_induce,H,Finset.sum_const,Finset.card_univ,
    hc,smul_eq_mul] using hsum

theorem graphDensity_nonneg (G:SimpleGraph V) (S:Finset V):0≤graphDensity G S:=by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Every simple graph of order s has density at most (s-1)/2. -/
theorem graphDensity_le (G:SimpleGraph V) (S:Finset V) (hs:0<S.card):
    graphDensity G S≤((S.card:ℝ)-1)/2:=by
  have hEdge:=two_mul_inducedEdges_le G S
  have hsR:0<(S.card:ℝ):=by exact_mod_cast hs
  have hcast:(2:ℝ)*(inducedEdges G S:ℝ)≤(S.card:ℝ)*(S.card-1:ℕ):=by
    exact_mod_cast hEdge
  rw [Nat.cast_sub (by omega :1≤S.card),Nat.cast_one] at hcast
  apply (div_le_iff₀ hsR).mpr
  nlinarith

/-- The manuscript's exact deletion identity. -/
theorem modifiedDensity_erase (G:SimpleGraph V) (S:Finset V) (x:V) (hx:x∈S):
    modifiedDensity G (S.erase x)=
      graphDensity G S-(inducedDegree G S x:ℝ)/S.card:=by
  have hDen:((S.erase x).card:ℝ)+1=(S.card:ℝ):=by
    exact_mod_cast Finset.card_erase_add_one hx
  unfold modifiedDensity graphDensity
  rw [inducedEdges_erase,Nat.cast_sub (inducedDegree_le_edges G S x),hDen,sub_div]

/-- All real deletion values lie in exactly the density window used in
the paper, of width (s-1)/s. -/
theorem modifiedDensity_erase_bounds (G:SimpleGraph V) (S:Finset V)
    (x:V) (hx:x∈S):
    graphDensity G S-((S.card:ℝ)-1)/S.card≤ modifiedDensity G (S.erase x) ∧
      modifiedDensity G (S.erase x)≤graphDensity G S:=by
  rw [modifiedDensity_erase G S x hx]
  have hs:0<S.card:=Finset.card_pos.mpr ⟨x,hx⟩
  have hsR:0<(S.card:ℝ):=by exact_mod_cast hs
  have hd:0≤(inducedDegree G S x:ℝ)/S.card:=div_nonneg (Nat.cast_nonneg _) hsR.le
  have hdegree:(inducedDegree G S x:ℝ)≤(S.card-1:ℕ):=by
    exact_mod_cast inducedDegree_le_card_sub_one G S x hx
  rw [Nat.cast_sub (by omega :1≤S.card),Nat.cast_one] at hdegree
  have hdiv:=div_le_div_of_nonneg_right hdegree hsR.le
  exact ⟨by linarith,by linarith⟩

end FairDivision.BF.Applications
