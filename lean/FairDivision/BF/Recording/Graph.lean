import FairDivision.Topology.FiniteSimplexSkeleton
import FairDivision.Topology.NerveConnectivity.FiniteLocallyPathConnected
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fintype.Fin

/-!
# The manuscript's graph of incomplete available item sets

A vertex remembers a real set and a dummy COUNT. Labels are introduced only
in its fixed representative, where the first d of a formal dummy labels are
used. The realization has only vertices and edges; its lottery coordinates
are the actual interpolation weights. Consequently the available pool is
the union over POSITIVE support, so an endpoint does not inherit the extra
item from an incident edge.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.Recording

open FairDivision.Topology
open FairDivision.Topology.NerveConnectivity

/-- Exactly `(A,d)` with d≤a and |A|+d=aq−1. -/
abbrev Vertex (a q m:ℕ) :=
  {b:Finset (Fin m)×Fin (a+1) // b.1.card+b.2.val=a*q-1}

abbrev real {a q m:ℕ} (b:Vertex a q m):Finset (Fin m):=b.1.1
abbrev dummyCount {a q m:ℕ} (b:Vertex a q m):ℕ:=b.1.2.val

theorem dummyCount_le {a q m:ℕ} (b:Vertex a q m):dummyCount b≤a:=by
  exact Nat.le_of_lt_succ b.1.2.isLt

theorem vertex_card {a q m:ℕ} (b:Vertex a q m):
    (real b).card+dummyCount b=a*q-1:=b.2

/-- An oriented real-for-real exchange; its reverse is also an edge. -/
def RealExchange {a q m:ℕ} (b c:Vertex a q m):Prop:=
  dummyCount b=dummyCount c ∧
  ∃x∈real b,∃y, y∉real b ∧real c=insert y ((real b).erase x)

/-- An oriented real-for-dummy exchange. The representative inserts the
next dummy label, which keeps all dummy prefixes nested. -/
def DummyExchange {a q m:ℕ} (b c:Vertex a q m):Prop:=
  dummyCount c=dummyCount b+1 ∧∃x∈real b,real c=(real b).erase x

/-- Literal undirected one-exchange adjacency of Section 4. -/
def adjacent {a q m:ℕ} (b c:Vertex a q m):Prop:=
  b≠c ∧(RealExchange b c ∨RealExchange c b ∨DummyExchange b c ∨DummyExchange c b)

theorem adjacent_symm {a q m:ℕ}{b c:Vertex a q m} (h:adjacent b c):adjacent c b:=by
  refine ⟨h.1.symm,?_⟩
  rcases h.2 with h|h|h|h
  ·exact Or.inr (Or.inl h)
  ·exact Or.inl h
  ·exact Or.inr (Or.inr (Or.inr h))
  ·exact Or.inr (Or.inr (Or.inl h))

/-- The finite simple graph before its ordinary edge realization. -/
def graph (a q m:ℕ):SimpleGraph (Vertex a q m) where
  Adj:=adjacent
  symm:=⟨fun _ _ h=>adjacent_symm h⟩
  loopless:=⟨fun b h=>h.1 rfl⟩

/-- Only one- and two-vertex graph faces, even when three vertices happen
to be pairwise adjacent. Thus this is the graph, not its clique complex. -/
def graphComplex (a q m:ℕ):PreAbstractSimplicialComplex (Vertex a q m) where
  faces:={S|S.Nonempty ∧S.card≤2 ∧∀b∈S,∀c∈S,b≠c→adjacent b c}
  isRelLowerSet_faces:=by
    intro S hS
    refine ⟨hS.1,?_⟩
    intro T hTS hT
    exact ⟨hT,(Finset.card_le_card hTS).trans hS.2.1,
      fun b hb c hc hbc=>hS.2.2 b (hTS hb) c (hTS hc) hbc⟩

/-- Ordinary finite graph realization, inside its probability simplex. -/
abbrev Space (a q m:ℕ):=simplicialRealization (graphComplex a q m)

/-- The graph has the local path structure used by the manuscript's
signed-distance recorder, with no graph-specific topological premise. -/
instance recordingSpaceLocallyPathConnected (a q m:ℕ):
    LocallyPathConnectedSpace (Space a q m):=
  NerveConnectivity.finiteRealization_locallyPathConnectedSpace (graphComplex a q m)

/-- Embed an original real item in the labeled auxiliary inventory. -/
abbrev realEmbedding (m a:ℕ):Fin m↪Fin (m+a):=Fin.castAddEmb a

/-- Formal labels δ₁,…,δₐ, disjoint from every real item. -/
def dummyLabels (m a:ℕ):Finset (Fin (m+a)):=
  Finset.univ.map (Fin.natAddEmb m)

/-- Exactly the initial d dummy labels. -/
def initialDummies (m a d:ℕ):Finset (Fin (m+a)):=
  (Finset.univ.filter (fun j:Fin a=>j.val<d)).map (Fin.natAddEmb m)

/-- A zero dummy count uses no labels, even if the ambient formal
inventory has unused dummy coordinates. -/
@[simp] theorem initialDummies_zero (m a:ℕ):initialDummies m a 0=∅:=by
  simp [initialDummies]

/-- The full prefix is precisely the formal dummy inventory. -/
@[simp] theorem initialDummies_full (m a:ℕ):initialDummies m a a=dummyLabels m a:=by
  apply congrArg (fun S:Finset (Fin a)=>S.map (Fin.natAddEmb m))
  ext δ
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact iff_of_true δ.isLt trivial

/-- The fixed labeled representative B(A,d) of a recording vertex. -/
def represented {a q m:ℕ} (b:Vertex a q m):Finset (Fin (m+a)):=
  (real b).map (realEmbedding m a) ∪initialDummies m a (dummyCount b)

theorem realEmbedding_ne_dummy {m a:ℕ} (i:Fin m) (j:Fin a):
    realEmbedding m a i≠Fin.natAdd m j:=by
  intro h
  have he:=congrArg Fin.val h
  change i.val=m+j.val at he
  omega

theorem realImage_disjoint_dummies {m a:ℕ} (A:Finset (Fin m)):
    Disjoint (A.map (realEmbedding m a)) (dummyLabels m a):=by
  classical
  apply Finset.disjoint_left.mpr
  intro z hzA hzD
  obtain ⟨i,hi,rfl⟩:=Finset.mem_map.mp hzA
  obtain ⟨j,hj,he⟩:=Finset.mem_map.mp hzD
  exact realEmbedding_ne_dummy i j he.symm

theorem initialDummies_subset (m a d:ℕ):initialDummies m a d⊆dummyLabels m a:=by
  intro z hz
  obtain ⟨j,hj,rfl⟩:=Finset.mem_map.mp hz
  exact Finset.mem_map.mpr ⟨j,Finset.mem_univ _,rfl⟩

theorem initialDummies_mono {m a d e:ℕ} (hde:d≤e):
    initialDummies m a d⊆initialDummies m a e:=by
  intro z hz
  obtain ⟨j,hj,rfl⟩:=Finset.mem_map.mp hz
  refine Finset.mem_map.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
  exact lt_of_lt_of_le (Finset.mem_filter.mp hj).2 hde

@[simp] theorem card_dummyLabels (m a:ℕ):(dummyLabels m a).card=a:=by
  simp [dummyLabels]

theorem card_initialDummies (m a d:ℕ) (hd:d≤a):
    (initialDummies m a d).card=d:=by
  rw [initialDummies,Finset.card_map,Fin.card_filter_val_lt,Nat.min_eq_right hd]

/-- The representative has exactly the manuscript's aq−1 items. -/
theorem card_represented {a q m:ℕ} (b:Vertex a q m):
    (represented b).card=a*q-1:=by
  have hDisj:= (realImage_disjoint_dummies (real b)).mono_right
    (initialDummies_subset m a (dummyCount b))
  rw [represented,Finset.card_union_of_disjoint hDisj,Finset.card_map,
    card_initialDummies m a (dummyCount b) (dummyCount_le b)]
  exact vertex_card b

@[simp] theorem represented_inter_dummy {a q m:ℕ} (b:Vertex a q m):
    represented b∩dummyLabels m a=initialDummies m a (dummyCount b):=by
  classical
  ext z
  constructor
  ·intro hz
   obtain ⟨hzB,hzD⟩:=Finset.mem_inter.mp hz
   rcases Finset.mem_union.mp hzB with hReal|hDummy
   ·exact False.elim ((Finset.disjoint_left.mp (realImage_disjoint_dummies (real b))) hReal hzD)
   ·exact hDummy
  ·intro hz
   exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hz,
     initialDummies_subset m a (dummyCount b) hz⟩

/-- Pull a labeled augmented bundle back to its actual original real set. -/
def realPart {m a:ℕ} (E:Finset (Fin (m+a))):Finset (Fin m):=
  Finset.univ.filter (fun g=>realEmbedding m a g∈E)

@[simp] theorem realPart_represented {a q m:ℕ} (b:Vertex a q m):
    realPart (represented b)=real b:=by
  classical
  ext g
  simp only [realPart,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  ·intro hg
   rcases Finset.mem_union.mp hg with hg|hg
   ·obtain ⟨h,hh,he⟩:=Finset.mem_map.mp hg
    exact (realEmbedding m a).injective he ▸hh
   ·exact False.elim ((Finset.disjoint_left.mp (realImage_disjoint_dummies {g}))
       (by simp) (initialDummies_subset m a (dummyCount b) hg))
  ·intro hg
   exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨g,hg,rfl⟩)

/-- Pool at the ACTUAL positive support: an edge endpoint has only its
vertex pool, while an edge interior has the union of its endpoint pools. -/
def available {a q m:ℕ} (x:Space a q m):Finset (Fin (m+a)):=
  (finiteSimplexSupport x.1).biUnion represented

theorem represented_subset_available {a q m:ℕ} (x:Space a q m)
    {b:Vertex a q m} (hb:b∈finiteSimplexSupport x.1):represented b⊆available x:=by
  intro z hz
  exact Finset.mem_biUnion.mpr ⟨b,hb,hz⟩

/-- Canonical deterministic recording-graph point. -/
def vertexPoint {a q m:ℕ} (b:Vertex a q m):Space a q m:=
  ⟨stdSimplex.vertex b,by
    change finiteSimplexSupport (stdSimplex.vertex b) ∈ graphComplex a q m
    rw [finiteSimplexSupport_vertex]
    exact ⟨Finset.singleton_nonempty _,by simp,by simp⟩⟩

@[simp] theorem available_vertexPoint {a q m:ℕ} (b:Vertex a q m):
    available (vertexPoint b)=represented b:=by
  simp [available,vertexPoint,finiteSimplexSupport_vertex]

/-- Literal description on a nondegenerate edge interior; the positivity
hypothesis is precisely that both endpoint lottery weights are nonzero. -/
theorem available_of_support_pair {a q m:ℕ} (x:Space a q m)
    (b c:Vertex a q m) (hSupport:finiteSimplexSupport x.1={b,c}):
    available x=represented b∪represented c:=by
  simp [available,hSupport]

/-- Every graph point uses no more than the a formal dummy labels. -/
theorem available_dummy_bound {a q m:ℕ} (x:Space a q m):
    (available x∩dummyLabels m a).card≤a:=by
  calc
    (available x∩dummyLabels m a).card≤(dummyLabels m a).card:=
      Finset.card_le_card Finset.inter_subset_right
    _=a:=card_dummyLabels m a

end FairDivision.BF.Recording
