import FairDivision.BF.Recording.AvailableAction
import FairDivision.Topology.Volovikov.UniversalJoinEquivariantTransfer
import FairDivision.Topology.VariableDummySimplicialHomotopy

/-!
# The SAME fixed Qp at vertices and along actual recording edges

Vertex targets use the exact one-item-excluded p−2 bound. For a graph edge,
include both already chosen vertex maps in its common available pool, and
join those ORIGINAL maps by the actual equivariant homotopy at the stronger
p−1 bound. Its range remains in that edge stock throughout.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

open scoped unitInterval Topology

namespace FairDivision.BF.Recording

open FairDivision.Topology FairDivision.Topology.NerveConnectivity
open FairDivision.Topology.Volovikov

/-- Exactly the manuscript's S_p action on the fixed p-fold join. -/
def qAction {p:ℕ} (g:ChildGroup p):Q p≃ₜQ p:=
  translateInvariantRealization (universalJoinComplex p (ChildGroup p)) universalJoinComplex_invariant g

/-- A concrete chosen equivariant vertex map, using the actual stock bound. -/
def vertexAuxiliaryMap {p a q m:ℕ} (hp:2≤p) (ha:0<a) (hq:2≤q)
    (b:Vertex (a*p) q m):
    C(Q p,simplicialRealization
      (availableAuxiliaryComplex p a q m (real b) (dummyCount b))):=
  Classical.choose (exists_equivariant_universalJoinMap (by omega:p≤(p-2)+2)
    (availableVertex_nullConnected hp ha hq b)
    (availableChildAction (real b)) (availableChildAction_laws (real b)))

theorem vertexAuxiliaryMap_equivariant {p a q m:ℕ}
    (hp:2≤p) (ha:0<a) (hq:2≤q) (b:Vertex (a*p) q m):
    IsEquivariantJoinMap (universalJoinComplex p (ChildGroup p)) universalJoinComplex_invariant
      (availableChildAction (real b)) (vertexAuxiliaryMap hp ha hq b):=
  Classical.choose_spec (exists_equivariant_universalJoinMap (by omega:p≤(p-2)+2)
    (availableVertex_nullConnected hp ha hq b)
    (availableChildAction (real b)) (availableChildAction_laws (real b)))

def vertexAmbientMap {p a q m:ℕ} (hp:2≤p) (ha:0<a) (hq:2≤q)
    (b:Vertex (a*p) q m):C(Q p,stdSimplex ℝ (ChildProfile p a q m)):=
  (availableAuxiliaryInclude (real b)).comp (vertexAuxiliaryMap hp ha hq b)

theorem initialDummies_union (m a d e:ℕ):
    initialDummies m a d∪initialDummies m a e=initialDummies m a (max d e):=by
  rcases le_total d e with h|h
  ·rw [max_eq_right h]
   exact Finset.union_eq_right.mpr (initialDummies_mono h)
  ·rw [max_eq_left h]
   exact Finset.union_eq_left.mpr (initialDummies_mono h)

/-- The representatives on each end of an edge have the exact common
real-union/maximum-dummy stock used in the auxiliary homotopy. -/
theorem represented_union_decomposition {A q m:ℕ} (b c:Vertex A q m):
    represented b∪represented c=
      ((real b∪real c).map (realEmbedding m A))∪
        initialDummies m A (max (dummyCount b) (dummyCount c)):=by
  classical
  have hD:=initialDummies_union m A (dummyCount b) (dummyCount c)
  rw [←hD]
  simp only [represented,Finset.map_union]
  ext z
  simp only [Finset.mem_union]
  tauto

theorem edge_stock_card {p a q m:ℕ} (hp:2≤p) (ha:0<a) (hq:2≤q)
    (b c:Vertex (a*p) q m) (hbc:adjacent b c):
    (real b∪real c).card+max (dummyCount b) (dummyCount c)=(a*p)*q:=by
  have hd:max (dummyCount b) (dummyCount c)≤a*p:=max_le (dummyCount_le b) (dummyCount_le c)
  have hDisj:Disjoint ((real b∪real c).map (realEmbedding m (a*p)))
      (initialDummies m (a*p) (max (dummyCount b) (dummyCount c))):=
    (realImage_disjoint_dummies (real b∪real c)).mono_right (initialDummies_subset _ _ _)
  have hCard:=card_represented_union_of_adjacent (Nat.mul_pos ha (by omega)) (by omega) b c hbc
  rw [represented_union_decomposition,Finset.card_union_of_disjoint hDisj,
    Finset.card_map,card_initialDummies _ _ _ hd] at hCard
  exact hCard

/-- The two EXISTING vertex maps included in the edge target. -/
def edgeEndpointMap {p a q m:ℕ} (hp:2≤p) (ha:0<a) (hq:2≤q)
    (b c:Vertex (a*p) q m):
    C(Q p,simplicialRealization
      (availableAuxiliaryComplex p a q m (real b∪real c)
        (max (dummyCount b) (dummyCount c)))):=
  (availableStockInclude Finset.subset_union_left (le_max_left _ _)).comp
    (vertexAuxiliaryMap hp ha hq b)

theorem edgeEndpointMap_equivariant {p a q m:ℕ} (hp:2≤p) (ha:0<a) (hq:2≤q)
    (b c:Vertex (a*p) q m):
    IsEquivariantJoinMap (universalJoinComplex p (ChildGroup p)) universalJoinComplex_invariant
      (availableChildAction (real b∪real c)) (edgeEndpointMap hp ha hq b c):=by
  intro g x
  change availableStockInclude
      (Finset.subset_union_left : real b⊆real b∪real c)
      (le_max_left (dummyCount b) (dummyCount c))
      (vertexAuxiliaryMap hp ha hq b (qAction g x))=_
  have hVertex : vertexAuxiliaryMap hp ha hq b (qAction g x)=
      availableChildAction (real b) g (vertexAuxiliaryMap hp ha hq b x) := by
    simpa only [qAction] using vertexAuxiliaryMap_equivariant hp ha hq b g x
  rw [hVertex]
  exact availableStockInclude_action
    (Finset.subset_union_left : real b⊆real b∪real c)
    (le_max_left (dummyCount b) (dummyCount c)) g _

/-- Continuous equivariant edge family in its exact stock, preserving both
original vertex maps. The only primeness use is later in the zero theorem. -/
theorem exists_edgeAuxiliaryHomotopy {p a q m:ℕ} (hp:2≤p) (ha:0<a) (hq:2≤q)
    (b c:Vertex (a*p) q m) (hbc:adjacent b c):
    ∃H:C(Q p×I,simplicialRealization
      (availableAuxiliaryComplex p a q m (real b∪real c)
        (max (dummyCount b) (dummyCount c)))),
      (∀x,(H (x,0)).1=vertexAmbientMap hp ha hq b x) ∧
      (∀x,(H (x,1)).1=vertexAmbientMap hp ha hq c x) ∧
      ∀g x t,H (qAction g x,t)=availableChildAction (real b∪real c) g (H (x,t)):=by
  let E:=real b∪real c
  let d:=max (dummyCount b) (dummyCount c)
  let f0:=edgeEndpointMap hp ha hq b c
  let f1:C(Q p,simplicialRealization (availableAuxiliaryComplex p a q m E d)):=
    (availableStockInclude Finset.subset_union_right (le_max_right _ _)).comp
      (vertexAuxiliaryMap hp ha hq c)
  have hf1:IsEquivariantJoinMap (universalJoinComplex p (ChildGroup p))
      universalJoinComplex_invariant (availableChildAction E) f1:=by
    intro g x
    change availableStockInclude
        (Finset.subset_union_right : real c⊆real b∪real c)
        (le_max_right (dummyCount b) (dummyCount c))
        (vertexAuxiliaryMap hp ha hq c (qAction g x))=_
    have hVertex : vertexAuxiliaryMap hp ha hq c (qAction g x)=
        availableChildAction (real c) g (vertexAuxiliaryMap hp ha hq c x) := by
      simpa only [qAction] using vertexAuxiliaryMap_equivariant hp ha hq c g x
    rw [hVertex]
    exact availableStockInclude_action
      (Finset.subset_union_right : real c⊆real b∪real c)
      (le_max_right (dummyCount b) (dummyCount c)) g _
  have hConnected:=availableEdge_nullConnected hp ha hq E d
    (edge_stock_card hp ha hq b c hbc) (max_le (dummyCount_le b) (dummyCount_le c))
  obtain ⟨H,h0,h1,hEquiv⟩:=exists_equivariant_universalJoinHomotopy
    (by omega:p≤(p-1)+1) hConnected (availableChildAction E)
    (availableChildAction_laws E) f0 f1 (edgeEndpointMap_equivariant hp ha hq b c) hf1
  refine ⟨H,?_,?_,hEquiv⟩
  ·intro x
   exact congrArg Subtype.val (h0 x)
  ·intro x
   exact congrArg Subtype.val (h1 x)

/-- The actual chosen homotopy, NOT an assumed runner. -/
def edgeAuxiliaryHomotopy {p a q m:ℕ} (hp:2≤p) (ha:0<a) (hq:2≤q)
    (b c:Vertex (a*p) q m) (hbc:adjacent b c):
    C(Q p×I,simplicialRealization
      (availableAuxiliaryComplex p a q m (real b∪real c)
        (max (dummyCount b) (dummyCount c)))):=
  Classical.choose (exists_edgeAuxiliaryHomotopy hp ha hq b c hbc)

theorem edgeAuxiliaryHomotopy_spec {p a q m:ℕ} (hp:2≤p) (ha:0<a) (hq:2≤q)
    (b c:Vertex (a*p) q m) (hbc:adjacent b c):
    (∀x,(edgeAuxiliaryHomotopy hp ha hq b c hbc (x,0)).1=vertexAmbientMap hp ha hq b x) ∧
    (∀x,(edgeAuxiliaryHomotopy hp ha hq b c hbc (x,1)).1=vertexAmbientMap hp ha hq c x) ∧
    ∀g x t,edgeAuxiliaryHomotopy hp ha hq b c hbc (qAction g x,t)=
      availableChildAction (real b∪real c) g (edgeAuxiliaryHomotopy hp ha hq b c hbc (x,t)):=
  Classical.choose_spec (exists_edgeAuxiliaryHomotopy hp ha hq b c hbc)

end FairDivision.BF.Recording
