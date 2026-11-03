import FairDivision.BF.Recording.VertexAndEdgeMaps
import FairDivision.BF.Recording.ChildScores
import FairDivision.Topology.SimplexOneSkeletonMap

/-!
# The actual fixed-domain auxiliary family over the recording graph

Choose equivariant maps at recording vertices using p−2 connectivity, retain
those choices, and use the actual p−1-connected edge homotopies between them.
The existing finite closed-face pasting theorem glues the maps on the graph.
All local auxiliary points are embedded by their unchanged real/count
profiles into one fixed finite simplex. The available stock at endpoints is
read from their ACTUAL positive support.

The helper totalizes paths on nonedges only to use the existing generic
one-skeleton paste. No such path is used on the graph, and no local-stock
claim is made for these unused ambient pairs.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical

open scoped unitInterval Topology

namespace FairDivision.BF.Recording

open FairDivision.Topology FairDivision.Topology.NerveConnectivity
open FairDivision.Topology.Volovikov

/-- Real stock at the actual support of a parent graph point. -/
def parentRealStock {p a q m:ℕ} (b:Space (a*p) q m):Finset (Fin m):=
  (finiteSimplexSupport b.1).biUnion real

/-- The largest initial dummy prefix at that SAME support. -/
def parentDummyBudget {p a q m:ℕ} (b:Space (a*p) q m):ℕ:=
  (finiteSimplexSupport b.1).sup dummyCount

@[simp] theorem parentRealStock_vertex {p a q m:ℕ} (b:Vertex (a*p) q m):
    parentRealStock (vertexPoint b)=real b:=by
  simp [parentRealStock,vertexPoint,finiteSimplexSupport_vertex]

@[simp] theorem parentDummyBudget_vertex {p a q m:ℕ} (b:Vertex (a*p) q m):
    parentDummyBudget (vertexPoint b)=dummyCount b:=by
  simp [parentDummyBudget,vertexPoint,finiteSimplexSupport_vertex]

/-- The numerical local stock is exactly the labeled available pool,
including at graph endpoints; no incident-edge extra item is added. -/
theorem available_eq_parentStock {p a q m:ℕ} (b:Space (a*p) q m):
    available b=(parentRealStock b).map (realEmbedding m (a*p))∪
      initialDummies m (a*p) (parentDummyBudget b):=by
  classical
  have hPos:0<(finiteSimplexSupport b.1).card:=
    Finset.card_pos.mpr (finiteSimplexSupport_nonempty b.1)
  have hLe:(finiteSimplexSupport b.1).card≤2:=b.2.2.1
  by_cases hOne:(finiteSimplexSupport b.1).card=1
  ·obtain ⟨u,hSupp⟩:=Finset.card_eq_one.mp hOne
   simp [available,parentRealStock,parentDummyBudget,hSupp,represented]
  ·have hTwo:(finiteSimplexSupport b.1).card=2:=by omega
   obtain ⟨u,w,hu,hSupp⟩:=Finset.card_eq_two.mp hTwo
   rw [available_of_support_pair b u w hSupp,represented_union_decomposition]
   simp [parentRealStock,parentDummyBudget,hSupp,Finset.sup_insert,Finset.sup_singleton]

def graphToOneSkeleton {A q m:ℕ}:C(Space A q m,SmallSupportSimplex (Vertex A q m) 2):=
  ⟨fun b=>⟨b.1,b.2.2.1⟩,
    continuous_subtype_val.subtype_mk (fun b:Space A q m=>b.2.2.1)⟩

/-- The graph inclusion preserves its deterministic vertices literally,
including the proof-independent one-skeleton subtype coordinates. -/
@[simp] theorem graphToOneSkeleton_vertex {A q m:ℕ} (b:Vertex A q m):
    graphToOneSkeleton (vertexPoint b)=FairDivision.Topology.oneSkeletonVertex b:=by
  classical
  apply Subtype.ext
  apply Subtype.ext
  funext c
  by_cases hc:c=b
  · subst c
    simp [graphToOneSkeleton,vertexPoint,FairDivision.Topology.oneSkeletonVertex,stdSimplex.vertex_coe,Pi.single_apply]
  · simp [graphToOneSkeleton,vertexPoint,FairDivision.Topology.oneSkeletonVertex,stdSimplex.vertex_coe,
      Pi.single_apply,hc,Ne.symm hc]

/-- Only an unused ambient nonedge fallback; actual graph edges below use
the proved equivariant homotopy in their exact auxiliary stock. -/
def ambientMapSegment {p a q m:ℕ}
    (f g:C(Q p,stdSimplex ℝ (ChildProfile p a q m))):Path f g:=by
  let H:C(I×Q p,stdSimplex ℝ (ChildProfile p a q m)):=
    ⟨fun z=>variableLotterySegment (f z.2) (g z.2) z.1,
      variableLotterySegment_continuous.comp (continuous_fst.prodMk
        ((f.continuous.comp continuous_snd).prodMk (g.continuous.comp continuous_snd)))⟩
  refine ⟨H.curry,?_,?_⟩
  ·apply ContinuousMap.ext
   intro x
   change variableLotterySegment (f x) (g x) 0=f x
   exact variableLotterySegment_zero (f x) (g x)
  ·apply ContinuousMap.ext
   intro x
   change variableLotterySegment (f x) (g x) 1=g x
   exact variableLotterySegment_one (f x) (g x)

/-- The actual edge homotopy, curried only to reuse the existing closed
one-skeleton pasting with values in a continuous-map space. -/
def edgeAmbientPath {p a q m:ℕ} (hp:2≤p) (ha:0<a) (hq:2≤q)
    (b c:Vertex (a*p) q m) (hbc:adjacent b c):
    Path (vertexAmbientMap hp ha hq b) (vertexAmbientMap hp ha hq c):=by
  let H:C(I×Q p,stdSimplex ℝ (ChildProfile p a q m)):=
    (availableAuxiliaryInclude (real b∪real c)).comp
      ((edgeAuxiliaryHomotopy hp ha hq b c hbc).comp
        (Homeomorph.prodComm I (Q p) : C(I×Q p,Q p×I)))
  refine ⟨H.curry,?_,?_⟩
  ·apply ContinuousMap.ext
   intro x
   change (edgeAuxiliaryHomotopy hp ha hq b c hbc (x,0)).1=vertexAmbientMap hp ha hq b x
   exact (edgeAuxiliaryHomotopy_spec hp ha hq b c hbc).1 x
  ·apply ContinuousMap.ext
   intro x
   change (edgeAuxiliaryHomotopy hp ha hq b c hbc (x,1)).1=vertexAmbientMap hp ha hq c x
   exact (edgeAuxiliaryHomotopy_spec hp ha hq b c hbc).2.1 x

@[simp] theorem edgeAmbientPath_apply {p a q m:ℕ}
    (hp:2≤p) (ha:0<a) (hq:2≤q) (b c:Vertex (a*p) q m)
    (hbc:adjacent b c) (t:I) (x:Q p):
    edgeAmbientPath hp ha hq b c hbc t x=
      (edgeAuxiliaryHomotopy hp ha hq b c hbc (x,t)).1:=rfl

/-- Total path family; ONLY its first branch is used on distinct graph
endpoints. Singleton graph faces use its endpoint value exactly. -/
def recordingGraphPaths {p a q m:ℕ} (hp:2≤p) (ha:0<a) (hq:2≤q)
    (b c:Vertex (a*p) q m):Path (vertexAmbientMap hp ha hq b) (vertexAmbientMap hp ha hq c):=
  if hbc:adjacent b c then edgeAmbientPath hp ha hq b c hbc
  else ambientMapSegment (vertexAmbientMap hp ha hq b) (vertexAmbientMap hp ha hq c)

theorem recordingGraphPaths_of_adjacent {p a q m:ℕ}
    (hp:2≤p) (ha:0<a) (hq:2≤q) (b c:Vertex (a*p) q m)
    (hbc:adjacent b c) (t:I) (x:Q p):
    recordingGraphPaths hp ha hq b c t x=
      (edgeAuxiliaryHomotopy hp ha hq b c hbc (x,t)).1:=by
  simp only [recordingGraphPaths,dif_pos hbc,edgeAmbientPath_apply]

/-- The genuine fixed-domain family with its exact local-stock condition. -/
structure AuxiliaryGraphFamily (p a q m:ℕ) (hp:2≤p) (ha:0<a) (hq:2≤q) where
  map:C(Q p×Space (a*p) q m,stdSimplex ℝ (ChildProfile p a q m))
  within:∀x b,finiteSimplexSupport (map (x,b))∈
    availableAuxiliaryComplex p a q m (parentRealStock b) (parentDummyBudget b)
  equivariant:∀g x b,map (qAction g x,b)=relabelChildLottery g.toMul (map (x,b))
  vertex:∀x b,map (x,vertexPoint b)=vertexAmbientMap hp ha hq b x

/-- All vertex maps, all actual edge homotopies, and finite closed pasting
are constructed here. No family-map or local-pool oracle remains. -/
theorem exists_auxiliaryGraphFamily {p a q m:ℕ}
    (hp:2≤p) (ha:0<a) (hq:2≤q):
    Nonempty (AuxiliaryGraphFamily p a q m hp ha hq):=by
  classical
  letI : DecidableEq (Vertex (a*p) q m):=Classical.decEq (Vertex (a*p) q m)
  letI : CompactSpace (Q p):=isCompact_iff_compactSpace.mp
    (simplicialRealization_isCompact (universalJoinComplex p (ChildGroup p)))
  obtain ⟨score,hVertices,hFaces⟩:=exists_simplexOneSkeletonMap_with_vertices
    (vertexAmbientMap (m:=m) hp ha hq) (recordingGraphPaths hp ha hq)
  let F:C(Q p×Space (a*p) q m,stdSimplex ℝ (ChildProfile p a q m)):=
    (score.comp graphToOneSkeleton).uncurry.comp
      (Homeomorph.prodComm (Q p) (Space (a*p) q m) :
        C(Q p×Space (a*p) q m,Space (a*p) q m×Q p))
  have hVertex:∀x b,F (x,vertexPoint b)=vertexAmbientMap hp ha hq b x:=by
    intro x b
    change score (graphToOneSkeleton (vertexPoint b)) x=vertexAmbientMap hp ha hq b x
    rw [graphToOneSkeleton_vertex,hVertices]
  have hAt:∀(x:Q p)(b:Space (a*p) q m),
      let S:SimplexSmallFace (Vertex (a*p) q m):=
        ⟨finiteSimplexSupport b.1,finiteSimplexSupport_nonempty b.1,b.2.2.1⟩
      let ends:=smallFaceEndpoints S
      F (x,b)=recordingGraphPaths hp ha hq ends.first ends.second
        ⟨b.1.1 ends.second,mem_Icc_of_mem_stdSimplex b.1.2 _⟩ x:=by
    intro x b
    let S:SimplexSmallFace (Vertex (a*p) q m):=
      ⟨finiteSimplexSupport b.1,finiteSimplexSupport_nonempty b.1,b.2.2.1⟩
    have hFace:(graphToOneSkeleton b).1∈simplexSupportFace S.1:=
      Finset.Subset.refl (finiteSimplexSupport b.1)
    have hPasted:=hFaces S (graphToOneSkeleton b) hFace
    exact congrArg (fun f:C(Q p,stdSimplex ℝ (ChildProfile p a q m))=>f x) hPasted
  have hPoint:∀(b:Space (a*p) q m)(u:Vertex (a*p) q m),
      finiteSimplexSupport b.1={u}→b=vertexPoint u:=by
    intro b u hSupp
    have hSimplex : b.1=stdSimplex.vertex u :=
      simplex_eq_vertex_of_support_singleton b.1 u hSupp
    apply Subtype.ext
    apply Subtype.ext
    funext w
    have hw:=congrFun (congrArg Subtype.val hSimplex) w
    by_cases hwu:w=u
    · subst w
      simpa [vertexPoint,stdSimplex.vertex_coe,Pi.single_apply] using hw
    · simpa [vertexPoint,stdSimplex.vertex_coe,Pi.single_apply,hwu,Ne.symm hwu] using hw
  refine ⟨⟨F,?_,?_,hVertex⟩⟩
  ·intro x b
   let S:SimplexSmallFace (Vertex (a*p) q m):=
     ⟨finiteSimplexSupport b.1,finiteSimplexSupport_nonempty b.1,b.2.2.1⟩
   let ends:=smallFaceEndpoints S
   have hPair:finiteSimplexSupport b.1={ends.first,ends.second}:=ends.face_eq
   by_cases he:ends.first=ends.second
   ·have hSupp:finiteSimplexSupport b.1={ends.second}:=by simpa [he] using hPair
    have hb:=hPoint b ends.second hSupp
    rw [hb,hVertex,parentRealStock_vertex,parentDummyBudget_vertex]
    exact (vertexAuxiliaryMap hp ha hq ends.second x).2
   ·have hFirst:ends.first∈finiteSimplexSupport b.1:=by
      rw [hPair]
      exact Finset.mem_insert_self _ _
    have hSecond:ends.second∈finiteSimplexSupport b.1:=by simp [hPair]
    have hAdj:adjacent ends.first ends.second:=b.2.2.2 _ hFirst _ hSecond he
    have hE:parentRealStock b=real ends.first∪real ends.second:=by simp [parentRealStock,hPair]
    have hD:parentDummyBudget b=max (dummyCount ends.first) (dummyCount ends.second):=by
      simp [parentDummyBudget,hPair,Finset.sup_insert,Finset.sup_singleton]
    rw [hAt x b,recordingGraphPaths_of_adjacent hp ha hq _ _ hAdj,hE,hD]
    exact (edgeAuxiliaryHomotopy hp ha hq _ _ hAdj
      (x,⟨b.1.1 ends.second,mem_Icc_of_mem_stdSimplex b.1.2 _⟩)).2
  ·intro g x b
   let S:SimplexSmallFace (Vertex (a*p) q m):=
     ⟨finiteSimplexSupport b.1,finiteSimplexSupport_nonempty b.1,b.2.2.1⟩
   let ends:=smallFaceEndpoints S
   have hPair:finiteSimplexSupport b.1={ends.first,ends.second}:=ends.face_eq
   by_cases he:ends.first=ends.second
   ·have hSupp:finiteSimplexSupport b.1={ends.second}:=by simpa [he] using hPair
    have hb:=hPoint b ends.second hSupp
    rw [hb,hVertex,hVertex]
    exact congrArg Subtype.val (vertexAuxiliaryMap_equivariant hp ha hq ends.second g x)
   ·have hFirst:ends.first∈finiteSimplexSupport b.1:=by simp [hPair]
    have hSecond:ends.second∈finiteSimplexSupport b.1:=by simp [hPair]
    have hAdj:adjacent ends.first ends.second:=b.2.2.2 _ hFirst _ hSecond he
    rw [hAt (qAction g x) b,hAt x b,
      recordingGraphPaths_of_adjacent hp ha hq _ _ hAdj,
      recordingGraphPaths_of_adjacent hp ha hq _ _ hAdj]
    exact congrArg Subtype.val ((edgeAuxiliaryHomotopy_spec hp ha hq _ _ hAdj).2.2 g x
      ⟨b.1.1 ends.second,mem_Icc_of_mem_stdSimplex b.1.2 _⟩)

/-- One actual global family, chosen from the fully proved construction. -/
def auxiliaryGraphFamily {p a q m:ℕ} (hp:2≤p) (ha:0<a) (hq:2≤q):
    AuxiliaryGraphFamily p a q m hp ha hq:=
  Classical.choice (exists_auxiliaryGraphFamily hp ha hq)

/-- The actual T of the manuscript prime-multiplication proof. Its auxiliary
family is constructed, rather than left as a premise. -/
def actualChildT {p a q m:ℕ} (hp:2≤p) (ha:0<a) (hq:2≤q)
    {v:Finset (Fin m)→ℝ}{L H:ℝ}{hLH:L≤H}
    (Φ:RecordingFunction a q m v L H hLH):
    C((Q p×Space (a*p) q m)×Set.Icc L H,Fin p→ℝ):=
  childT Φ (auxiliaryGraphFamily hp ha hq).map

theorem actualChildT_lower {p a q m:ℕ} (hp:2≤p) (ha:0<a) (hq:2≤q)
    {v:Finset (Fin m)→ℝ}{L H:ℝ}{hLH:L≤H}
    (Φ:RecordingFunction a q m v L H hLH) (x:Q p) (b:Space (a*p) q m) (i:Fin p):
    actualChildT hp ha hq Φ ((x,b),lowerTarget hLH) i<0:=
  childT_lower Φ (auxiliaryGraphFamily hp ha hq).map (x,b) i

theorem actualChildT_upper {p a q m:ℕ} (hp:2≤p) (ha:0<a) (hq:2≤q)
    {v:Finset (Fin m)→ℝ}{L H:ℝ}{hLH:L≤H}
    (Φ:RecordingFunction a q m v L H hLH) (x:Q p) (b:Space (a*p) q m) (i:Fin p):
    0<actualChildT hp ha hq Φ ((x,b),upperTarget hLH) i:=
  childT_upper Φ (auxiliaryGraphFamily hp ha hq).map (x,b) i

theorem actualChildT_equivariant {p a q m:ℕ} (hp:2≤p) (ha:0<a) (hq:2≤q)
    {v:Finset (Fin m)→ℝ}{L H:ℝ}{hLH:L≤H}
    (Φ:RecordingFunction a q m v L H hLH) (g:ChildGroup p)
    (x:Q p) (b:Space (a*p) q m) (t:Set.Icc L H) (i:Fin p):
    actualChildT hp ha hq Φ ((qAction g x,b),t) (g.toMul i)=
      actualChildT hp ha hq Φ ((x,b),t) i:=by
  change childScores Φ ((auxiliaryGraphFamily hp ha hq).map (qAction g x,b),t) (g.toMul i)=_
  rw [(auxiliaryGraphFamily hp ha hq).equivariant]
  exact childScores_equivariant Φ g.toMul _ t i

end FairDivision.BF.Recording
