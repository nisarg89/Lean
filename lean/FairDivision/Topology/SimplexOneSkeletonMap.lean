import FairDivision.Topology.FiniteSimplexSkeleton
import FairDivision.Topology.FiniteClosedCoverMaps
import Mathlib.Topology.Path

/-!
# Paste prescribed paths on the actual one-skeleton of a finite simplex

A face with one or two vertices is parameterized by the weight of a fixed
second endpoint. The endpoints are selected once per face. Shared vertices
are the only nonempty overlaps of distinct such faces, so endpoint agreement
and the existing finite closed-cover pasting theorem give a continuous map.
No triangulation or replacement of the lottery domain is used.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology

open scoped Classical
open Set

/-- A nonempty face of the one-skeleton, including its vertices. -/
abbrev SimplexSmallFace (V : Type*) :=
  {S : Finset V // S.Nonempty ∧ S.card ≤ 2}

/-- The ordinary closed face of the probability simplex, expressed by support. -/
def simplexSupportFace {V : Type*} [Fintype V] (S : Finset V) :
    Set (stdSimplex ℝ V) :=
  {x | finiteSimplexSupport x ⊆ S}

/-- Outside the positive support a nonnegative coordinate is zero. -/
theorem simplex_coordinate_eq_zero_of_not_support
    {V : Type*} [Fintype V] (x : stdSimplex ℝ V) {v : V}
    (hv : v ∉ finiteSimplexSupport x) : x.1 v = 0 := by
  have hn : ¬0 < x.1 v := fun h => hv ((mem_finiteSimplexSupport_iff x v).2 h)
  exact le_antisymm (le_of_not_gt hn) (x.2.1 v)

/-- A support face is cut out by literal zero-coordinate equalities. -/
theorem simplexSupportFace_iff {V : Type*} [Fintype V]
    (S : Finset V) (x : stdSimplex ℝ V) :
    x ∈ simplexSupportFace S ↔ ∀ v, v ∉ S → x.1 v = 0 := by
  constructor
  · intro hx v hv
    exact simplex_coordinate_eq_zero_of_not_support x (fun h => hv (hx h))
  · intro hx v hv
    by_contra hnot
    have hpos := (mem_finiteSimplexSupport_iff x v).1 hv
    rw [hx v hnot] at hpos
    exact (lt_irrefl _) hpos

theorem simplexSupportFace_closed {V : Type*} [Fintype V]
    (S : Finset V) : IsClosed (simplexSupportFace S) := by
  have he : simplexSupportFace S =
      ⋂ v : V, ⋂ (_h : v ∉ S), {x : stdSimplex ℝ V | x.1 v = 0} := by
    ext x
    simp only [mem_iInter]
    exact simplexSupportFace_iff S x
  rw [he]
  apply isClosed_iInter
  intro v
  apply isClosed_iInter
  intro _
  exact isClosed_eq ((continuous_apply v).comp continuous_subtype_val) continuous_const

/-- A probability vector supported on one vertex is that deterministic lottery. -/
theorem simplex_eq_vertex_of_support_singleton
    {V : Type*} [Fintype V] [DecidableEq V]
    (x : stdSimplex ℝ V) (v : V) (hx : finiteSimplexSupport x = {v}) :
    x = stdSimplex.vertex v := by
  have hz : ∀ w, w ≠ v → x.1 w = 0 := by
    intro w hw
    apply simplex_coordinate_eq_zero_of_not_support x
    simpa [hx] using hw
  have hs : (∑ w : V, x.1 w) = x.1 v := by
    apply Finset.sum_eq_single v
    · intro w _ hw
      exact hz w hw
    · intro h
      exact False.elim (h (Finset.mem_univ v))
  have hv : x.1 v = 1 := hs.symm.trans x.2.2
  apply Subtype.ext
  funext w
  by_cases hw : w = v
  · subst w
    simp [stdSimplex.vertex_coe, hv]
  · simp [stdSimplex.vertex_coe, hz w hw, hw, Ne.symm hw]

/-- Distinct one-dimensional closed faces can only overlap at a vertex. -/
theorem simplexSmallFace_overlap_vertex
    {V : Type*} [Fintype V] [DecidableEq V]
    (S T : SimplexSmallFace V) (hne : S ≠ T)
    (x : stdSimplex ℝ V)
    (hS : x ∈ simplexSupportFace S.1) (hT : x ∈ simplexSupportFace T.1) :
    ∃ v, x = stdSimplex.vertex v ∧ v ∈ S.1 ∧ v ∈ T.1 := by
  classical
  have hc : (finiteSimplexSupport x).card ≤ 1 := by
    by_contra hlarge
    have htwo : 2 ≤ (finiteSimplexSupport x).card := by omega
    have heS : finiteSimplexSupport x = S.1 :=
      Finset.eq_of_subset_of_card_le hS (S.2.2.trans htwo)
    have heT : finiteSimplexSupport x = T.1 :=
      Finset.eq_of_subset_of_card_le hT (T.2.2.trans htwo)
    exact hne (Subtype.ext (heS.symm.trans heT))
  have hpos := Finset.card_pos.mpr (finiteSimplexSupport_nonempty x)
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (show (finiteSimplexSupport x).card = 1 by omega)
  have hvmem : v ∈ finiteSimplexSupport x := by simp [hv]
  exact ⟨v, simplex_eq_vertex_of_support_singleton x v hv, hS hvmem, hT hvmem⟩

/-- A fixed ordered pair spanning a small face. A one-vertex face repeats its
endpoint; no artificial extra simplex vertex is introduced. -/
structure SmallFaceEndpoints {V : Type*} (S : SimplexSmallFace V) where
  first : V
  second : V
  face_eq : S.1 = {first, second}

theorem exists_smallFaceEndpoints {V : Type*} (S : SimplexSmallFace V) :
    Nonempty (SmallFaceEndpoints S) := by
  classical
  have hpos := Finset.card_pos.mpr S.2.1
  by_cases hone : S.1.card = 1
  · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hone
    exact ⟨⟨v, v, by simpa using hv⟩⟩
  · have htwo : S.1.card = 2 := by omega
    obtain ⟨a, b, _, hab⟩ := Finset.card_eq_two.mp htwo
    exact ⟨⟨a, b, hab⟩⟩

def smallFaceEndpoints {V : Type*} (S : SimplexSmallFace V) : SmallFaceEndpoints S :=
  Classical.choice (exists_smallFaceEndpoints S)

/-- Run the fixed endpoint path at the actual lottery weight of its second
endpoint. This is one continuous vector map for all agents. -/
def simplexSmallFaceMap
    {V Y : Type*} [Fintype V] [TopologicalSpace Y]
    (value : V → Y) (edge : ∀ a b, Path (value a) (value b))
    (S : SimplexSmallFace V) : C(simplexSupportFace S.1, Y) := {
  toFun := fun x =>
    edge (smallFaceEndpoints S).first (smallFaceEndpoints S).second
      ⟨x.1.1 (smallFaceEndpoints S).second,
        mem_Icc_of_mem_stdSimplex x.1.2 _⟩
  continuous_toFun := by
    apply (edge _ _).continuous.comp
    exact (((continuous_apply _).comp continuous_subtype_val).comp
      continuous_subtype_val).subtype_mk _ }

/-- Every edge map agrees with the prescribed vertex map, including a
one-vertex face. Thus no compatibility assumption is needed from the caller. -/
theorem simplexSmallFaceMap_vertex
    {V Y : Type*} [Fintype V] [DecidableEq V] [TopologicalSpace Y]
    (value : V → Y) (edge : ∀ a b, Path (value a) (value b))
    (S : SimplexSmallFace V) (v : V) (hv : v ∈ S.1)
    (hface : stdSimplex.vertex v ∈ simplexSupportFace S.1) :
    simplexSmallFaceMap value edge S ⟨stdSimplex.vertex v, hface⟩ = value v := by
  have hpair : v = (smallFaceEndpoints S).first ∨ v = (smallFaceEndpoints S).second := by
    simpa [(smallFaceEndpoints S).face_eq] using hv
  by_cases hsecond : v = (smallFaceEndpoints S).second
  · subst v
    change edge _ _ _ = _
    have ht : (⟨(stdSimplex.vertex (smallFaceEndpoints S).second).1
        (smallFaceEndpoints S).second,
        mem_Icc_of_mem_stdSimplex (stdSimplex.vertex (smallFaceEndpoints S).second).2 _⟩ :
        unitInterval) = 1 := by
      apply Subtype.ext
      simp [stdSimplex.vertex_coe]
    rw [ht, Path.target]
  · have hfirst : v = (smallFaceEndpoints S).first := hpair.resolve_right hsecond
    change edge _ _ _ = _
    have ht : (⟨(stdSimplex.vertex v).1 (smallFaceEndpoints S).second,
        mem_Icc_of_mem_stdSimplex (stdSimplex.vertex v).2 _⟩ : unitInterval) = 0 := by
      apply Subtype.ext
      simp [stdSimplex.vertex_coe, hsecond, Ne.symm hsecond]
    rw [ht, Path.source, ← hfirst]

/-- Prescribed paths, one fixed ordered path per small face, paste to a
continuous function on the literal lottery one-skeleton. -/
theorem exists_simplexOneSkeletonMap
    {V Y : Type*} [Fintype V] [TopologicalSpace Y]
    (value : V → Y) (edge : ∀ a b, Path (value a) (value b)) :
    ∃ score : C(SmallSupportSimplex V 2, Y),
      ∀ (S : SimplexSmallFace V) (x : SmallSupportSimplex V 2)
        (hx : x.1 ∈ simplexSupportFace S.1),
        score x = simplexSmallFaceMap value edge S ⟨x.1, hx⟩ := by
  classical
  let piece : SimplexSmallFace V → Set (SmallSupportSimplex V 2) :=
    fun S => {x | x.1 ∈ simplexSupportFace S.1}
  have closed : ∀ S, IsClosed (piece S) := fun S =>
    (simplexSupportFace_closed S.1).preimage continuous_subtype_val
  have cover : ∀ x : SmallSupportSimplex V 2, ∃ S, x ∈ piece S := by
    intro x
    refine ⟨⟨finiteSimplexSupport x.1, finiteSimplexSupport_nonempty x.1, x.2⟩, ?_⟩
    exact Finset.Subset.rfl
  let faceMap : ∀ S, C(piece S, Y) := fun S =>
    (simplexSmallFaceMap value edge S).comp {
      toFun := fun x => ⟨x.1.1, x.2⟩
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  have compatible : ∀ S T x (hS : x ∈ piece S) (hT : x ∈ piece T),
      faceMap S ⟨x, hS⟩ = faceMap T ⟨x, hT⟩ := by
    intro S T x hS hT
    by_cases hST : S = T
    · subst T
      rfl
    · obtain ⟨v, hv, hvS, hvT⟩ := simplexSmallFace_overlap_vertex S T hST x.1 hS hT
      change simplexSmallFaceMap value edge S ⟨x.1, hS⟩ =
        simplexSmallFaceMap value edge T ⟨x.1, hT⟩
      have hSv : stdSimplex.vertex v ∈ simplexSupportFace S.1 :=
        hv ▸ (show x.1 ∈ simplexSupportFace S.1 from hS)
      have hTv : stdSimplex.vertex v ∈ simplexSupportFace T.1 :=
        hv ▸ (show x.1 ∈ simplexSupportFace T.1 from hT)
      have hSpoint : (⟨x.1,hS⟩ : simplexSupportFace S.1)=
          ⟨stdSimplex.vertex v,hSv⟩ := Subtype.ext hv
      have hTpoint : (⟨x.1,hT⟩ : simplexSupportFace T.1)=
          ⟨stdSimplex.vertex v,hTv⟩ := Subtype.ext hv
      rw [hSpoint,hTpoint]
      exact (simplexSmallFaceMap_vertex value edge S v hvS hSv).trans
        (simplexSmallFaceMap_vertex value edge T v hvT hTv).symm
  obtain ⟨score, hscore⟩ := exists_finiteClosedCoverMap piece closed cover faceMap compatible
  exact ⟨score, fun S x hx => hscore S x hx⟩


/-- A deterministic lottery as a point of the actual one-skeleton. -/
def oneSkeletonVertex {V : Type*} [Fintype V] (v : V) : SmallSupportSimplex V 2 := by
  classical
  exact ⟨stdSimplex.vertex v, by simp [finiteSimplexSupport_vertex]⟩

/-- The pasting result with its exact vertex agreement made explicit. -/
theorem exists_simplexOneSkeletonMap_with_vertices
    {V Y : Type*} [Fintype V] [TopologicalSpace Y]
    (value : V → Y) (edge : ∀ a b, Path (value a) (value b)) :
    ∃ score : C(SmallSupportSimplex V 2, Y),
      (∀ v, score (oneSkeletonVertex v) = value v) ∧
      ∀ (S : SimplexSmallFace V) (x : SmallSupportSimplex V 2)
        (hx : x.1 ∈ simplexSupportFace S.1),
        score x = simplexSmallFaceMap value edge S ⟨x.1, hx⟩ := by
  classical
  obtain ⟨score, hscore⟩ := exists_simplexOneSkeletonMap value edge
  refine ⟨score, ?_, hscore⟩
  intro v
  let S : SimplexSmallFace V := ⟨{v}, by simp⟩
  have hx : (oneSkeletonVertex v).1 ∈ simplexSupportFace S.1 := by
    simp [oneSkeletonVertex, simplexSupportFace, S, finiteSimplexSupport_vertex]
  exact (hscore S (oneSkeletonVertex v) hx).trans
    (simplexSmallFaceMap_vertex value edge S v (by simp [S]) hx)

end FairDivision.Topology
