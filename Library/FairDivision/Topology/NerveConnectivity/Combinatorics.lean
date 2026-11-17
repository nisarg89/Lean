import FairDivision.Topology.NerveConnectivity.Basic

/-!
# Finite-cover bookkeeping for the nerve induction

The restrictions and intersections here preserve precisely the connectivity
indices needed by the induction over the number of covering subcomplexes.
They are independent of the still-open higher-dimensional gluing theorem.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe u v

variable {ι : Type v} {X : Type u} [TopologicalSpace X] [Fintype ι]

/-- Restrict a cover to the members in a finite index set. -/
def restrictCover (C : ι → Set X) (J : Finset ι) : J → Set X :=
  fun i => C i.1

def subtypeEmbedding (J : Finset ι) : J ↪ ι :=
  ⟨Subtype.val, Subtype.val_injective⟩

theorem coverIntersection_restrict (C : ι → Set X) (J : Finset ι)
    (T : Finset J) :
    coverIntersection (restrictCover C J) T =
      coverIntersection C (T.map (subtypeEmbedding J)) := by
  ext x
  simp only [coverIntersection, restrictCover, Set.mem_iInter]
  constructor
  · intro h i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    exact h j hj
  · intro h j hj
    exact h j.1 (Finset.mem_map.mpr ⟨j, hj, rfl⟩)

/-- The finite-cover nerve hypotheses hold on every nonempty subfamily. -/
theorem NerveConnectivityHypotheses.restrict (C : ι → Set X)
    {k : ℕ} (hC : NerveConnectivityHypotheses k C)
    (J : Finset ι) [Nonempty J] :
    NerveConnectivityHypotheses k (restrictCover C J) := by
  constructor
  · obtain ⟨x, hx⟩ := hC.1
    exact ⟨x, fun i => hx i.1⟩
  · intro T hT hcard
    rw [coverIntersection_restrict]
    have hmap : (T.map (subtypeEmbedding J)).Nonempty := Finset.Nonempty.map hT
    have hmapcard : (T.map (subtypeEmbedding J)).card = T.card := Finset.card_map _
    simpa [hmapcard] using hC.2 (T.map (subtypeEmbedding J)) hmap
      (by omega)

variable [DecidableEq ι]

/-- Intersect every member of a restricted cover with one fixed member. -/
def intersectCover (C : ι → Set X) (i₀ : ι) (J : Finset ι) : J → Set X :=
  fun i => C i.1 ∩ C i₀

/-- Intersecting the union of a subfamily with one fixed set is the union
of the corresponding pairwise intersections. -/
theorem coverUnion_intersect (C : ι → Set X) (i₀ : ι) (J : Finset ι) :
    coverUnion (intersectCover C i₀ J) =
      coverUnion (restrictCover C J) ∩ C i₀ := by
  ext x
  simp only [coverUnion, intersectCover, restrictCover, Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨⟨i, hi.1⟩, hi.2⟩
  · rintro ⟨⟨i, hi⟩, h₀⟩
    exact ⟨i, ⟨hi, h₀⟩⟩

theorem coverIntersection_intersect (C : ι → Set X) (i₀ : ι)
    (J : Finset ι) (T : Finset J) (hT : T.Nonempty) :
    coverIntersection (intersectCover C i₀ J) T =
      coverIntersection C (insert i₀ (T.map (subtypeEmbedding J))) := by
  ext x
  simp only [coverIntersection, intersectCover, Set.mem_iInter, Set.mem_inter_iff]
  constructor
  · intro h i hi
    rcases Finset.mem_insert.mp hi with rfl | himap
    · obtain ⟨j, hj⟩ := hT
      exact (h j hj).2
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp himap
      exact (h j hj).1
  · intro h j hj
    refine ⟨h j.1 ?_, h i₀ (Finset.mem_insert_self _ _)⟩
    exact Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨j, hj, rfl⟩)

theorem card_intersection_indices (i₀ : ι) (J : Finset ι)
    (hi₀ : i₀ ∉ J) (T : Finset J) :
    (insert i₀ (T.map (subtypeEmbedding J))).card = T.card + 1 := by
  have hnot : i₀ ∉ T.map (subtypeEmbedding J) := by
    intro hmem
    obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hmem
    apply hi₀
    exact hj ▸ j.2
  rw [Finset.card_insert_of_notMem hnot, Finset.card_map]

/-- The one-step intersection shift for any connectivity predicate. -/
theorem FiniteCoverConnectivityHypotheses.intersect
    (P : ℕ → Set X → Prop) (C : ι → Set X)
    {k : ℕ} (hk : 1 ≤ k)
    (hC : FiniteCoverConnectivityHypotheses P k C)
    (i₀ : ι) (J : Finset ι) (hi₀ : i₀ ∉ J) [Nonempty J] :
    FiniteCoverConnectivityHypotheses P (k - 1)
      (intersectCover C i₀ J) := by
  constructor
  · obtain ⟨x, hx⟩ := hC.1
    exact ⟨x, fun i => ⟨hx i.1, hx i₀⟩⟩
  · intro T hT hcard
    rw [coverIntersection_intersect C i₀ J T hT]
    have hbig : (insert i₀ (T.map (subtypeEmbedding J))).Nonempty :=
      Finset.insert_nonempty _ _
    have hcard' := card_intersection_indices i₀ J hi₀ T
    have hbound : (insert i₀ (T.map (subtypeEmbedding J))).card ≤ k + 1 := by
      omega
    have hresult := hC.2 (insert i₀ (T.map (subtypeEmbedding J))) hbig hbound
    convert hresult using 1 <;> omega

/-- The exact shift used in the inductive proof of the nerve theorem: after
intersecting each remaining cover member with a fixed one, the target
connectivity parameter drops by one. -/
theorem NerveConnectivityHypotheses.intersect (C : ι → Set X)
    {k : ℕ} (hk : 1 ≤ k) (hC : NerveConnectivityHypotheses k C)
    (i₀ : ι) (J : Finset ι) (hi₀ : i₀ ∉ J) [Nonempty J] :
    NerveConnectivityHypotheses (k - 1) (intersectCover C i₀ J) :=
  FiniteCoverConnectivityHypotheses.intersect
    (fun j S => ConnectedThrough j S) C hk hC i₀ J hi₀

end FairDivision.Topology.NerveConnectivity
