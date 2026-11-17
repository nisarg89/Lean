import FairDivision.Topology.AAK.SuspendedJoinVertexSelection
import RequestProject.Dvoretzky.Dold.Main
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Actual fine source-time selection for the relative AAK prism

The source chains and their shrinking barycentric mesh are the imported DKGM
ones. Compact uniform continuity supplies one spatial mesh and one finite time
grid for the entire homotopy. The least-good-color selector maps each adjacent
source-time prism into one actual target face, preserves the exact endpoints,
and is equivariant. This is a concrete construction from a continuous pole
homotopy, not an assumed simplicial approximation or invariance principle.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.AAK.SuspendedJoinPrismSelection

open Dvoretzky Dvoretzky.Dold
open FairDivision.Topology FairDivision.Topology.NerveConnectivity
open ZeroFreeBipyramid
open scoped BigOperators Classical

variable (p : ℕ) [Fact p.Prime]

abbrev SourceSpace := Fin p → Multiplicative (ZMod p) → ℝ
abbrev Source := GroupJoin (Multiplicative (ZMod p)) p
abbrev TargetVertex := SuspensionVertex (p - 1) (ZMod p)
abbrev Target := SuspensionRealization (p - 1) (ZMod p)

/-- The actual action on the compact source join. -/
def sourceAct (g : Multiplicative (ZMod p)) (x : Source p) : Source p :=
  ⟨joinAct g x.1, joinAct_mem g x.2⟩

/-- Time j/K, including both endpoints. -/
def gridTime (K : ℕ) (hK : 0 < K) (j : Fin (K + 1)) : unitInterval :=
  ⟨(j.val : ℝ) / K, by
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    refine ⟨div_nonneg (Nat.cast_nonneg _) hK'.le, (div_le_one hK').2 ?_⟩
    exact_mod_cast (show j.val ≤ K by omega)⟩

@[simp] theorem gridTime_zero (K : ℕ) (hK : 0 < K) : gridTime K hK 0 = 0 := by
  apply Subtype.ext
  simp [gridTime]

@[simp] theorem gridTime_last (K : ℕ) (hK : 0 < K) : gridTime K hK (Fin.last K) = 1 := by
  apply Subtype.ext
  simp [gridTime, ne_of_gt hK]

theorem gridTime_step_dist (K : ℕ) (hK : 0 < K) (j : Fin K) :
    dist (gridTime K hK j.castSucc) (gridTime K hK j.succ) = 1 / (K : ℝ) := by
  change |(j.val : ℝ) / (K : ℝ) - ((j.val + 1 : ℕ) : ℝ) / (K : ℝ)| = _
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  push_cast
  rw [← sub_div]
  have he : (j.val : ℝ) - ((j.val : ℝ) + 1) = -1 := by ring
  rw [he, neg_div, abs_neg, abs_of_pos (one_div_pos.mpr hK')]

/-- A total vertex map on the ambient ordered-chain vertex type. Only its
restriction to the actual source join is used. -/
def selector (H : C(unitInterval × Source p, Target p)) (t : unitInterval)
    (x : SourceSpace p) : TargetVertex p :=
  if hx : x ∈ GroupJoin (Multiplicative (ZMod p)) p then
    suspensionVertexSelection (H (t, ⟨x, hx⟩)) else pole false

@[simp] theorem selector_on_source (H : C(unitInterval × Source p, Target p))
    (t : unitInterval) (x : Source p) :
    selector p H t x.1 = suspensionVertexSelection (H (t, x)) := by
  simp [selector, x.2]

/-- Both maps of one adjacent-time prism use vertices of a common simplex. -/
def PrismFace (f g : SourceSpace p → TargetVertex p) (l : List (SourceSpace p)) : Prop :=
  (l.map f ++ l.map g).toFinset ∈ suspensionJoinComplex (p - 1) (ZMod p)

/-- The literal fine chains already carrying the imported Dold recurrence. -/
def fineChain (r k : ℕ) : Chain (ZMod p) (SourceSpace p) :=
  (sd ^ r) (cseq p k)

private theorem homotopy_uniform_mesh (H : C(unitInterval × Source p, Target p)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t s (x y : Source p),
      dist t s < δ → dist x.1 y.1 < δ →
      ∀ v, |(H (t, x)).1.1 v - (H (s, y)).1.1 v| < 1 / (2 * (p : ℝ)) := by
  letI : CompactSpace (Source p) :=
    isCompact_iff_compactSpace.mp (isCompact_groupJoin (G := Multiplicative (ZMod p)) p)
  have hu : UniformContinuous H := CompactSpace.uniformContinuous_of_continuous H.continuous
  have hε : (0 : ℝ) < 1 / (2 * (p : ℝ)) := by
    have hp : 0 < p := (Fact.out : p.Prime).pos
    positivity
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.1 hu _ hε
  refine ⟨δ, hδ, ?_⟩
  intro t s x y ht hx v
  have hd : dist (t, x) (s, y) < δ := by
    rw [Prod.dist_eq]
    exact max_lt ht hx
  have hout := hclose hd
  exact lt_of_le_of_lt (dist_le_pi_dist (H (t, x)).1.1 (H (s, y)).1.1 v) hout

/-- A uniformly small source list and two sufficiently close times give a
single containing target face, for the entire staircase prism. -/
theorem prismFace_of_small
    (H : C(unitInterval × Source p, Target p)) {δ : ℝ}
    (hclose : ∀ t s (x y : Source p), dist t s < δ → dist x.1 y.1 < δ →
      ∀ v, |(H (t, x)).1.1 v - (H (s, y)).1.1 v| < 1 / (2 * (p : ℝ)))
    (hδ : 0 < δ) (t s : unitInterval) (ht : dist t s < δ)
    (l : List (SourceSpace p)) (hl : l ≠ [])
    (hJ : ∀ x ∈ l, x ∈ GroupJoin (Multiplicative (ZMod p)) p)
    (hd : ∀ x ∈ l, ∀ y ∈ l, dist x y < δ) :
    PrismFace p (selector p H t) (selector p H s) l := by
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil l hl
  let anchor : Source p := ⟨x, hJ x hx⟩
  let S := finiteSimplexSupport (H (t, anchor)).1
  have hsub : (l.map (selector p H t) ++ l.map (selector p H s)).toFinset ⊆ S := by
    intro v hv
    simp only [List.mem_toFinset, List.mem_append, List.mem_map] at hv
    rcases hv with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
    · have hyJ := hJ y hy
      rw [show selector p H t y = suspensionVertexSelection (H (t, ⟨y, hyJ⟩)) by
        simp [selector, hyJ]]
      exact suspensionVertexSelection_mem_of_close p (H (t, anchor)) (H (t, ⟨y, hyJ⟩))
        (hclose t t anchor ⟨y, hyJ⟩ (by simpa using hδ) (hd x hx y hy))
    · have hyJ := hJ y hy
      rw [show selector p H s y = suspensionVertexSelection (H (s, ⟨y, hyJ⟩)) by
        simp [selector, hyJ]]
      exact suspensionVertexSelection_mem_of_close p (H (t, anchor)) (H (s, ⟨y, hyJ⟩))
        (hclose t s anchor ⟨y, hyJ⟩ ht (hd x hx y hy))
  apply ((suspensionJoinComplex (p - 1) (ZMod p)).isRelLowerSet_faces
    (H (t, anchor)).2).2 hsub
  refine ⟨selector p H t x, ?_⟩
  simp only [List.mem_toFinset, List.mem_append, List.mem_map]
  exact Or.inl ⟨x, hx, rfl⟩

/-- Actual constructive source-time selection. The source has p colors;
its relevant lists have dimensions 0 through p−1. The same r and K work
for every one of those lists and every adjacent pair of time slices. -/
theorem exists_fine_prism_selection
    (H : C(unitInterval × Source p, Target p))
    (hSouth : ∀ x, H (0, x) = suspensionPole (p - 1) (ZMod p) false)
    (hNorth : ∀ x, H (1, x) = suspensionPole (p - 1) (ZMod p) true)
    (heq : ∀ g t x, H (t, sourceAct p g x) =
      suspensionRelabel p (-g.toAdd) (H (t, x))) :
    ∃ (K : ℕ) (hK : 0 < K) (r : ℕ)
      (sel : Fin (K + 1) → SourceSpace p → TargetVertex p),
      (∀ x ∈ GroupJoin (Multiplicative (ZMod p)) p, sel 0 x = pole false) ∧
      (∀ x ∈ GroupJoin (Multiplicative (ZMod p)) p, sel (Fin.last K) x = pole true) ∧
      (∀ j g x, x ∈ GroupJoin (Multiplicative (ZMod p)) p →
        sel j (joinAct g x) = suspensionTranslate (-g.toAdd) (sel j x)) ∧
      (∀ k ≤ p - 1, ∀ l ∈ (fineChain p r k).support,
        l.length = k + 1 ∧ (∀ x ∈ l, x ∈ GroupJoin (Multiplicative (ZMod p)) p) ∧
        ∀ j : Fin K, PrismFace p (sel j.castSucc) (sel j.succ) l) := by
  obtain ⟨δ, hδpos, hδ⟩ := homotopy_uniform_mesh p H
  obtain ⟨K₀, hKδ⟩ := exists_nat_one_div_lt hδpos
  let K := K₀ + 1
  have hK : 0 < K := by omega
  let q : ℝ := (p : ℝ) / (p + 1)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by dsimp [q]; rw [div_lt_one (by positivity)]; linarith
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hδpos hq1
  let sel : Fin (K + 1) → SourceSpace p → TargetVertex p :=
    fun j => selector p H (gridTime K hK j)
  refine ⟨K, hK, r, sel, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp [sel, selector, hx, hSouth]
  · intro x hx
    simp [sel, selector, hx, hNorth]
  · intro j g x hx
    have hgx := joinAct_mem g hx
    simp only [sel, selector, dif_pos hx, dif_pos hgx]
    rw [show H (gridTime K hK j, ⟨joinAct g x, hgx⟩) =
      suspensionRelabel p (-g.toAdd) (H (gridTime K hK j, ⟨x, hx⟩)) from
      heq g (gridTime K hK j) ⟨x, hx⟩]
    exact suspensionVertexSelection_translate p (-g.toAdd) _
  · intro k hk l hl
    obtain ⟨l₀, hl₀, hl'⟩ := mem_support_map hl
    have hV : VList p k l₀ := cseq_supported p k hl₀
    obtain ⟨hlen, hhull, hdist⟩ := sdIter_support r l₀ 1 hV.dist_le l hl'
    have hlen' := hV.length_eq
    have hk' : k < p := by have hp := (Fact.out : p.Prime).pos; omega
    have hJ : ∀ x ∈ l, x ∈ GroupJoin (Multiplicative (ZMod p)) p :=
      fun x hx => hV.hull_subset hk' (hhull x hx)
    have hd : ∀ x ∈ l, ∀ y ∈ l, dist x y < δ := by
      intro x hx y hy
      refine lt_of_le_of_lt (hdist x hx y hy) (lt_of_le_of_lt ?_ hr)
      rw [mul_one, hlen']
      refine pow_le_pow_left₀ (ratio_nonneg (k + 1)) ?_ r
      dsimp [q]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hkn : (k : ℝ) + 1 ≤ p := by
        exact_mod_cast (Nat.succ_le_of_lt hk')
      push_cast
      nlinarith
    refine ⟨hlen.trans hlen', hJ, ?_⟩
    intro j
    apply prismFace_of_small p H hδ hδpos (gridTime K hK j.castSucc)
      (gridTime K hK j.succ) ?_ l (by have := hlen.trans hlen'; intro hz; simp [hz] at this) hJ hd
    rw [gridTime_step_dist]
    simpa [K, Nat.cast_add, Nat.cast_one] using hKδ

end FairDivision.Topology.AAK.SuspendedJoinPrismSelection
