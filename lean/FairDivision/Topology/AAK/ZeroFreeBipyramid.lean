import FairDivision.Topology.NerveConnectivity.SimplicialCover
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# An explicit finite bipyramid target for a zero-free sign reversal

The target is the suspension of the boundary of the simplex on the coordinate
labels. Its two poles are fixed under coordinate permutations. Every other
face omits at least one base label and contains at most one pole.

A nonzero vector is sent into this complex by subtracting its smallest
coordinate, using the sign of its total sum for the pole, then normalizing.
All formulas are continuous and permutation-equivariant. This is an explicit
finite-complex reduction for the EXTERNAL AAK obstruction, not an assumption
that a relative equivariant obstruction has already been proved.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.AAK.ZeroFreeBipyramid

open FairDivision.Topology.NerveConnectivity
open Set
open scoped Classical

abbrev Vertex (V : Type*) := Bool ⊕ V

abbrev pole {V : Type*} (b : Bool) : Vertex V := Sum.inl b
abbrev base {V : Type*} (v : V) : Vertex V := Sum.inr v

/-- Suspension of the boundary of the coordinate-label simplex. -/
def complex (V : Type*) : PreAbstractSimplicialComplex (Vertex V) where
  faces := {S | S.Nonempty ∧
    ¬(pole true ∈ S ∧ pole false ∈ S) ∧ ∃ v : V, base v ∉ S}
  isRelLowerSet_faces := by
    intro S hS
    refine ⟨hS.1, ?_⟩
    intro T hTS hT
    refine ⟨hT, ?_, ?_⟩
    · exact fun h => hS.2.1 ⟨hTS h.1, hTS h.2⟩
    · obtain ⟨v, hv⟩ := hS.2.2
      exact ⟨v, fun h => hv (hTS h)⟩

abbrev Realization (V : Type*) [Fintype V] := simplicialRealization (complex V)

variable {V : Type*} [Fintype V] [Nonempty V]

/-- Lowest coordinate, using mathlib's finite attained infimum. -/
def minimum (y : V → ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty y

theorem minimum_le (y : V → ℝ) (v : V) : minimum y ≤ y v :=
  Finset.inf'_le _ (Finset.mem_univ v)

theorem minimum_attained (y : V → ℝ) : ∃ v, minimum y = y v := by
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty y
  exact ⟨v, hv⟩

@[fun_prop] theorem minimum_continuous : Continuous (minimum (V := V)) :=
  Continuous.finset_inf'_apply Finset.univ_nonempty (fun v _ => continuous_apply v)

def total (y : V → ℝ) : ℝ := ∑ v, y v

def baseNumerator (y : V → ℝ) (v : V) : ℝ := y v - minimum y

def gauge (y : V → ℝ) : ℝ := |total y| + ∑ v, baseNumerator y v

theorem baseNumerator_nonneg (y : V → ℝ) (v : V) : 0 ≤ baseNumerator y v :=
  sub_nonneg.mpr (minimum_le y v)

theorem gauge_nonneg (y : V → ℝ) : 0 ≤ gauge y :=
  add_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun v _ => baseNumerator_nonneg y v))

/-- The denominator vanishes only at the actual zero vector. -/
theorem gauge_eq_zero_iff (y : V → ℝ) : gauge y = 0 ↔ y = 0 := by
  constructor
  · intro hg
    have hb : 0 ≤ ∑ v : V, baseNumerator y v :=
      Finset.sum_nonneg (fun v _ => baseNumerator_nonneg y v)
    have ht : total y = 0 := by
      have hab : |total y| = 0 := by dsimp [gauge] at hg; linarith [abs_nonneg (total y)]
      exact abs_eq_zero.mp hab
    have hsum : (∑ v : V, baseNumerator y v) = 0 := by
      dsimp [gauge] at hg
      rw [ht, abs_zero, zero_add] at hg
      exact hg
    have hflat : ∀ v, y v = minimum y := by
      intro v
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun v _ => baseNumerator_nonneg y v)).mp hsum v (Finset.mem_univ v)
      exact sub_eq_zero.mp hz
    have hmin : minimum y = 0 := by
      have hcard : (Fintype.card V : ℝ) ≠ 0 := by
        exact_mod_cast (Fintype.card_ne_zero : Fintype.card V ≠ 0)
      have hm : (Fintype.card V : ℝ) * minimum y = 0 := by
        simpa [total, hflat, nsmul_eq_mul] using ht
      exact (mul_eq_zero.mp hm).resolve_left hcard
    funext v
    exact (hflat v).trans hmin
  · rintro rfl
    have hm : minimum (0 : V → ℝ) = 0 := by simp [minimum]
    simp [gauge, total, baseNumerator, hm]

theorem gauge_pos {y : V → ℝ} (hy : y ≠ 0) : 0 < gauge y :=
  lt_of_le_of_ne (gauge_nonneg y) (fun h => hy ((gauge_eq_zero_iff y).mp h.symm))

@[fun_prop] theorem total_continuous : Continuous (total (V := V)) :=
  continuous_finset_sum _ (fun v _ => continuous_apply v)

@[fun_prop] theorem gauge_continuous : Continuous (gauge (V := V)) := by
  exact total_continuous.abs.add (continuous_finset_sum _ (fun v _ =>
    (continuous_apply v).sub minimum_continuous))

/-- Raw barycentric weights of the normalization. -/
def weights (y : V → ℝ) : Vertex V → ℝ
  | Sum.inl true => max (total y) 0 / gauge y
  | Sum.inl false => max (-total y) 0 / gauge y
  | Sum.inr v => baseNumerator y v / gauge y

private theorem poleNumerators_sum (s : ℝ) : max s 0 + max (-s) 0 = |s| := by
  rcases le_total 0 s with hs | hs
  · rw [max_eq_left hs, max_eq_right (neg_nonpos.mpr hs), abs_of_nonneg hs]
    simp
  · rw [max_eq_right hs, max_eq_left (neg_nonneg.mpr hs), abs_of_nonpos hs]
    simp

theorem weights_nonneg {y : V → ℝ} (hy : y ≠ 0) (v : Vertex V) : 0 ≤ weights y v := by
  cases v with
  | inl b => cases b <;> exact div_nonneg (le_max_right _ _) (gauge_pos hy).le
  | inr v => exact div_nonneg (baseNumerator_nonneg y v) (gauge_pos hy).le

theorem weights_sum {y : V → ℝ} (hy : y ≠ 0) : (∑ v : Vertex V, weights y v) = 1 := by
  calc
    (∑ v : Vertex V, weights y v) =
        (max (total y) 0 + max (-total y) 0 + ∑ v : V, baseNumerator y v) / gauge y := by
      rw [Fintype.sum_sum_type, Fintype.sum_bool]
      simp only [weights]
      rw [← Finset.sum_div]
      ring
    _ = gauge y / gauge y := by rw [poleNumerators_sum]; rfl
    _ = 1 := div_self (ne_of_gt (gauge_pos hy))

/-- The two pole weights are never both positive. -/
theorem weights_no_two_poles {y : V → ℝ} (hy : y ≠ 0) :
    weights y (pole true) = 0 ∨ weights y (pole false) = 0 := by
  rcases le_total (total y) 0 with ht | ht
  · left
    simp [weights, max_eq_right ht]
  · right
    simp [weights, max_eq_right (neg_nonpos.mpr ht)]

theorem weights_missing_base (y : V → ℝ) : ∃ v, weights y (base v) = 0 := by
  obtain ⟨v, hv⟩ := minimum_attained y
  exact ⟨v, by simp [weights, baseNumerator, hv]⟩

/-- The normalized point in the actual finite complex. -/
def normalize (y : {y : V → ℝ // y ≠ 0}) : Realization V := by
  let w : stdSimplex ℝ (Vertex V) := ⟨weights y.1, weights_nonneg y.2, weights_sum y.2⟩
  refine ⟨w, finiteSimplexSupport_nonempty w, ?_, ?_⟩
  · intro h
    obtain hz | hz := weights_no_two_poles y.2
    · have hp := (mem_finiteSimplexSupport_iff w (pole true)).1 h.1
      rw [show w.1 (pole true) = 0 from hz] at hp
      exact (lt_irrefl _) hp
    · have hp := (mem_finiteSimplexSupport_iff w (pole false)).1 h.2
      rw [show w.1 (pole false) = 0 from hz] at hp
      exact (lt_irrefl _) hp
  · obtain ⟨v, hv⟩ := weights_missing_base y.1
    refine ⟨v, ?_⟩
    intro h
    have hp := (mem_finiteSimplexSupport_iff w (base v)).1 h
    rw [show w.1 (base v) = 0 from hv] at hp
    exact (lt_irrefl _) hp

@[simp] theorem normalize_coordinate (y : {y : V → ℝ // y ≠ 0}) (v : Vertex V) :
    (normalize y).1.1 v = weights y.1 v := rfl

/-- Continuity uses only finite min, finite sum, and division by the proved
strictly positive denominator. -/
@[fun_prop] theorem normalize_continuous : Continuous (normalize (V := V)) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  have hd : Continuous (fun y : {y : V → ℝ // y ≠ 0} => gauge y.1) :=
    (gauge_continuous (V := V)).comp continuous_subtype_val
  have hdn : ∀ y : {y : V → ℝ // y ≠ 0}, gauge y.1 ≠ 0 :=
    fun y => ne_of_gt (gauge_pos y.2)
  cases v with
  | inl b =>
      cases b
      · exact (((total_continuous.comp continuous_subtype_val).neg).max continuous_const).div hd hdn
      · exact ((total_continuous.comp continuous_subtype_val).max continuous_const).div hd hdn
  | inr v =>
      exact (((continuous_apply v).comp continuous_subtype_val).sub
        (minimum_continuous.comp continuous_subtype_val)).div hd hdn

/-- Coordinate permutations act by the same permutation on the base, fixing
both poles. -/
def vertexPerm (σ : Equiv.Perm V) : Equiv.Perm (Vertex V) :=
  Equiv.sumCongr (Equiv.refl Bool) σ

def permuteVector (σ : Equiv.Perm V) (y : V → ℝ) : V → ℝ :=
  fun v => y (σ.symm v)

theorem minimum_permute (σ : Equiv.Perm V) (y : V → ℝ) :
    minimum (permuteVector σ y) = minimum y := by
  apply le_antisymm
  · obtain ⟨v, hv⟩ := minimum_attained y
    calc
      minimum (permuteVector σ y) ≤ permuteVector σ y (σ v) := minimum_le _ _
      _ = minimum y := by simp [permuteVector, hv]
  · obtain ⟨v, hv⟩ := minimum_attained (permuteVector σ y)
    calc
      minimum y ≤ y (σ.symm v) := minimum_le _ _
      _ = minimum (permuteVector σ y) := hv.symm

theorem total_permute (σ : Equiv.Perm V) (y : V → ℝ) :
    total (permuteVector σ y) = total y := σ.symm.sum_comp y

theorem gauge_permute (σ : Equiv.Perm V) (y : V → ℝ) :
    gauge (permuteVector σ y) = gauge y := by
  simp only [gauge, baseNumerator, total_permute, minimum_permute]
  congr 1
  exact σ.symm.sum_comp (fun v => y v - minimum y)

theorem weights_permute (σ : Equiv.Perm V) (y : V → ℝ) (v : Vertex V) :
    weights (permuteVector σ y) v = weights y ((vertexPerm σ).symm v) := by
  cases v with
  | inl b => cases b <;> simp [weights, total_permute, gauge_permute, vertexPerm]
  | inr v => simp [weights, baseNumerator, permuteVector, minimum_permute,
      gauge_permute, vertexPerm]

/-- A constant strictly positive vector normalizes to the north pole;
a constant strictly negative one normalizes to the south pole. -/
theorem normalize_constant {c : ℝ} (hc : c ≠ 0) :
    (normalize ⟨fun _ : V => c, fun h => hc (congrFun h (Classical.choice inferInstance))⟩).1 =
      stdSimplex.vertex (pole (decide (0 < c))) := by
  have hm : minimum (fun _ : V => c) = c := by simp [minimum]
  have hcard : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  apply Subtype.ext
  funext v
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · have hsum : (Fintype.card V : ℝ) * c < 0 := mul_neg_of_pos_of_neg hcard hneg
    cases v with
    | inl b => cases b <;>
        simp [weights, total, baseNumerator, gauge, hm, nsmul_eq_mul,
          hneg.not_gt, max_eq_right hsum.le, max_eq_left (neg_nonneg.mpr hsum.le),
          abs_of_neg hsum, ne_of_gt (neg_pos.mpr hsum)]
    | inr v => simp [weights, baseNumerator, hm, hneg.not_gt]
  · have hsum : 0 < (Fintype.card V : ℝ) * c := mul_pos hcard hpos
    cases v with
    | inl b => cases b <;>
        simp [weights, total, baseNumerator, gauge, hm, nsmul_eq_mul,
          hpos, max_eq_left hsum.le, max_eq_right (neg_nonpos.mpr hsum.le),
          abs_of_pos hsum, ne_of_gt hsum]
    | inr v => simp [weights, baseNumerator, hm, hpos]


/-- Every target face has at most as many vertices as coordinate labels.
Thus its dimension is at most `card V - 1`, with the poles included. -/
theorem complex_face_card_le {S : Finset (Vertex V)} (hS : S ∈ complex V) :
    S.card ≤ Fintype.card V := by
  obtain ⟨v, hv⟩ := hS.2.2
  have hpole : ∃ b : Bool, pole b ∉ S := by
    by_cases hn : pole true ∈ S
    · exact ⟨false, fun h => hS.2.1 ⟨hn, h⟩⟩
    · exact ⟨true, hn⟩
  obtain ⟨b, hb⟩ := hpole
  let allowed : Finset (Vertex V) := (Finset.univ.erase (base v)).erase (pole b)
  have hsub : S ⊆ allowed := by
    intro z hz
    simp only [allowed, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun h => hb (h ▸ hz), fun h => hv (h ▸ hz)⟩
  have hcard : allowed.card = Fintype.card V := by
    have hbase : base v ∈ (Finset.univ : Finset (Vertex V)) := Finset.mem_univ _
    have hp : pole b ∈ (Finset.univ.erase (base v) : Finset (Vertex V)) := by simp
    rw [show allowed = (Finset.univ.erase (base v)).erase (pole b) from rfl,
      Finset.card_erase_of_mem hp, Finset.card_erase_of_mem hbase]
    simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_bool]
    omega
  exact hcard ▸ Finset.card_le_card hsub

/-- Literal pullback of barycentric coordinates under a base-label permutation. -/
def relabel (σ : Equiv.Perm V) (x : Realization V) : Realization V := by
  let w : stdSimplex ℝ (Vertex V) := ⟨fun v => x.1.1 ((vertexPerm σ).symm v),
    fun v => x.1.2.1 _, by
      exact ((vertexPerm σ).symm.sum_comp x.1.1).trans x.1.2.2⟩
  refine ⟨w, finiteSimplexSupport_nonempty w, ?_, ?_⟩
  · simpa [mem_finiteSimplexSupport_iff, w, vertexPerm] using x.2.2.1
  · obtain ⟨v, hv⟩ := x.2.2.2
    refine ⟨σ v, ?_⟩
    simpa [mem_finiteSimplexSupport_iff, w, vertexPerm] using hv

@[simp] theorem relabel_coordinate (σ : Equiv.Perm V) (x : Realization V) (v : Vertex V) :
    (relabel σ x).1.1 v = x.1.1 ((vertexPerm σ).symm v) := rfl

theorem permuteVector_ne_zero (σ : Equiv.Perm V) {y : V → ℝ} (hy : y ≠ 0) :
    permuteVector σ y ≠ 0 := by
  intro hz
  apply hy
  funext v
  have h := congrFun hz (σ v)
  simpa [permuteVector] using h

/-- Full equivariance of the actual normalization into the finite complex. -/
theorem normalize_relabel (σ : Equiv.Perm V) (y : {y : V → ℝ // y ≠ 0}) :
    normalize ⟨permuteVector σ y.1, permuteVector_ne_zero σ y.2⟩ =
      relabel σ (normalize y) := by
  apply Subtype.ext
  apply Subtype.ext
  funext v
  exact weights_permute σ y.1 v

/-- The fixed pole itself, as an actual point of the finite complex. -/
def polePoint (b : Bool) : Realization V := by
  refine ⟨stdSimplex.vertex (pole b), ?_⟩
  change (finiteSimplexSupport (stdSimplex.vertex (pole b))).Nonempty ∧ _
  rw [finiteSimplexSupport_vertex]
  refine ⟨Finset.singleton_nonempty _, ?_, ?_⟩
  · cases b <;> simp
  · exact ⟨Classical.choice inferInstance, by simp⟩

@[simp] theorem polePoint_coordinate (b : Bool) (v : Vertex V) :
    (polePoint (V := V) b).1.1 v = if v = pole b then 1 else 0 := by
  simp [polePoint, stdSimplex.vertex_coe, Pi.single_apply, eq_comm]

@[simp] theorem relabel_polePoint (σ : Equiv.Perm V) (b : Bool) :
    relabel σ (polePoint b) = polePoint b := by
  apply Subtype.ext
  apply Subtype.ext
  funext v
  cases v with
  | inl c => simp [relabel_coordinate, polePoint_coordinate, vertexPerm]
  | inr v => simp [relabel_coordinate, polePoint_coordinate, vertexPerm]

/-- Strict negative endpoint coordinates put the normalized point in the
south cone; there is no north-pole weight. -/
theorem normalize_negative_north_zero (y : {y : V → ℝ // y ≠ 0})
    (hy : ∀ v, y.1 v < 0) : (normalize y).1.1 (pole true) = 0 := by
  have ht : total y.1 < 0 :=
    Finset.sum_neg (fun v _ => hy v) Finset.univ_nonempty
  simp [weights, max_eq_right ht.le]

/-- Strict positive endpoint coordinates put the point in the north cone. -/
theorem normalize_positive_south_zero (y : {y : V → ℝ // y ≠ 0})
    (hy : ∀ v, 0 < y.1 v) : (normalize y).1.1 (pole false) = 0 := by
  have ht : 0 < total y.1 :=
    Finset.sum_pos (fun v _ => hy v) Finset.univ_nonempty
  simp [weights, max_eq_right (neg_nonpos.mpr ht.le)]

end FairDivision.Topology.AAK.ZeroFreeBipyramid
