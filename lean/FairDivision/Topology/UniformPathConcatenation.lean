import FairDivision.Topology.FiniteClosedCoverMaps
import Mathlib.Topology.Path

/-!
# Concatenate a finite family of paths on equal subintervals

The `k`th path is run on `[k/length,(k+1)/length]`, without changing its
own unit-interval parameter. This supplies exactly the manuscript's first
(equal) subdivision, rather than the unequal dyadic timings of recursive
binary path concatenation.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology

open Set

/-- The closed `k`th unit block in the interval `[0,length]`. -/
def uniformPathBlock {length : ℕ} (k : Fin length) :
    Set (Set.Icc (0 : ℝ) length) :=
  {t | (k.1 : ℝ) ≤ t.1 ∧ t.1 ≤ (k.1 : ℝ) + 1}

theorem uniformPathBlock_closed {length : ℕ} (k : Fin length) :
    IsClosed (uniformPathBlock k) :=
  (isClosed_le continuous_const continuous_subtype_val).inter
    (isClosed_le continuous_subtype_val continuous_const)

/-- The equal blocks cover the whole parameter interval, including its ends. -/
theorem uniformPathBlock_cover (length : ℕ) (hlength : 0 < length)
    (t : Set.Icc (0 : ℝ) length) : ∃ k : Fin length, t ∈ uniformPathBlock k := by
  induction length with
  | zero => omega
  | succ length ih =>
      by_cases hzero : length = 0
      · subst length
        exact ⟨0, by simpa [uniformPathBlock] using t.2⟩
      · by_cases ht : t.1 ≤ length
        · obtain ⟨k, hk⟩ := ih (by omega) ⟨t.1, t.2.1, ht⟩
          exact ⟨k.castSucc, hk⟩
        · refine ⟨Fin.last length, ?_⟩
          exact ⟨(le_of_not_ge ht), by simpa using t.2.2⟩

/-- Rescale one closed block to the unit interval. -/
def uniformPathBlockParameter {length : ℕ} (k : Fin length)
    (t : uniformPathBlock k) : unitInterval :=
  ⟨t.1.1 - k.1, sub_nonneg.mpr t.2.1, by linarith [t.2.2]⟩

theorem uniformPathBlockParameter_continuous {length : ℕ} (k : Fin length) :
    Continuous (uniformPathBlockParameter k) := by
  exact ((continuous_subtype_val.comp continuous_subtype_val).sub
    continuous_const).subtype_mk _

/-- The actual continuous map on `[0,length]` with the prescribed individual
paths on every unit block. -/
theorem exists_uniformPathMap
    {X : Type*} [TopologicalSpace X] {length : ℕ} (hlength : 0 < length)
    (vertex : Fin (length + 1) → X)
    (segment : ∀ k : Fin length, Path (vertex k.castSucc) (vertex k.succ)) :
    ∃ F : C(Set.Icc (0 : ℝ) length, X),
      ∀ (k : Fin length) (t : Set.Icc (0 : ℝ) length)
        (ht : t ∈ uniformPathBlock k),
        F t = segment k (uniformPathBlockParameter k ⟨t, ht⟩) := by
  classical
  let f : ∀ k : Fin length, C(uniformPathBlock k, X) := fun k =>
    ⟨fun t => segment k (uniformPathBlockParameter k t),
      (segment k).continuous.comp (uniformPathBlockParameter_continuous k)⟩
  apply exists_finiteClosedCoverMap uniformPathBlock uniformPathBlock_closed
    (uniformPathBlock_cover length hlength) f
  intro i j t hi hj
  rcases lt_trichotomy i.1 j.1 with hij | hij | hji
  · have hstep : i.1 + 1 ≤ j.1 := hij
    have hstepR : (i.1 : ℝ) + 1 ≤ j.1 := by exact_mod_cast hstep
    have ht : t.1 = j.1 := le_antisymm (hi.2.trans hstepR) hj.1
    have hnext : i.1 + 1 = j.1 := by
      have he : (i.1 : ℝ) + 1 = j.1 := le_antisymm hstepR (hj.1.trans hi.2)
      exact_mod_cast he
    have heq : i.succ = j.castSucc := Fin.ext hnext
    have hleft : uniformPathBlockParameter i ⟨t, hi⟩ = 1 := by
      apply Subtype.ext
      dsimp [uniformPathBlockParameter]
      rw [ht]
      have he : (i.1 : ℝ) + 1 = j.1 := by exact_mod_cast hnext
      linarith
    have hright : uniformPathBlockParameter j ⟨t, hj⟩ = 0 := by
      apply Subtype.ext
      simp [uniformPathBlockParameter, ht]
    change segment i _ = segment j _
    rw [hleft, hright, Path.target, Path.source, heq]
  · have he : i = j := Fin.ext hij
    subst j
    rfl
  · have hstep : j.1 + 1 ≤ i.1 := hji
    have hstepR : (j.1 : ℝ) + 1 ≤ i.1 := by exact_mod_cast hstep
    have ht : t.1 = i.1 := le_antisymm (hj.2.trans hstepR) hi.1
    have hnext : j.1 + 1 = i.1 := by
      have he : (j.1 : ℝ) + 1 = i.1 := le_antisymm hstepR (hi.1.trans hj.2)
      exact_mod_cast he
    have heq : j.succ = i.castSucc := Fin.ext hnext
    have hleft : uniformPathBlockParameter j ⟨t, hj⟩ = 1 := by
      apply Subtype.ext
      dsimp [uniformPathBlockParameter]
      rw [ht]
      have he : (j.1 : ℝ) + 1 = i.1 := by exact_mod_cast hnext
      linarith
    have hright : uniformPathBlockParameter i ⟨t, hi⟩ = 0 := by
      apply Subtype.ext
      simp [uniformPathBlockParameter, ht]
    change segment i _ = segment j _
    rw [hleft, hright, Path.target, Path.source, heq]

/-- A fixed, shared equal-subdivision concatenation. -/
def uniformPathMap
    {X : Type*} [TopologicalSpace X] {length : ℕ} (hlength : 0 < length)
    (vertex : Fin (length + 1) → X)
    (segment : ∀ k : Fin length, Path (vertex k.castSucc) (vertex k.succ)) :
    C(Set.Icc (0 : ℝ) length, X) :=
  Classical.choose (exists_uniformPathMap hlength vertex segment)

theorem uniformPathMap_on_block
    {X : Type*} [TopologicalSpace X] {length : ℕ} (hlength : 0 < length)
    (vertex : Fin (length + 1) → X)
    (segment : ∀ k : Fin length, Path (vertex k.castSucc) (vertex k.succ))
    (k : Fin length) (t : Set.Icc (0 : ℝ) length)
    (ht : t ∈ uniformPathBlock k) :
    uniformPathMap hlength vertex segment t =
      segment k (uniformPathBlockParameter k ⟨t, ht⟩) :=
  Classical.choose_spec (exists_uniformPathMap hlength vertex segment) k t ht

/-- Equal subdivision of the unit interval into `length` pieces. -/
def uniformPath
    {X : Type*} [TopologicalSpace X] {length : ℕ} (hlength : 0 < length)
    (vertex : Fin (length + 1) → X)
    (segment : ∀ k : Fin length, Path (vertex k.castSucc) (vertex k.succ)) :
    Path (vertex 0) (vertex (Fin.last length)) where
  toFun t := uniformPathMap hlength vertex segment
    ⟨(length : ℝ) * t.1, mul_nonneg (Nat.cast_nonneg _) t.2.1,
      by nlinarith [t.2.2, Nat.cast_nonneg (α := ℝ) length]⟩
  continuous_toFun := (uniformPathMap hlength vertex segment).continuous.comp
    ((continuous_const.mul continuous_subtype_val).subtype_mk _)
  source' := by
    have hblock : (⟨(length : ℝ) * 0, by positivity, by simp⟩ :
        Set.Icc (0 : ℝ) length) ∈ uniformPathBlock (⟨0, hlength⟩ : Fin length) := by
      simp [uniformPathBlock]
    change uniformPathMap hlength vertex segment
      ⟨(length : ℝ) * 0, by positivity, by simp⟩ = vertex 0
    rw [uniformPathMap_on_block hlength vertex segment ⟨0, hlength⟩ _ hblock]
    have ht : uniformPathBlockParameter (⟨0, hlength⟩ : Fin length)
        ⟨⟨(length : ℝ) * 0, by positivity, by simp⟩, hblock⟩ = 0 := by
      apply Subtype.ext
      simp [uniformPathBlockParameter]
    rw [ht, Path.source]
    congr 1
  target' := by
    let last : Fin length := ⟨length - 1, by omega⟩
    have hlast : last.1 + 1 = length := by dsimp [last]; omega
    have hcast : (last.1 : ℝ) + 1 = length := by exact_mod_cast hlast
    have hblock : (⟨(length : ℝ) * 1, by positivity, by simp⟩ :
        Set.Icc (0 : ℝ) length) ∈ uniformPathBlock last := by
      change (last.1 : ℝ) ≤ (length : ℝ) * 1 ∧
        (length : ℝ) * 1 ≤ (last.1 : ℝ) + 1
      constructor <;> nlinarith
    change uniformPathMap hlength vertex segment
      ⟨(length : ℝ) * 1, by positivity, by simp⟩ = vertex (Fin.last length)
    rw [uniformPathMap_on_block hlength vertex segment last _ hblock]
    have ht : uniformPathBlockParameter last
        ⟨⟨(length : ℝ) * 1, by positivity, by simp⟩, hblock⟩ = 1 := by
      apply Subtype.ext
      dsimp [uniformPathBlockParameter]
      linarith
    rw [ht, Path.target]
    congr 1
    exact Fin.ext hlast

/-- Literal unit-interval time in the kth equal subinterval. All coordinates
of a vector-valued path use this same parameter. -/
def uniformPathTime {length : ℕ} (hlength : 0 < length)
    (k : Fin length) (t : unitInterval) : unitInterval := by
  have hlengthR : (0 : ℝ) < length := by exact_mod_cast hlength
  have hk : (k.val : ℝ) + 1 ≤ length := by
    exact_mod_cast (Nat.succ_le_of_lt k.isLt)
  refine ⟨((k.val : ℝ) + t.val) / length, ?_, ?_⟩
  · exact div_nonneg (add_nonneg (Nat.cast_nonneg _) t.2.1) hlengthR.le
  · apply (div_le_one hlengthR).2
    linarith [t.2.2]

/-- Exact agreement with the prescribed segment on every equal subinterval,
including both shared subdivision endpoints. This reuses the already proved
closed-block pasting equality; the individual segment is not reparameterized.
-/
theorem uniformPath_on_subinterval
    {X : Type*} [TopologicalSpace X] {length : ℕ} (hlength : 0 < length)
    (vertex : Fin (length + 1) → X)
    (segment : ∀ k : Fin length, Path (vertex k.castSucc) (vertex k.succ))
    (k : Fin length) (t : unitInterval) :
    uniformPath hlength vertex segment (uniformPathTime hlength k t) = segment k t := by
  have hlengthR : (length : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hlength)
  have hscale : (length : ℝ) * (uniformPathTime hlength k t).val =
      (k.val : ℝ) + t.val := by
    change (length : ℝ) * (((k.val : ℝ) + t.val) / length) = _
    field_simp [hlengthR] <;> ring
  let s : Set.Icc (0 : ℝ) length :=
    ⟨(length : ℝ) * (uniformPathTime hlength k t).val,
      mul_nonneg (Nat.cast_nonneg _) (uniformPathTime hlength k t).2.1,
      by nlinarith [(uniformPathTime hlength k t).2.2,
        Nat.cast_nonneg (α := ℝ) length]⟩
  have hs : s ∈ uniformPathBlock k := by
    change (k.val : ℝ) ≤ (length : ℝ) * (uniformPathTime hlength k t).val ∧
      (length : ℝ) * (uniformPathTime hlength k t).val ≤ (k.val : ℝ) + 1
    rw [hscale]
    constructor <;> linarith [t.2.1,t.2.2]
  change uniformPathMap hlength vertex segment s = segment k t
  rw [uniformPathMap_on_block hlength vertex segment k s hs]
  congr 1
  apply Subtype.ext
  change (length : ℝ) * (uniformPathTime hlength k t).val - (k.val : ℝ) = t.val
  rw [hscale]
  ring

/-- Every value of the equal-subdivision path is a value of one of the
original segments, so the same local witness proofs can be reused. -/
theorem uniformPath_property
    {X : Type*} [TopologicalSpace X] {length : ℕ} (hlength : 0 < length)
    (vertex : Fin (length + 1) → X)
    (segment : ∀ k : Fin length, Path (vertex k.castSucc) (vertex k.succ))
    (P : X → Prop) (hP : ∀ k t, P (segment k t)) :
    ∀ t, P (uniformPath hlength vertex segment t) := by
  intro t
  let s : Set.Icc (0 : ℝ) length :=
    ⟨(length : ℝ) * t.1, mul_nonneg (Nat.cast_nonneg _) t.2.1,
      by nlinarith [t.2.2, Nat.cast_nonneg (α := ℝ) length]⟩
  obtain ⟨k, hk⟩ := uniformPathBlock_cover length hlength s
  change P (uniformPathMap hlength vertex segment s)
  rw [uniformPathMap_on_block hlength vertex segment k s hk]
  exact hP k _

end FairDivision.Topology
