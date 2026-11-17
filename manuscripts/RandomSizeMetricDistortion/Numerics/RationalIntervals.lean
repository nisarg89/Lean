import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Numerics_RationalIntervals

private theorem linear_interval {a lo hi y L U : ℝ} (hy : y ∈ Icc lo hi)
    (hl : L ≤ a*lo) (hl' : L ≤ a*hi) (hu : a*lo ≤ U) (hu' : a*hi ≤ U) :
    a*y ∈ Icc L U := by
  by_cases ha : 0 ≤ a
  · exact ⟨hl.trans (mul_le_mul_of_nonneg_left hy.1 ha),
      (mul_le_mul_of_nonneg_left hy.2 ha).trans hu'⟩
  · have ha' : a ≤ 0 := le_of_not_ge ha
    exact ⟨hl'.trans (mul_le_mul_of_nonpos_left hy.2 ha'),
      (mul_le_mul_of_nonpos_left hy.1 ha').trans hu⟩

private theorem rectangle_product {al au bl bu x y : ℝ}
    (hx : x ∈ Icc al au) (hy : y ∈ Icc bl bu) :
    x*y ∈ Icc (min (min (al*bl) (al*bu)) (min (au*bl) (au*bu)))
      (max (max (al*bl) (al*bu)) (max (au*bl) (au*bu))) := by
  let L := min (min (al*bl) (al*bu)) (min (au*bl) (au*bu))
  let U := max (max (al*bl) (al*bu)) (max (au*bl) (au*bu))
  have hal : al*y ∈ Icc L U := linear_interval hy
    ((min_le_left _ _).trans (min_le_left _ _))
    ((min_le_left _ _).trans (min_le_right _ _))
    ((le_max_left _ _).trans (le_max_left _ _))
    ((le_max_right _ _).trans (le_max_left _ _))
  have hau : au*y ∈ Icc L U := linear_interval hy
    ((min_le_right _ _).trans (min_le_left _ _))
    ((min_le_right _ _).trans (min_le_right _ _))
    ((le_max_left _ _).trans (le_max_right _ _))
    ((le_max_right _ _).trans (le_max_right _ _))
  change x*y ∈ Icc L U
  simpa only [mul_comm] using linear_interval (a := y) hx
    (by simpa [mul_comm] using hal.1) (by simpa [mul_comm] using hau.1)
    (by simpa [mul_comm] using hal.2) (by simpa [mul_comm] using hau.2)

theorem from_children (h : Needs) : Statement := by
  intro e
  induction e with
  | const q =>
    intro B hB x hx
    exact ⟨le_rfl,le_rfl⟩
  | var i =>
    intro B hB x hx
    exact hx i
  | add a b ha hb =>
    intro B hB x hx
    have h₁ := ha B hB x hx
    have h₂ := hb B hB x hx
    simpa [eval, intervalEval, intervalAdd] using
      (show eval a x+eval b x ∈ Icc
        (((intervalEval a B).lo : ℝ)+((intervalEval b B).lo : ℝ))
        (((intervalEval a B).hi : ℝ)+((intervalEval b B).hi : ℝ)) from
        ⟨add_le_add h₁.1 h₂.1,add_le_add h₁.2 h₂.2⟩)
  | mul a b ha hb =>
    intro B hB x hx
    simpa [eval, intervalEval, intervalMul, Rat.cast_min, Rat.cast_max] using
      rectangle_product (ha B hB x hx) (hb B hB x hx)
  | neg a ha =>
    intro B hB x hx
    have h₁ := ha B hB x hx
    simpa [eval, intervalEval, intervalNeg] using
      (show -eval a x ∈ Icc (-((intervalEval a B).hi : ℝ)) (-((intervalEval a B).lo : ℝ)) from
        ⟨neg_le_neg h₁.2,neg_le_neg h₁.1⟩)

#print axioms from_children
end MetricDistortion.Contracts.Numerics_RationalIntervals
