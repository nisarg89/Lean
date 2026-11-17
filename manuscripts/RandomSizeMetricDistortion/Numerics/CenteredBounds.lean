import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Numerics_CenteredBounds

private theorem update_in_box {B : Box} {y : Fin 4 → ℝ} (hy : inBox B y)
    (i : Fin 4) (t : ℝ) (ht : t ∈ Icc ((B i).lo : ℝ) ((B i).hi : ℝ)) :
    inBox B (Function.update y i t) := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa using ht
  · simpa [Function.update_of_ne hji] using hy j

theorem from_children (h : Needs) : Statement := by
  intro e B hB x hx
  let c : Fin 4 → ℝ := fun i => (((B i).lo+(B i).hi)/2 : ℚ)
  let r : Fin 4 → ℝ := fun i => (((B i).hi : ℝ)-(B i).lo)/2
  let C : Fin 4 → ℝ := fun i =>
    max |((intervalEval (derivative i e) B).lo : ℝ)| |((intervalEval (derivative i e) B).hi : ℝ)|
  have hc : inBox B c := by
    intro i
    have hle : ((B i).lo : ℝ) ≤ (B i).hi := by exact_mod_cast hB i
    dsimp [c]
    push_cast
    constructor <;> linarith
  have hC : ∀ i, 0 ≤ C i := by
    intro i
    exact (abs_nonneg _).trans (le_max_left _ _)
  have step_bound : ∀ y : Fin 4 → ℝ, inBox B y → ∀ i : Fin 4, y i = c i →
      eval e (Function.update y i (x i)) ≤ eval e y+C i*r i := by
    intro y hy i hmid
    let f : ℝ → ℝ := fun t => eval e (Function.update y i t)
    let g : ℝ → ℝ := fun t => eval (derivative i e) (Function.update y i t)
    have hd : ∀ t, HasDerivAt f (g t) t := by
      intro t
      simpa only [Function.update_self,Function.update_idem] using
        h.child_1 e i (Function.update y i t)
    have hg : ∀ t ∈ Icc ((B i).lo : ℝ) ((B i).hi : ℝ), ‖g t‖ ≤ C i := by
      intro t ht
      have ht' := h.child_0 (derivative i e) B hB _ (update_in_box hy i t ht)
      rw [Real.norm_eq_abs,abs_le]
      constructor
      · exact (neg_le_neg (le_max_left _ _)).trans ((neg_abs_le _).trans ht'.1)
      · exact ht'.2.trans ((le_abs_self _).trans (le_max_right _ _))
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ => (hd t).hasDerivWithinAt) hg
        (convex_Icc ((B i).lo : ℝ) ((B i).hi : ℝ)) (hc i) (hx i)
    have hdist : ‖x i-c i‖ ≤ r i := by
      rw [Real.norm_eq_abs,abs_le]
      dsimp [c,r]
      push_cast
      constructor <;> linarith [(hx i).1,(hx i).2]
    have hnorm : f (x i)-f (c i) ≤ C i*‖x i-c i‖ :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hmvt)
    have hdiff : f (x i)-f (c i) ≤ C i*r i :=
      hnorm.trans (mul_le_mul_of_nonneg_left hdist (hC i))
    have hbase : f (c i) = eval e y := by
      dsimp [f]
      rw [← hmid,Function.update_eq_self]
    have hfinal : f (x i) ≤ f (c i)+C i*r i := by linarith
    rw [hbase] at hfinal
    exact hfinal
  let y1 := Function.update c (0 : Fin 4) (x 0)
  let y2 := Function.update y1 (1 : Fin 4) (x 1)
  let y3 := Function.update y2 (2 : Fin 4) (x 2)
  let y4 := Function.update y3 (3 : Fin 4) (x 3)
  have hy1 : inBox B y1 := update_in_box hc 0 (x 0) (hx 0)
  have hy2 : inBox B y2 := update_in_box hy1 1 (x 1) (hx 1)
  have hy3 : inBox B y3 := update_in_box hy2 2 (x 2) (hx 2)
  have h0 : eval e y1 ≤ eval e c+C 0*r 0 := step_bound c hc 0 rfl
  have h1 : eval e y2 ≤ eval e y1+C 1*r 1 := by
    apply step_bound y1 hy1 1
    simp [y1]
  have h2 : eval e y3 ≤ eval e y2+C 2*r 2 := by
    apply step_bound y2 hy2 2
    simp [y2,y1]
  have h3 : eval e y4 ≤ eval e y3+C 3*r 3 := by
    apply step_bound y3 hy3 3
    simp [y3,y2,y1]
  have hy4 : y4 = x := by
    ext i
    fin_cases i <;> simp [y4,y3,y2,y1]
  have hsum : (centeredBound e B : ℝ) = eval e c+
      (C 0*r 0+C 1*r 1+C 2*r 2+C 3*r 3) := by
    unfold centeredBound
    rw [Rat.cast_add]
    have hq : (qEval e (fun i => ((B i).lo+(B i).hi)/2) : ℝ) = eval e c := by
      simpa [c] using (h.child_2 e (fun i => ((B i).lo+(B i).hi)/2)).symm
    rw [hq]
    simp [Fin.sum_univ_succ,C,r,Rat.cast_max,Rat.cast_abs] <;> ring
  rw [hsum]
  rw [hy4] at h3
  linarith

#print axioms from_children
end MetricDistortion.Contracts.Numerics_CenteredBounds
