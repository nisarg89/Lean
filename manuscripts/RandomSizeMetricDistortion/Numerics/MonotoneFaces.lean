import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Numerics_MonotoneFaces

private theorem slice_derivative (hd : Numerics_DerivativeBounds.Statement)
    (e : PolyExpr) (i : Fin 4) (x : Fin 4 → ℝ) (t : ℝ) :
    HasDerivAt (fun u => eval e (Function.update x i u))
      (eval (derivative i e) (Function.update x i t)) t := by
  simpa only [Function.update_self,Function.update_idem] using hd e i (Function.update x i t)

private theorem slice_in_box {B : Box} {x : Fin 4 → ℝ} (hx : inBox B x)
    (i : Fin 4) (t : ℝ) (ht : t ∈ Icc ((B i).lo : ℝ) ((B i).hi : ℝ)) :
    inBox B (Function.update x i t) := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa using ht
  · simpa [Function.update_of_ne hji] using hx j

theorem from_children (h : Needs) : Statement := by
  intro e B i upper hB hsign hface x hx
  let L : ℝ := (B i).lo
  let U : ℝ := (B i).hi
  let f : ℝ → ℝ := fun t => eval e (Function.update x i t)
  let g : ℝ → ℝ := fun t => eval (derivative i e) (Function.update x i t)
  have hd : ∀ t, HasDerivAt f (g t) t := fun t => slice_derivative h.child_1 e i x t
  have hcont : ContinuousOn f (Icc L U) :=
    (continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt).continuousOn
  have hdiff : DifferentiableOn ℝ f (interior (Icc L U)) :=
    fun t _ => (hd t).differentiableAt.differentiableWithinAt
  have hLU : L ≤ U := by
    change ((B i).lo : ℝ) ≤ ((B i).hi : ℝ)
    exact_mod_cast hB i
  have hgrad : ∀ t ∈ Icc L U,
      g t ∈ Icc ((intervalEval (derivative i e) B).lo : ℝ)
        ((intervalEval (derivative i e) B).hi : ℝ) := by
    intro t ht
    exact h.child_0 (derivative i e) B hB _ (slice_in_box hx i t ht)
  have hxi : x i ∈ Icc L U := hx i
  cases upper
  · have hs : ((intervalEval (derivative i e) B).hi : ℝ) ≤ 0 := by exact_mod_cast hsign
    have hanti : AntitoneOn f (Icc L U) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc L U) hcont hdiff
      intro t ht
      rw [(hd t).deriv]
      exact (hgrad t (interior_subset ht)).2.trans hs
    have hle : f (x i) ≤ f L := hanti ⟨le_rfl,hLU⟩ hxi hxi.1
    have hb : eval e (Function.update x i L) ≤ 0 := by
      apply hface
      intro j
      by_cases hji : j = i
      · subst j
        simp [faceBox,L]
      · simpa [faceBox,Function.update_of_ne hji] using hx j
    simpa [f,Function.update_eq_self] using hle.trans hb
  · have hs : 0 ≤ ((intervalEval (derivative i e) B).lo : ℝ) := by exact_mod_cast hsign
    have hmono : MonotoneOn f (Icc L U) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc L U) hcont hdiff
      intro t ht
      rw [(hd t).deriv]
      exact hs.trans (hgrad t (interior_subset ht)).1
    have hle : f (x i) ≤ f U := hmono hxi ⟨hLU,le_rfl⟩ hxi.2
    have hb : eval e (Function.update x i U) ≤ 0 := by
      apply hface
      intro j
      by_cases hji : j = i
      · subst j
        simp [faceBox,U]
      · simpa [faceBox,Function.update_of_ne hji] using hx j
    simpa [f,Function.update_eq_self] using hle.trans hb

#print axioms from_children
end MetricDistortion.Contracts.Numerics_MonotoneFaces
