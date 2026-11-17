import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Numerics_TreeSoundness

private theorem valid_face {B : Box} (hB : ValidBox B) (i : Fin 4) (upper : Bool) :
    ValidBox (faceBox B i upper) := by
  intro j
  by_cases hji : j = i
  · subst j
    simp [faceBox]
  · simpa [faceBox,Function.update_of_ne hji] using hB j

private theorem valid_split {B : Box} (hB : ValidBox B) (i : Fin 4) (q : ℚ)
    (hq : (B i).lo ≤ q ∧ q ≤ (B i).hi) (right : Bool) :
    ValidBox (splitBox B i q right) := by
  intro j
  by_cases hji : j = i
  · subst j
    cases right
    · simpa [splitBox] using hq.1
    · simpa [splitBox] using hq.2
  · simpa [splitBox,Function.update_of_ne hji] using hB j

theorem from_children (h : Needs) : Statement := by
  intro e B tree
  induction tree generalizing B with
  | direct =>
    intro hB hok x hx
    have hb : (intervalEval e B).hi ≤ 0 := of_decide_eq_true hok
    exact (h.child_0 e B hB x hx).2.trans (by exact_mod_cast hb)
  | centered =>
    intro hB hok x hx
    have hb : centeredBound e B ≤ 0 := of_decide_eq_true hok
    exact (h.child_1 e B hB x hx).trans (by exact_mod_cast hb)
  | face i upper child ih =>
    intro hB hok x hx
    have hh : (if upper then decide (0 ≤ (intervalEval (derivative i e) B).lo)
        else decide ((intervalEval (derivative i e) B).hi ≤ 0)) = true ∧
        verifyTree e (faceBox B i upper) child = true := by
      simpa only [verifyTree,Bool.and_eq_true_iff] using hok
    apply h.child_2 e B i upper hB
    · cases upper <;> simpa using (of_decide_eq_true hh.1)
    · exact ih (faceBox B i upper) (valid_face hB i upper) hh.2
    · exact hx
  | split i q left right ihl ihr =>
    intro hB hok x hx
    have hh : ((B i).lo ≤ q ∧ q ≤ (B i).hi) ∧
        verifyTree e (splitBox B i q false) left = true ∧
        verifyTree e (splitBox B i q true) right = true := by
      simpa only [verifyTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq] using hok
    have hq := hh.1
    by_cases hxq : x i ≤ (q : ℝ)
    · apply ihl (splitBox B i q false) (valid_split hB i q hq false) hh.2.1 x
      intro j
      by_cases hji : j = i
      · subst j
        simpa [splitBox,inBox] using (show x i ∈ Icc ((B i).lo : ℝ) (q : ℝ) from ⟨(hx i).1,hxq⟩)
      · simpa [splitBox,Function.update_of_ne hji] using hx j
    · apply ihr (splitBox B i q true) (valid_split hB i q hq true) hh.2.2 x
      intro j
      by_cases hji : j = i
      · subst j
        simpa [splitBox,inBox] using (show x i ∈ Icc (q : ℝ) ((B i).hi : ℝ) from ⟨(le_of_not_ge hxq),(hx i).2⟩)
      · simpa [splitBox,Function.update_of_ne hji] using hx j

#print axioms from_children
end MetricDistortion.Contracts.Numerics_TreeSoundness
