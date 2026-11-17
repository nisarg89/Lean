import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Examples_TwoCandidateGap

private def opposite : Profile 2 2 := fun v =>
  if v = 0 then Equiv.swap 0 1 else Equiv.refl _

private def lineMetric (x y : ℝ) : Metric 2 2 :=
  PseudoMetricSpace.induced
    (Sum.elim (fun v : Fin 2 => if v = 0 then x else y)
      (fun c : Fin 2 => if c = 0 then (0 : ℝ) else 4)) inferInstance

private theorem line_distance (x y : ℝ) (v c : Fin 2) :
    distance (lineMetric x y) (.inl v) (.inr c) =
      |(if v = 0 then x else y) - (if c = 0 then 0 else 4)| := by
  change dist (if v = 0 then x else y) (if c = 0 then (0 : ℝ) else 4) = _
  rw [Real.dist_eq]

private theorem two_optimum (d : Metric 2 2) :
    optimum d = min (sc d 0) (sc d 1) := by
  change sInf (Set.range (sc d)) = min (sc d 0) (sc d 1)
  have hb : BddBelow (Set.range (sc d)) := (Set.finite_range (sc d)).bddBelow
  apply le_antisymm
  · exact le_min (csInf_le hb ⟨0,rfl⟩) (csInf_le hb ⟨1,rfl⟩)
  · apply le_csInf (show (Set.range (sc d)).Nonempty from ⟨sc d (0 : Fin 2),0,rfl⟩)
    rintro t ⟨c,rfl⟩
    fin_cases c
    · exact min_le_left _ _
    · exact min_le_right _ _

theorem from_children (h : Needs) : Statement := by
  have hpref0 : prefers (opposite 0) 0 1 := by norm_num [opposite,prefers]
  have hpref1 : prefers (opposite 1) 1 0 := by norm_num [opposite,prefers]
  let dA := lineMetric 0 2
  let dB := lineMetric 2 4
  have hconA : Consistent opposite dA := by
    intro v a b hab
    fin_cases v <;> fin_cases a <;> fin_cases b <;>
      norm_num [opposite,prefers] at hab
    all_goals norm_num [dA,line_distance]
  have hconB : Consistent opposite dB := by
    intro v a b hab
    fin_cases v <;> fin_cases a <;> fin_cases b <;>
      norm_num [opposite,prefers] at hab
    all_goals norm_num [dB,line_distance]
  have hA0 : sc dA 0 = 1 := by norm_num [sc,avg,Fin.sum_univ_two,dA,line_distance]
  have hA1 : sc dA 1 = 3 := by norm_num [sc,avg,Fin.sum_univ_two,dA,line_distance]
  have hB0 : sc dB 0 = 3 := by norm_num [sc,avg,Fin.sum_univ_two,dB,line_distance]
  have hB1 : sc dB 1 = 1 := by norm_num [sc,avg,Fin.sum_univ_two,dB,line_distance]
  refine ⟨opposite,hpref0,hpref1,⟨dA,dB,hconA,hconB,hA0,hA1,hB0,hB1⟩,?_⟩
  intro P
  have hp0 : 0 ≤ P.val 0 := P.property.1 0
  have hp1 : P.val 0 ≤ 1 := ((h.child_1 2 P).1 0).2
  have hP1 : P.val 1 = 1-P.val 0 := by
    have hh := P.property.2
    rw [Fin.sum_univ_two] at hh
    linarith
  have hmax1 : (1 : ℝ) ≤ max (3-2*P.val 0) (1+2*P.val 0) :=
    (by linarith : (1 : ℝ) ≤ 3-2*P.val 0).trans (le_max_left _ _)
  have hupper : distortion opposite P ≤
      ENNReal.ofReal (max (3-2*P.val 0) (1+2*P.val 0)) := by
    unfold distortion
    refine iSup_le fun d => ?_
    obtain ⟨hself,hsym,htri,hnonneg⟩ := h.child_0 2 2 d.val
    have hc0 : 0 ≤ sc d.val 0 := by
      unfold sc avg
      exact div_nonneg (Finset.sum_nonneg fun v _ => hnonneg _ _) (by norm_num)
    have hc1 : 0 ≤ sc d.val 1 := by
      unfold sc avg
      exact div_nonneg (Finset.sum_nonneg fun v _ => hnonneg _ _) (by norm_num)
    have h01 := d.property 0 0 1 hpref0
    have h10 := d.property 1 1 0 hpref1
    have h3A : sc d.val 1 ≤ 3*sc d.val 0 := by
      have ht0 := htri (.inl 0) (.inr 0) (.inr 1)
      have ht1 := htri (.inr 0) (.inl 1) (.inr 1)
      rw [hsym (.inr 0) (.inl 1)] at ht1
      have ha := hnonneg (.inl 0) (.inr 0)
      simp only [sc,avg,Fin.sum_univ_two] at ⊢
      linarith
    have h3B : sc d.val 0 ≤ 3*sc d.val 1 := by
      have ht1 := htri (.inl 1) (.inr 1) (.inr 0)
      have ht0 := htri (.inr 1) (.inl 0) (.inr 0)
      rw [hsym (.inr 1) (.inl 0)] at ht0
      have hb := hnonneg (.inl 1) (.inr 1)
      simp only [sc,avg,Fin.sum_univ_two] at ⊢
      linarith
    have hE : expectedCost d.val P =
        P.val 0*sc d.val 0+(1-P.val 0)*sc d.val 1 := by
      simp only [expectedCost,Fin.sum_univ_two,hP1]
    rw [two_optimum]
    by_cases hzero : sc d.val 0 = 0
    · have hzero1 : sc d.val 1 = 0 := by linarith
      rw [hE,hzero,hzero1]
      simp only [mul_zero,add_zero,min_self]
      rw [h.child_2.1]
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hmax1
    · have hc0pos : 0 < sc d.val 0 := lt_of_le_of_ne hc0 (Ne.symm hzero)
      have hc1pos : 0 < sc d.val 1 := by linarith
      rcases le_total (sc d.val 0) (sc d.val 1) with horder | horder
      · rw [min_eq_left horder]
        simp only [ratio,if_neg hzero]
        apply ENNReal.ofReal_le_ofReal
        apply (div_le_iff₀ hc0pos).2
        have hb := mul_le_mul_of_nonneg_left h3A (sub_nonneg.mpr hp1)
        have hsmall : expectedCost d.val P ≤ (3-2*P.val 0)*sc d.val 0 := by rw [hE]; nlinarith
        exact hsmall.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hc0)
      · rw [min_eq_right horder]
        simp only [ratio,if_neg (ne_of_gt hc1pos)]
        apply ENNReal.ofReal_le_ofReal
        apply (div_le_iff₀ hc1pos).2
        have ha := mul_le_mul_of_nonneg_left h3B hp0
        have hsmall : expectedCost d.val P ≤ (1+2*P.val 0)*sc d.val 1 := by rw [hE]; nlinarith
        exact hsmall.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hc1)
  have hEA : expectedCost dA P = 3-2*P.val 0 := by
    rw [expectedCost,Fin.sum_univ_two,hA0,hA1,hP1]
    ring
  have hEB : expectedCost dB P = 1+2*P.val 0 := by
    rw [expectedCost,Fin.sum_univ_two,hB0,hB1,hP1]
    ring
  have hOA : optimum dA = 1 := by rw [two_optimum,hA0,hA1]; norm_num
  have hOB : optimum dB = 1 := by rw [two_optimum,hB0,hB1]; norm_num
  have hlowA : ENNReal.ofReal (3-2*P.val 0) ≤ distortion opposite P := by
    have hh := le_iSup (fun d : {d : Metric 2 2 // Consistent opposite d} =>
      ratio (expectedCost d.val P) (optimum d.val)) ⟨dA,hconA⟩
    change ratio (expectedCost dA P) (optimum dA) ≤ distortion opposite P at hh
    simpa only [hEA,hOA,ratio,one_ne_zero,if_false,div_one] using hh
  have hlowB : ENNReal.ofReal (1+2*P.val 0) ≤ distortion opposite P := by
    have hh := le_iSup (fun d : {d : Metric 2 2 // Consistent opposite d} =>
      ratio (expectedCost d.val P) (optimum d.val)) ⟨dB,hconB⟩
    change ratio (expectedCost dB P) (optimum dB) ≤ distortion opposite P at hh
    simpa only [hEB,hOB,ratio,one_ne_zero,if_false,div_one] using hh
  apply le_antisymm hupper
  rcases le_total (3-2*P.val 0) (1+2*P.val 0) with hab | hba
  · rw [max_eq_right hab]
    exact hlowB
  · rw [max_eq_left hba]
    exact hlowA

#print axioms from_children
end MetricDistortion.Contracts.Examples_TwoCandidateGap
