import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Comparison_ScoreBounds

theorem from_children (h : Needs) : Statement := by
  intro n m hn hm D σ P
  have hw := (h.child_2 D).1
  have hws := (h.child_2 D).2
  have hp := h.child_1 D
  have hphiCont : ContinuousOn (phi D) (Icc (0 : ℝ) 1) := hp.2.2.1
  have hphiBound : ∀ u ∈ Icc (0 : ℝ) 1, phi D u ∈ Icc (0 : ℝ) 1 := by
    intro u hu
    constructor
    · rw [← hp.2.2.2.1]
      exact hp.1 (by constructor <;> norm_num) hu hu.1
    · rw [← hp.2.2.2.2.1]
      exact hp.1 hu (by constructor <;> norm_num) hu.2
  have hcompare : ∀ v c, compare D (σ v) P c ∈ Icc (0 : ℝ) 1 := by
    intro v c
    have hb : 0 ≤ below (σ v) P c := by
      unfold below mass
      apply Finset.sum_nonneg
      intro j _
      split_ifs
      · exact P.property.1 j
      · exact le_rfl
    have htotal : below (σ v) P c+P.val c ≤ 1 := by
      calc
        _ = ∑ j, ((if prefers (σ v) c j then P.val j else 0)+(if j=c then P.val j else 0)) := by
          simp [below,mass,Finset.sum_add_distrib]
        _ ≤ ∑ j, P.val j := by
          apply Finset.sum_le_sum
          intro j _
          by_cases hj : j=c
          · subst j
            simp [prefers]
          · simp only [hj,ite_false,add_zero]
            split_ifs <;> simp_all [P.property.1 j]
        _ = 1 := P.property.2
    have harg : ∀ s ∈ Icc (0 : ℝ) 1, below (σ v) P c+s*P.val c ∈ Icc (0 : ℝ) 1 := by
      intro s hs
      constructor
      · exact add_nonneg hb (mul_nonneg hs.1 (P.property.1 c))
      · linarith [mul_le_mul_of_nonneg_right hs.2 (P.property.1 c)]
    have hi : IntervalIntegrable (fun s => phi D (below (σ v) P c+s*P.val c)) volume 0 1 :=
      (hphiCont.comp (by fun_prop) harg).intervalIntegrable_of_Icc zero_le_one
    rw [(h.child_0 m D (σ v) P c).1]
    unfold ambientCompare
    constructor
    · have H := intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const hi
        (fun s hs => (hphiBound _ (harg s hs)).1)
      simpa [below,mass] using H
    · have H := intervalIntegral.integral_mono_on zero_le_one hi intervalIntegrable_const
        (fun s hs => (hphiBound _ (harg s hs)).2)
      simpa [below,mass] using H
  have hmuNonneg : ∀ k : ℕ, 0 ≤ drawWeight D k/(k+2 : ℕ) := fun k => div_nonneg (hw k) (by positivity)
  have hmuSummable : Summable (fun k => drawWeight D k/(k+2 : ℕ)) := by
    apply Summable.of_nonneg_of_le hmuNonneg _ hws.summable
    intro k
    apply div_le_self (hw k)
    exact_mod_cast (show 1 ≤ k+2 by omega)
  have hhalf : HasSum (fun k => drawWeight D k/2) (1/2 : ℝ) := hws.div_const 2
  have hmuUpper : mu D ≤ (1/2 : ℝ) := by
    calc
      mu D ≤ ∑' k, drawWeight D k/2 := by
        apply Summable.tsum_le_tsum _ hmuSummable hhalf.summable
        intro k
        have hden : (2 : ℝ) ≤ ((k+2 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ k+2 by omega)
        exact div_le_div_of_nonneg_left (hw k) (by norm_num : (0 : ℝ) < 2) hden
      _ = 1/2 := hhalf.tsum_eq
  have hpositive : ∃ k, 0 < drawWeight D k := by
    by_contra! H
    have hz : drawWeight D = fun _ => 0 := funext fun k => le_antisymm (H k) (hw k)
    have hsum : (∑' k, drawWeight D k) = 0 := by simp [hz]
    rw [hws.tsum_eq] at hsum
    norm_num at hsum
  obtain ⟨k,hk⟩ := hpositive
  have hmuPositive : 0 < mu D := hmuSummable.tsum_pos hmuNonneg k (div_pos hk (by positivity))
  refine ⟨?_,hmuPositive,hmuUpper⟩
  intro c
  change (∑ v, compare D (σ v) P c)/(n : ℝ) ∈ Icc (0 : ℝ) 1
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun v _ => (hcompare v c).1) (Nat.cast_nonneg n)
  · apply (div_le_one (by exact_mod_cast hn : (0 : ℝ) < n)).2
    simpa using (Finset.sum_le_sum (s := Finset.univ) fun v _ => (hcompare v c).2)

#print axioms from_children
end MetricDistortion.Contracts.Comparison_ScoreBounds
