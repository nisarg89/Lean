import Voting.Stable.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Comparison_ScoreRegularity

theorem from_children (h : Needs) : Statement := by
  intro m D r c
  let arg : (Fin m → ℝ) → ℝ → ℝ := fun p s =>
    (∑ j, if prefers r c j then p j else 0)+s*p c
  have harg : ∀ p ∈ simplex m, ∀ s ∈ Icc (0 : ℝ) 1, arg p s ∈ Icc (0 : ℝ) 1 := by
    intro p hp s hs
    have hb : 0 ≤ ∑ j, if prefers r c j then p j else 0 := by
      apply Finset.sum_nonneg
      intro j _
      split_ifs
      · exact hp.1 j
      · exact le_rfl
    have ht : (∑ j, if prefers r c j then p j else 0)+p c ≤ 1 := by
      calc
        _ = ∑ j, ((if prefers r c j then p j else 0)+(if j=c then p j else 0)) := by
          simp [Finset.sum_add_distrib]
        _ ≤ ∑ j, p j := by
          apply Finset.sum_le_sum
          intro j _
          by_cases hj : j=c
          · subst j
            simp [prefers]
          · simp only [hj,ite_false,add_zero]
            split_ifs <;> simp_all [hp.1 j]
        _ = 1 := hp.2
    dsimp [arg]
    constructor
    · exact add_nonneg hb (mul_nonneg hs.1 (hp.1 c))
    · linarith [mul_le_mul_of_nonneg_right hs.2 (hp.1 c)]
  have hphi := h.child_0 D
  have hphiCont : ContinuousOn (phi D) (Icc (0 : ℝ) 1) := hphi.2.2.1
  have hphiConv : ConvexOn ℝ (Icc (0 : ℝ) 1) (phi D) := hphi.2.1
  have hbound : ∀ p ∈ simplex m, ∀ s ∈ Icc (0 : ℝ) 1, phi D (arg p s) ∈ Icc (0 : ℝ) 1 := by
    intro p hp s hs
    have ha := harg p hp s hs
    constructor
    · rw [← hphi.2.2.2.1]
      exact hphi.1 (by constructor <;> norm_num) ha ha.1
    · rw [← hphi.2.2.2.2.1]
      exact hphi.1 ha (by constructor <;> norm_num) ha.2
  have hiCont : ∀ p ∈ simplex m,
      ContinuousOn (fun s => phi D (arg p s)) (Icc (0 : ℝ) 1) := by
    intro p hp
    exact hphiCont.comp (by dsimp [arg]; fun_prop) (harg p hp)
  have hi : ∀ p ∈ simplex m,
      IntervalIntegrable (fun s => phi D (arg p s)) volume 0 1 := by
    intro p hp
    exact (hiCont p hp).intervalIntegrable_of_Icc zero_le_one
  have hc : Convex ℝ (simplex m) := by
    intro p hp q hq a b ha hb hab
    constructor
    · intro j
      exact add_nonneg (mul_nonneg ha (hp.1 j)) (mul_nonneg hb (hq.1 j))
    · simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,
        ← Finset.mul_sum,hp.2,hq.2,mul_one,hab]
  have hparamCont (s : ℝ) : Continuous (fun p : Fin m → ℝ => arg p s) := by
    dsimp [arg]
    apply Continuous.add
    · apply continuous_finsetSum
      intro j _
      by_cases hj : prefers r c j <;> simp only [hj,ite_true,ite_false] <;> fun_prop
    · fun_prop
  have hlinear : ∀ p q : Fin m → ℝ, ∀ a b s : ℝ,
      arg (a • p+b • q) s = a*arg p s+b*arg q s := by
    intro p q a b s
    dsimp [arg]
    calc
      _ = (∑ j, (a*(if prefers r c j then p j else 0)+b*(if prefers r c j then q j else 0)))+
          s*(a*p c+b*q c) := by
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> ring
      _ = _ := by
        rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
        ring
  constructor
  · intro p hp
    change ContinuousWithinAt (fun p => ∫ s in (0 : ℝ)..1, phi D (arg p s)) (simplex m) p
    apply intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ => 1)
    · filter_upwards [self_mem_nhdsWithin] with q hq
      simpa only [uIoc_of_le zero_le_one] using
        ((hiCont q hq).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [self_mem_nhdsWithin] with q hq
      filter_upwards [] with s hs
      have hsm : s ∈ Icc (0 : ℝ) 1 := by
        simpa only [uIcc_of_le zero_le_one] using (uIoc_subset_uIcc hs)
      have hb := hbound q hq s hsm
      simpa only [Real.norm_eq_abs,abs_of_nonneg hb.1] using hb.2
    · exact intervalIntegrable_const
    · filter_upwards [] with s hs
      have hsm : s ∈ Icc (0 : ℝ) 1 := by
        simpa only [uIcc_of_le zero_le_one] using (uIoc_subset_uIcc hs)
      exact (hphiCont.comp (hparamCont s).continuousOn (fun q hq => harg q hq s hsm)).continuousWithinAt hp
  · refine ⟨hc, ?_⟩
    intro p hp q hq a b ha hb hab
    change (∫ s in (0 : ℝ)..1, phi D (arg (a • p+b • q) s)) ≤
      a • (∫ s in (0 : ℝ)..1, phi D (arg p s))+b • (∫ s in (0 : ℝ)..1, phi D (arg q s))
    calc
      _ ≤ ∫ s in (0 : ℝ)..1, (a*phi D (arg p s)+b*phi D (arg q s)) := by
        apply intervalIntegral.integral_mono_on zero_le_one (hi _ (hc hp hq ha hb hab))
          (((hi p hp).const_mul a).add ((hi q hq).const_mul b))
        intro s hs
        rw [hlinear]
        exact hphiConv.2 (harg p hp s hs) (harg q hq s hs) ha hb hab
      _ = _ := by
        rw [intervalIntegral.integral_add ((hi p hp).const_mul a) ((hi q hq).const_mul b),
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
        rfl

#print axioms from_children
end MetricDistortion.Contracts.Comparison_ScoreRegularity
