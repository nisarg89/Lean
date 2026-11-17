import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Lower_AveragedPowerGap

private theorem phi_integral_series (hmix : Analysis_IntegralMixture.Statement)
    (D : DrawLaw) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Phi D t = ∑' k, drawWeight D k*t^(k+2)/(k+2 : ℕ) := by
  have hm := hmix D 0 t (by norm_num) ht.1 (by simpa using ht.2)
  simp only [zero_add] at hm
  have hs : Phi D t = t*(∫ s in (0 : ℝ)..1, phi D (s*t)) := by
    simpa [Phi,smul_eq_mul] using
      (intervalIntegral.smul_integral_comp_mul_right (phi D) t (a := (0 : ℝ)) (b := 1)).symm
  have hpoly (k : ℕ) : (∫ s in (0 : ℝ)..1, (s*t)^(k+1)) = t^(k+1)/(k+2 : ℕ) := by
    simp_rw [mul_pow,intervalIntegral.integral_mul_const]
    rw [integral_pow]
    simp only [one_pow,zero_pow (by omega : k+1+1 ≠ 0),sub_zero,one_div]
    push_cast
    ring
  rw [hs,hm,← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [hpoly]
  simp only [pow_succ]
  push_cast
  ring

theorem from_children (h : Needs) : Statement := by
  intro D
  obtain ⟨hw,hsw⟩ := h.child_2 D
  have hsum : Summable (drawWeight D) := hsw.summable
  have hpow (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (s : ℕ) :
      Summable (fun k => drawWeight D k*t^(k+s)) := by
    apply Summable.of_nonneg_of_le (fun k => mul_nonneg (hw k) (pow_nonneg ht.1 _))
      (fun k => ?_) hsum
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ ht.1 ht.2) (hw k)).trans_eq (mul_one _)
  have hint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Summable (fun k => drawWeight D k*t^(k+2)/(k+2 : ℕ)) := by
    apply Summable.of_nonneg_of_le (fun k =>
      div_nonneg (mul_nonneg (hw k) (pow_nonneg ht.1 _)) (Nat.cast_nonneg _)) (fun k => ?_) hsum
    have hden : (1 : ℝ) ≤ (k+2 : ℕ) := by exact_mod_cast (by omega : 1 ≤ k+2)
    calc
      drawWeight D k*t^(k+2)/(k+2 : ℕ) ≤ drawWeight D k*t^(k+2) :=
        div_le_self (mul_nonneg (hw k) (pow_nonneg ht.1 _)) hden
      _ ≤ drawWeight D k :=
        (mul_le_mul_of_nonneg_left (pow_le_one₀ ht.1 ht.2) (hw k)).trans_eq (mul_one _)
  let L : ℕ → ℝ := fun k => drawWeight D k*(7/26 : ℝ)^(k+2)/(k+2 : ℕ) +
    (71/125-7/26)*(drawWeight D k*(71/125 : ℝ)^(k+1))
  let R : ℕ → ℝ := fun k => drawWeight D k*(1/52 : ℝ)^(k+2)/(k+2 : ℕ) +
    ((71/125-1/52)/(3/4))*(drawWeight D k*(3/4 : ℝ)^(k+2)/(k+2 : ℕ))
  have hLb := hint (7/26) ⟨by norm_num,by norm_num⟩
  have hLc := (hpow (71/125) ⟨by norm_num,by norm_num⟩ 1).mul_left (71/125-7/26)
  have hRa := hint (1/52) ⟨by norm_num,by norm_num⟩
  have hRp := (hint (3/4) ⟨by norm_num,by norm_num⟩).mul_left ((71/125-1/52)/(3/4))
  have hLs : Summable L := hLb.add hLc
  have hRs : Summable R := hRa.add hRp
  have hdiff (k : ℕ) : R k-L k = drawWeight D k*lowerGap (k+1)/(k+2 : ℕ) := by
    dsimp [R,L,lowerGap]
    simp only [pow_succ]
    push_cast
    field_simp
    <;> ring
  have hle : ∀ k, L k ≤ R k := by
    intro k
    have hg := h.child_0.1 (k+1) (by omega)
    have hp : 0 ≤ R k-L k := by
      rw [hdiff]
      exact div_nonneg (mul_nonneg (hw k) hg.le) (by positivity)
    linarith
  have hex : ∃ k, 0 < drawWeight D k := by
    by_contra hnone
    push_neg at hnone
    have hz : ∀ k, drawWeight D k = 0 := fun k => le_antisymm (hnone k) (hw k)
    have he := hsw.tsum_eq
    simp [hz] at he
  obtain ⟨j,hj⟩ := hex
  have hstrict : L j < R j := by
    have hg := h.child_0.1 (j+1) (by omega)
    have hp : 0 < R j-L j := by
      rw [hdiff]
      exact div_pos (mul_pos hj hg) (by positivity)
    linarith
  have hslt : (∑' k, L k) < ∑' k, R k := hLs.tsum_lt_tsum hle hstrict hRs
  rw [phi_integral_series h.child_1 D (7/26) ⟨by norm_num,by norm_num⟩,
    phi_integral_series h.child_1 D (1/52) ⟨by norm_num,by norm_num⟩,
    phi_integral_series h.child_1 D (3/4) ⟨by norm_num,by norm_num⟩]
  change _ < _
  simpa only [L,R,hLb.tsum_add hLc,hRa.tsum_add hRp,tsum_mul_left,phi] using hslt

#print axioms from_children
end MetricDistortion.Contracts.Lower_AveragedPowerGap
