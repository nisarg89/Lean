import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Numerics_StarLaw

private theorem star_antiderivative (x : ℝ) : HasDerivAt PhiStar (phiStar x) x := by
  have hd := (((hasDerivAt_pow 2 x).const_mul (19/146 : ℝ)).add
    ((hasDerivAt_pow 3 x).const_mul (35/438 : ℝ))).add
      ((hasDerivAt_pow 33 x).div_const 66)
  norm_num only [Nat.cast_ofNat] at hd
  have hcoef : (19/146 : ℝ)*(2*x^(2-1))+(35/438 : ℝ)*(3*x^(3-1))+
      (33*x^(33-1))/66 = phiStar x := by
    norm_num [phiStar] <;> ring
  rw [hcoef] at hd
  rw [hasDerivAt_iff_isLittleO] at hd ⊢
  simpa only [PhiStar,Pi.add_apply,smul_eq_mul] using hd

theorem from_children (h : Needs) : Statement := by
  constructor
  · let f : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (if k = 0 then (19/73 : ℝ) else
      if k = 1 then (35/146 : ℝ) else if k = 31 then (1/2 : ℝ) else 0)
    have hsum : ∑ k ∈ ({0,1,31} : Finset ℕ), f k = 1 := by
      norm_num [f,Finset.sum_insert]
      rw [← ENNReal.ofReal_add (by norm_num : 0 ≤ (35/146 : ℝ)) (by norm_num : 0 ≤ (1/2 : ℝ))]
      rw [← ENNReal.ofReal_add (by norm_num : 0 ≤ (19/73 : ℝ)) (by norm_num : 0 ≤ (35/146 : ℝ)+(1/2 : ℝ))]
      norm_num
    have hout : ∀ k ∉ ({0,1,31} : Finset ℕ), f k = 0 := by
      intro k hk
      have hk' : k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 31 := by simpa using hk
      simp [f,hk'.1,hk'.2.1,hk'.2.2]
    refine ⟨PMF.ofFinset f {0,1,31} hsum hout, ?_⟩
    intro k
    rfl
  · intro D hD
    change ∀ k, D k = ENNReal.ofReal (if k = 0 then (19/73 : ℝ) else
      if k = 1 then (35/146 : ℝ) else if k = 31 then (1/2 : ℝ) else 0) at hD
    have hz : ∀ k ∉ ({0,1,31} : Finset ℕ), drawWeight D k = 0 := by
      intro k hk
      have hk' : k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 31 := by simpa using hk
      simp [drawWeight,hD k,hk'.1,hk'.2.1,hk'.2.2]
    have hφ : ∀ u, phi D u = phiStar u := by
      intro u
      unfold phi
      rw [tsum_eq_sum (s := ({0,1,31} : Finset ℕ)) (fun k hk => by rw [hz k hk,zero_mul])]
      norm_num [drawWeight,hD,phiStar,Finset.sum_insert]
      ring
    refine ⟨hφ, ?_, ?_, ?_⟩
    · intro u
      unfold Phi
      simp_rw [hφ]
      have hint : IntervalIntegrable phiStar volume 0 u :=
        (by unfold phiStar; fun_prop : Continuous phiStar).intervalIntegrable 0 u
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => star_antiderivative x) hint]
      simp [PhiStar]
    · unfold mu
      rw [tsum_eq_sum (s := ({0,1,31} : Finset ℕ)) (fun k hk => by rw [hz k hk,zero_div])]
      norm_num [drawWeight,hD,muStar,Finset.sum_insert]
    · norm_num [cStar]

#print axioms from_children
end MetricDistortion.Contracts.Numerics_StarLaw
