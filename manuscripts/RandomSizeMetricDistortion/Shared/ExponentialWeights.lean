import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Shared_ExponentialWeights

/-- The finite-distribution form of Hoeffding's lemma used in the potential proof. -/
private theorem finite_hoeffding {m : ℕ} (p : Lottery m) (f : Fin m → ℝ)
    (hf : ∀ c, f c ∈ Icc (0 : ℝ) 1) (η : ℝ) :
    (∑ c, p.val c * Real.exp (η*f c)) ≤
      Real.exp (η*(∑ c, p.val c*f c)+η^2/8) := by
  let q : PMF (Fin m) := PMF.ofFintype (fun c => ENNReal.ofReal (p.val c)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => p.property.1 c), p.property.2]
    simp)
  have hmean : ∫ c, f c ∂q.toMeasure = ∑ c, p.val c*f c := by
    rw [PMF.integral_eq_sum]
    simp [q, ENNReal.toReal_ofReal (p.property.1 _), smul_eq_mul]
  have hmgf := (ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
    (μ := q.toMeasure) (a := (0 : ℝ)) (b := 1)
    (X := f) (measurable_of_finite f).aemeasurable (Filter.Eventually.of_forall hf)).mgf_le η
  rw [ProbabilityTheory.mgf, PMF.integral_eq_sum, hmean] at hmgf
  simp only [q, PMF.ofFintype_apply, ENNReal.toReal_ofReal (p.property.1 _),
    smul_eq_mul] at hmgf
  norm_num at hmgf
  have hmgf' : (∑ c, p.val c*Real.exp (η*(f c-∑ b, p.val b*f b))) ≤ Real.exp (η^2/8) := by
    convert hmgf using 1 <;> congr 1 <;> ring
  calc
    (∑ c, p.val c*Real.exp (η*f c)) =
        (∑ c, p.val c*Real.exp (η*(f c-∑ b, p.val b*f b))) *
          Real.exp (η*(∑ b, p.val b*f b)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (η^2/8)*Real.exp (η*(∑ b, p.val b*f b)) :=
      mul_le_mul_of_nonneg_right hmgf' (Real.exp_nonneg _)
    _ = Real.exp (η*(∑ b, p.val b*f b)+η^2/8) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem proved : Statement := by
  intro m hm g hg η hη N hN c
  let W (t : ℕ) : ℝ := ∑ b, mwWeight g η t b
  have hW (t : ℕ) : 0 < W t := by
    exact Finset.sum_pos' (fun b _ => (Real.exp_pos _).le)
      ⟨⟨0,hm⟩, Finset.mem_univ _, Real.exp_pos _⟩
  let p (t : ℕ) : Lottery m := ⟨mwProbability g η t, by
    refine ⟨fun b => div_nonneg (Real.exp_nonneg _) (hW t).le, ?_⟩
    change (∑ b, mwWeight g η t b / W t) = 1
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (hW t))⟩
  let reward (t : ℕ) : ℝ := ∑ b, mwProbability g η t b*g t b
  have hweight (t : ℕ) (b : Fin m) :
      mwWeight g η (t+1) b = mwWeight g η t b*Real.exp (η*g t b) := by
    simp only [mwWeight, Finset.sum_range_succ, mul_add, Real.exp_add]
  have hnext (t : ℕ) : W (t+1) = W t*(∑ b, (p t).val b*Real.exp (η*g t b)) := by
    dsimp only [W]
    simp_rw [hweight]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    change mwWeight g η t b * Real.exp (η*g t b) =
      W t*(mwWeight g η t b/W t*Real.exp (η*g t b))
    field_simp [ne_of_gt (hW t)]
  have hlognext (t : ℕ) : Real.log (W (t+1)) ≤ Real.log (W t)+η*reward t+η^2/8 := by
    have hs := finite_hoeffding (p t) (g t) (hg t) η
    have he : W (t+1) ≤ W t*Real.exp (η*reward t+η^2/8) := by
      rw [hnext]
      exact mul_le_mul_of_nonneg_left hs (hW t).le
    have hl := Real.log_le_log (hW (t+1)) he
    rw [Real.log_mul (ne_of_gt (hW t)) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at hl
    linarith
  have hpotential (t : ℕ) : Real.log (W t) ≤
      Real.log m+η*(∑ s ∈ Finset.range t, reward s)+(t : ℝ)*η^2/8 := by
    induction t with
    | zero => simp [W,mwWeight]
    | succ t ih =>
      rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
      linarith [hlognext t]
  have hlower : η*(∑ t ∈ Finset.range N, g t c) ≤ Real.log (W N) := by
    have hs : mwWeight g η N c ≤ W N :=
      Finset.single_le_sum (f := mwWeight g η N) (fun b _ => Real.exp_nonneg _) (Finset.mem_univ c)
    have hl := Real.log_le_log (Real.exp_pos _) hs
    simpa only [mwWeight, Real.log_exp] using hl
  have hcombined := le_trans hlower (hpotential N)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  apply (div_le_iff₀ hNr).mpr
  have heq : ((∑ t ∈ Finset.range N, reward t)/(N : ℝ)+
      Real.log m/(η*N)+η/8)*(N : ℝ) =
      (∑ t ∈ Finset.range N, reward t)+Real.log m/η+(N : ℝ)*η/8 := by
    field_simp [ne_of_gt hη, ne_of_gt hNr]
  change (∑ t ∈ Finset.range N, g t c) ≤
    ((∑ t ∈ Finset.range N, reward t)/(N : ℝ)+Real.log m/(η*N)+η/8)*(N : ℝ)
  rw [heq]
  apply (mul_le_mul_iff_right₀ hη).mp
  have hcancel : (Real.log m/η)*η = Real.log m := div_mul_cancel₀ _ (ne_of_gt hη)
  nlinarith

#print axioms proved
end MetricDistortion.Contracts.Shared_ExponentialWeights
