import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Computation_MWGuarantee

theorem from_children (h : Needs) : Statement := by
  intro n m hn hm D σ δ P hδ hP Q hQ
  have hm0 : 0 < m := by omega
  let N : ℕ := Nat.ceil (Real.log m/(2*δ^2))
  have hi := h.child_2 m hm δ hδ
  have hN : 0 < N := hi.1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let g : ℕ → Fin m → ℝ := fun t c => score D σ (P t) c
  let η : ℝ := 4*δ
  let W (t : ℕ) : ℝ := ∑ c, mwWeight g η t c
  have hW (t : ℕ) : 0 < W t :=
    Finset.sum_pos' (fun c _ => (Real.exp_pos _).le)
      ⟨⟨0,hm0⟩,Finset.mem_univ _,Real.exp_pos _⟩
  have hw (t : ℕ) (c : Fin m) :
      mwWeight g η (t+1) c = mwWeight g η t c*Real.exp (η*g t c) := by
    simp only [mwWeight,Finset.sum_range_succ,mul_add,Real.exp_add]
  have hp (t : ℕ) (c : Fin m) : (P t).val c = mwProbability g η t c := by
    induction t generalizing c with
    | zero => rw [hP.1]; simp [mwProbability,mwWeight]
    | succ t ih =>
      rw [hP.2]
      have hall (b : Fin m) : (P t).val b = mwProbability g η t b := by
        exact ih b
      simp_rw [hall]
      have hden : (∑ b, mwProbability g η t b*Real.exp (η*g t b)) = W (t+1)/W t := by
        simp only [mwProbability,div_mul_eq_mul_div,← Finset.sum_div]
        congr 1
        dsimp only [W]
        simp_rw [hw]
      change mwProbability g η t c*Real.exp (η*g t c) /
        (∑ b, mwProbability g η t b*Real.exp (η*g t b)) = _
      rw [hden]
      change (mwWeight g η t c/W t)*Real.exp (η*g t c)/(W (t+1)/W t) =
        mwWeight g η (t+1) c/W (t+1)
      rw [hw]
      field_simp [ne_of_gt (hW t),ne_of_gt (hW (t+1))]
  have hgain (t : ℕ) : (∑ b, mwProbability g η t b*g t b) = mu D := by
    simp_rw [← hp]
    exact h.child_3 n m hn hm0 D σ (P t)
  have hregret (c : Fin m) : (∑ t ∈ Finset.range N, score D σ (P t) c)/(N : ℝ) ≤ mu D+δ := by
    have hg : ∀ t c, g t c ∈ Icc (0 : ℝ) 1 :=
      fun t c => (h.child_5 n m hn hm0 D σ (P t)).1 c
    have hr := h.child_0 m hm0 g hg η (by dsimp [η]; positivity) N hN c
    simp_rw [hgain] at hr
    have hs : (∑ t ∈ Finset.range N, mu D)/(N : ℝ) = mu D := by
      simp [ne_of_gt hNr]
    rw [hs] at hr
    dsimp only [η,g] at hr
    have her : 4*δ/8 = δ/2 := by ring
    rw [her] at hr
    exact le_trans hr (by linarith [hi.2.1])
  have hsumweights : ∑ t ∈ Finset.range N, (1/(N : ℝ)) = 1 := by
    simp [ne_of_gt hNr]
  have hvec : (∑ t ∈ Finset.range N, (1/(N : ℝ)) • (P t).val) = Q.val := by
    ext c
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [← Finset.mul_sum]
    rw [hQ c]
    ring
  intro c
  have hjensen (v : Fin n) : compare D (σ v) Q c ≤
      (∑ t ∈ Finset.range N, compare D (σ v) (P t) c)/(N : ℝ) := by
    have hcv := (h.child_4 m D (σ v) Q c).2.2.2
    have hj := hcv.map_sum_le
      (t := Finset.range N) (w := fun _ => 1/(N : ℝ))
      (fun t _ => by positivity) hsumweights
      (fun t _ => (P t).property)
    rw [hvec] at hj
    simp_rw [← (h.child_4 m D (σ v) Q c).1] at hj
    have he (t : ℕ) : ambientCompare D (σ v) (P t).val c = compare D (σ v) (P t) c :=
      (h.child_4 m D (σ v) (P t) c).1.symm
    simp_rw [he] at hj
    change compare D (σ v) Q c ≤ ∑ t ∈ Finset.range N, (1/(N : ℝ))*compare D (σ v) (P t) c at hj
    rw [← Finset.mul_sum] at hj
    convert hj using 1 <;> ring
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    score D σ Q c ≤ (∑ v, (∑ t ∈ Finset.range N, compare D (σ v) (P t) c)/(N : ℝ))/(n : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun v _ => hjensen v)) hnR.le
    _ = (∑ t ∈ Finset.range N, score D σ (P t) c)/(N : ℝ) := by
      unfold score avg
      rw [← Finset.sum_div,Finset.sum_comm,← Finset.sum_div]
      ring
    _ ≤ mu D+δ := hregret c

#print axioms from_children
end MetricDistortion.Contracts.Computation_MWGuarantee
