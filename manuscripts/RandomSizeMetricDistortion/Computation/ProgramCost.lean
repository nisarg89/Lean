import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Computation_ProgramCost

private theorem budget_bound (n m : ℕ) (hn : 0 < n) (hm : 2 ≤ m)
    (ε : ℝ) (he : 0 < ε) : loopBudget n m ε ≤ 1024*computationBound n m ε := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hn)
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have he0 : ε ≠ 0 := ne_of_gt he
  have hlog : 0 < Real.log m := Real.log_pos (by linarith)
  have hδ : 0 < ε/(32*(n : ℝ)) := by positivity
  have hx : 0 ≤ Real.log m/(2*(ε/(32*(n : ℝ)))^2) := by positivity
  have hceil := le_of_lt (Nat.ceil_lt_add_one hx)
  have hceil_mul := mul_le_mul_of_nonneg_left hceil
    (by positivity : 0 ≤ (n : ℝ)*(m : ℝ))
  have hscale : (n : ℝ)*(m : ℝ)*(Real.log m/(2*(ε/(32*(n : ℝ)))^2)) =
      512*(n : ℝ)^3*(m : ℝ)*Real.log m/ε^2 := by
    field_simp [he0,hn0]
    <;> ring
  have hmSq : (m : ℝ) ≤ (m : ℝ)^2 := by nlinarith
  have hsmall : (n : ℝ)*(m : ℝ) ≤ (n : ℝ)*(m : ℝ)^2 :=
    mul_le_mul_of_nonneg_left hmSq (by positivity)
  have hone : (1 : ℝ) ≤ (n : ℝ)*(m : ℝ)^2 := by
    have := mul_le_mul_of_nonneg_left (by nlinarith : (1 : ℝ) ≤ (m : ℝ)^2)
      (by positivity : 0 ≤ (n : ℝ))
    nlinarith
  have hlarge : 0 ≤ (n : ℝ)^3*(m : ℝ)*Real.log m/ε^2 := by positivity
  rw [mul_add] at hceil_mul
  rw [hscale] at hceil_mul
  let N : ℕ := Nat.ceil (Real.log m/(2*(ε/(32*(n : ℝ)))^2))
  have hceil' : (n : ℝ)*m*(N : ℝ) ≤
      512*((n : ℝ)^3*m*Real.log m/ε^2)+(n : ℝ)*m := by
    calc
      _ ≤ _ := hceil_mul
      _ = _ := by ring
  calc
    loopBudget n m ε = (n : ℝ)*m^2+(n : ℝ)*m*(N : ℝ)+1 := by
      rfl
    _ ≤ (n : ℝ)*m^2+(512*((n : ℝ)^3*m*Real.log m/ε^2)+(n : ℝ)*m)+1 := by
      linarith only [hceil']
    _ ≤ 3*((n : ℝ)*m^2)+512*((n : ℝ)^3*m*Real.log m/ε^2) := by
      linarith only [hsmall,hone]
    _ ≤ 1024*((n : ℝ)*m^2+(n : ℝ)^3*m*Real.log m/ε^2) := by
      linarith only [hone,hlarge]
    _ = 1024*computationBound n m ε := rfl

theorem from_children (h : Needs) : Statement := by
  intro prog himplements hloop hcorrect
  obtain ⟨K,hK,hwork⟩ := hloop
  refine ⟨K*1024, mul_pos hK (by norm_num), ?_⟩
  intro n m hn hm σ ε hε
  obtain ⟨k,out,hrun,hhalt,hcost⟩ := hwork n m hn hm σ ε hε
  obtain ⟨Q,hQ,hbound⟩ := hcorrect n m hn hm σ ε hε k out hrun hhalt
  refine ⟨Q,k,out,hrun,hhalt,hQ,hbound,?_⟩
  calc
    (k : ℝ) ≤ K*loopBudget n m ε := hcost
    _ ≤ K*(1024*computationBound n m ε) :=
      mul_le_mul_of_nonneg_left (budget_bound n m hn hm ε hε.1) hK.le
    _ = _ := by ring

#print axioms from_children
end MetricDistortion.Contracts.Computation_ProgramCost
