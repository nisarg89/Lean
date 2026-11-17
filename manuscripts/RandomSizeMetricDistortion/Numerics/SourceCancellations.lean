import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace MetricDistortion.Contracts.Numerics_SourceCancellations

private lemma shifted_geom (x : ℝ) (d : ℕ) :
    (1-x)*(∑ i ∈ Finset.Icc 1 d, x^i)=x-x^(d+1) := by
  have hset : Finset.Ico 1 (d+1)=Finset.Icc 1 d := by
    ext i
    simp only [Finset.mem_Ico,Finset.mem_Icc]
    omega
  have H := geom_sum_Ico_mul_neg x (show 1 ≤ d+1 by omega)
  rw [hset,pow_one] at H
  simpa only [mul_comm] using H

theorem b_correct (x : ℝ) : (1-x)*sourceB x=HStar x/sourceDenom := by
  have H : (1-x)*sourceB x =
      ∑ k : Fin 3, (sourceWeight k/(sourceDegree k+1 : ℕ)/sourceDenom)*
        (x-x^(sourceDegree k+1)) := by
    unfold sourceB
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    calc
      _ = (sourceWeight k/(sourceDegree k+1 : ℕ)/sourceDenom)*
          ((1-x)*(∑ i ∈ Finset.Icc 1 (sourceDegree k), x^i)) := by ring
      _ = _ := by rw [shifted_geom]
  rw [H]
  norm_num [sourceWeight,sourceDegree,sourceDenom,Fin.sum_univ_succ,muStar,HStar,PhiStar] <;> ring

theorem inc_correct (x h : ℝ) : h*(psiStar x/sourceDenom+sourceInc x h)=
    (HStar (x+h)-HStar x)/sourceDenom := by
  norm_num [sourceInc,sourceWeight,sourceDegree,sourceDenom,Fin.sum_univ_succ,
    Finset.sum_Icc_succ_top,Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial,Nat.factorial,psiStar,phiStar,HStar,PhiStar,muStar] <;> ring

theorem f0_correct (x : ℝ) : x*sourceF0 x=HStar x/sourceDenom := by
  norm_num [sourceF0,sourceWeight,sourceDegree,sourceDenom,Fin.sum_univ_succ,
    muStar,HStar,PhiStar] <;> ring

theorem pd_correct (x y : ℝ) : sourcePD x y (y-x)=(psiStar y-psiStar x)/sourceDenom := by
  norm_num [sourcePD,sourceWeight,sourceDegree,sourceDenom,Fin.sum_univ_succ,
    Finset.sum_range_succ,psiStar,phiStar,muStar] <;> ring

theorem j_correct (x y : ℝ) : (y-x)^2*sourceJ x y=
    (HStar y-HStar x-(y-x)*psiStar y)/sourceDenom := by
  norm_num [sourceJ,sourceWeight,sourceDegree,sourceDenom,Fin.sum_univ_succ,
    Finset.sum_range_succ,psiStar,phiStar,HStar,PhiStar,muStar] <;> ring


theorem proved : Statement :=
  ⟨f0_correct,b_correct,inc_correct,pd_correct,j_correct⟩

#print axioms proved
end MetricDistortion.Contracts.Numerics_SourceCancellations
