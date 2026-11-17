import RandomSizeMetricDistortion.Statements
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
namespace MetricDistortion.Contracts.Numerics_MeasureSigns

private theorem base_checks (j : Fin 9) :
    0 ≤ eta j ∧ bStar < cutoff j ∧ cutoff j < 1 ∧ 0 ≤ atom j ∧ 0 < shift j ∧
      0 ≤ eta j*phiStarDeriv bStar-1 ∧ cutoff j+eta j*psiStar (cutoff j) ≤ 0 := by
  fin_cases j <;>
    norm_num [eta,etas,cutoff,cutoffs,atom,shift,shifts,bStar,cStar,psiStar,
      phiStar,phiStarDeriv,muStar]

private theorem derivative_monotone_above_b (z : ℝ) (hz : bStar ≤ z) :
    phiStarDeriv bStar ≤ phiStarDeriv z := by
  have hb : 0 ≤ bStar := by norm_num [bStar]
  have hp := pow_le_pow_left₀ hb hz 31
  unfold phiStarDeriv
  nlinarith

private theorem phi_tangent (a h : ℝ) (hh : 0 ≤ h) (ha : h ≤ a) :
    phiStar h+phiStarDeriv h*(a-h) ≤ phiStar a := by
  have hs : 0 ≤ 2*h+(a-h) := by linarith
  have h2 := pow_add_mul_le_add_pow hh hs 2
  have h32 := pow_add_mul_le_add_pow hh hs 32
  have heq : h+(a-h) = a := by ring
  rw [heq] at h2 h32
  norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one] at h2 h32
  unfold phiStar phiStarDeriv
  nlinarith

theorem from_children (h : Needs) : Statement := by
  intro j
  have hb := base_checks j
  have hdensity : ∀ z, bStar ≤ z → 0 ≤ eta j*phiStarDeriv z-1 := by
    intro z hz
    have hm := mul_le_mul_of_nonneg_left (derivative_monotone_above_b z hz) hb.1
    linarith [hb.2.2.2.2.2.1]
  refine ⟨hb.2.1,hb.2.2.1,hb.2.2.2.1,hb.2.2.2.2.1,?_,?_⟩
  · intro z hz
    exact hdensity z hz.1
  · intro a ha
    have hcut : 0 ≤ cutoff j := (by norm_num [bStar] : 0 ≤ bStar).trans hb.2.1.le
    have ht := mul_le_mul_of_nonneg_left (phi_tangent a (cutoff j) hcut ha) hb.1
    have hprod : (a-cutoff j)*(1-eta j*phiStarDeriv (cutoff j)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ha) (by linarith [hdensity (cutoff j) hb.2.1.le])
    have hrem : a+eta j*psiStar a ≤
        cutoff j+eta j*psiStar (cutoff j)+(a-cutoff j)*(1-eta j*phiStarDeriv (cutoff j)) := by
      unfold psiStar
      nlinarith
    exact hrem.trans (by linarith [hb.2.2.2.2.2.2])

#print axioms from_children
end MetricDistortion.Contracts.Numerics_MeasureSigns
