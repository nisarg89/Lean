import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Numerics_MeasureIntervals

theorem from_children (h : Needs) : Statement := by
  intro j a A ha haA hA
  have hs := h.child_0 j
  let f : ℝ → ℝ := fun z => eta j*phiStarDeriv z-1
  let D : Set ℝ := Ioo bStar (cutoff j)
  let T : Set ℝ := Ico a A ∩ D
  have hcont : Continuous f := by dsimp [f,phiStarDeriv]; fun_prop
  have hInt : IntegrableOn f D volume :=
    (hcont.intervalIntegrable bStar (cutoff j)).1.mono_set Ioo_subset_Ioc_self
  have hIntT : IntegrableOn f T volume := hInt.mono_set inter_subset_right
  have hnn : 0 ≤ᵐ[volume.restrict T] f := by
    filter_upwards [ae_restrict_mem (measurableSet_Ico.inter measurableSet_Ioo)] with z hz
    exact hs.2.2.2.2.1 z ⟨hz.2.1.le,hz.2.2.le⟩
  have hnonneg : 0 ≤ ∫ z in T, f z := integral_nonneg_of_ae hnn
  have hdensity : ((volume.restrict D).withDensity (fun z => ENNReal.ofReal (f z))) (Ico a A) =
      ENNReal.ofReal (∫ z in T, f z) := by
    rw [withDensity_apply _ measurableSet_Ico,Measure.restrict_restrict measurableSet_Ico]
    exact (ofReal_integral_eq_lintegral_ofReal hIntT hnn).symm
  have hreal : nuStar j (Ico a A) =
      ENNReal.ofReal (if a ≤ bStar ∧ bStar < A then atom j else 0) +
        ENNReal.ofReal (∫ z in T, f z) := by
    dsimp [nuStar]
    change ENNReal.ofReal (atom j)*(Measure.dirac bStar (Ico a A))+
      ((volume.restrict D).withDensity (fun z => ENNReal.ofReal (f z))) (Ico a A) = _
    rw [hdensity]
    by_cases hb : a ≤ bStar ∧ bStar < A
    · simp [Measure.dirac_apply',hb]
    · simp [Measure.dirac_apply',hb]
  rw [hreal,ENNReal.toReal_add (by simp) (by simp)]
  have hatom : 0 ≤ if a ≤ bStar ∧ bStar < A then atom j else 0 := by
    split_ifs <;> first | exact hs.2.2.1 | exact le_rfl
  rw [ENNReal.toReal_ofReal hatom,ENNReal.toReal_ofReal hnonneg]

#print axioms from_children
end MetricDistortion.Contracts.Numerics_MeasureIntervals
