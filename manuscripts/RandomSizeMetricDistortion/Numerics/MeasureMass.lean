import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Numerics_MeasureMass

private theorem phi_derivative (x : ℝ) : HasDerivAt phiStar (phiStarDeriv x) x := by
  have hd := (((hasDerivAt_id x).const_mul (19/73 : ℝ)).add
    ((hasDerivAt_pow 2 x).const_mul (35/146 : ℝ))).add
      ((hasDerivAt_pow 32 x).div_const 2)
  norm_num only [Nat.cast_ofNat] at hd
  have hcoef : (19/73 : ℝ)+(35/146 : ℝ)*(2*x^1)+(32*x^31)/2 =
      phiStarDeriv x := by norm_num [phiStarDeriv] <;> ring
  rw [hcoef] at hd
  rw [hasDerivAt_iff_isLittleO] at hd ⊢
  simpa only [phiStar,Pi.add_apply,smul_eq_mul,id_eq] using hd

theorem from_children (h : Needs) : Statement := by
  intro j
  have hs := h.child_0 j
  let f : ℝ → ℝ := fun z => eta j*phiStarDeriv z-1
  let g : ℝ → ℝ := fun z => eta j*phiStar z-z
  let A : Set ℝ := Ioo bStar (cutoff j)
  let S : Set ℝ := Icc (0 : ℝ) 1
  let J : ℝ := eta j*(phiStar (cutoff j)-phiStar bStar)-(cutoff j-bStar)
  have hcont : Continuous f := by dsimp [f,phiStarDeriv]; fun_prop
  have hint : IntervalIntegrable f volume bStar (cutoff j) := hcont.intervalIntegrable _ _
  have hi : IntegrableOn f A volume := hint.1.mono_set Ioo_subset_Ioc_self
  have hnn : 0 ≤ᵐ[volume.restrict A] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact hs.2.2.2.2.1 z ⟨hz.1.le,hz.2.le⟩
  have hderiv : ∀ z, HasDerivAt g (f z) z := by
    intro z
    have hd := ((phi_derivative z).const_mul (eta j)).sub (hasDerivAt_id z)
    rw [hasDerivAt_iff_isLittleO] at hd ⊢
    simpa only [f,g,Pi.sub_apply,smul_eq_mul,id_eq] using hd
  have hJ : (∫ z in A, f z) = J := by
    dsimp [A]
    rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hs.1.le]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hderiv z) hint]
    dsimp [g,J]
    ring
  have hJnn : 0 ≤ J := by
    rw [← hJ]
    exact integral_nonneg_of_ae hnn
  have hdensity : ((volume.restrict A).withDensity (fun z => ENNReal.ofReal (f z))) univ =
      ENNReal.ofReal J := by
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hi hnn,hJ]
  have hbS : bStar ∈ S := by norm_num [S,bStar]
  have hAS : A ⊆ S := by
    intro z hz
    have hb : 0 ≤ bStar := by norm_num [bStar]
    exact ⟨hb.trans hz.1.le,hz.2.le.trans hs.2.1.le⟩
  have hzero : ((volume.restrict A).withDensity (fun z => ENNReal.ofReal (f z))) Sᶜ = 0 := by
    have hbase : (volume.restrict A) Sᶜ = 0 := by
      rw [Measure.restrict_apply (show MeasurableSet Sᶜ from measurableSet_Icc.compl)]
      have he : Sᶜ ∩ A = ∅ := by
        ext z
        simp only [Set.mem_inter_iff,Set.mem_compl_iff,Set.mem_empty_iff_false,iff_false,not_and]
        intro hz hzA
        exact hz (hAS hzA)
      rw [he]
      exact measure_empty
    exact withDensity_absolutelyContinuous (volume.restrict A) (fun z => ENNReal.ofReal (f z)) hbase
  have hsupport : nuStar j Sᶜ = 0 := by
    simpa [nuStar,S,A,f,Measure.add_apply,Measure.smul_apply,Measure.dirac_apply',hbS]
      using hzero
  have htotal : nuStar j univ = ENNReal.ofReal cStar := by
    have hsum : atom j+J = cStar := by unfold atom; dsimp [J]; ring
    simpa [nuStar,A,f,Measure.add_apply,Measure.smul_apply,hdensity,
      ← ENNReal.ofReal_add hs.2.2.1 hJnn,hsum] using
      (show ENNReal.ofReal (atom j)+ENNReal.ofReal J = ENNReal.ofReal cStar from by
        rw [← ENNReal.ofReal_add hs.2.2.1 hJnn,hsum])
  refine ⟨?_,hsupport⟩
  have hsum := measure_add_measure_compl (μ := nuStar j) (s := S)
    (show MeasurableSet S from measurableSet_Icc)
  rw [hsupport,add_zero,htotal] at hsum
  exact hsum

#print axioms from_children
end MetricDistortion.Contracts.Numerics_MeasureMass
