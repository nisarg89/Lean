import Voting.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Analysis_MonotoneSetIntegral

/-- Move all mass outside the prescribed initial interval to the rightmost
interval of the same length. Subtracting f at the cut makes the pointwise
indicator comparison have the same sign on both sides of the cut. -/
theorem proved : Statement := by
  intro f hf hmono a p A ha hap hpA hA S hS hsub hvol hcontains
  let c : ℝ := a+A-p
  let g : ℝ → ℝ := fun x => f x-f c
  have hac : a ≤ c := by dsimp [c]; linarith
  have hcA : c ≤ A := by dsimp [c]; linarith
  have hc0 : 0 ≤ c := ha.trans hac
  have hc01 : c ∈ Icc (0 : ℝ) 1 := ⟨hc0,hcA.trans hA⟩
  have hS01 : S ⊆ Icc (0 : ℝ) 1 := fun _ hx => ⟨(hsub hx).1,(hsub hx).2.trans hA⟩
  have hL01 : Icc (0 : ℝ) a ⊆ Icc (0 : ℝ) 1 := fun _ hx => ⟨hx.1,hx.2.trans (hap.trans (hpA.trans hA))⟩
  have hR01 : Icc c A ⊆ Icc (0 : ℝ) 1 := fun _ hx => ⟨hc0.trans hx.1,hx.2.trans hA⟩
  have hfg : ContinuousOn g (Icc (0 : ℝ) 1) := hf.sub continuousOn_const
  have hgs : IntegrableOn g S volume := hfg.integrableOn_Icc.mono_set hS01
  have hgL : IntegrableOn g (Icc (0 : ℝ) a) volume := hfg.integrableOn_Icc.mono_set hL01
  have hgR : IntegrableOn g (Icc c A) volume := hfg.integrableOn_Icc.mono_set hR01
  have hIs : Integrable (S.indicator g) volume := (integrable_indicator_iff hS).2 hgs
  have hIL : Integrable ((Icc (0 : ℝ) a).indicator g) volume :=
    (integrable_indicator_iff measurableSet_Icc).2 hgL
  have hIR : Integrable ((Icc c A).indicator g) volume :=
    (integrable_indicator_iff measurableSet_Icc).2 hgR
  have hpoint : ∀ᵐ x ∂volume, S.indicator g x ≤
      (Icc (0 : ℝ) a).indicator g x+(Icc c A).indicator g x := by
    filter_upwards [hcontains] with x hx
    by_cases hxL : x ∈ Icc (0 : ℝ) a
    · have hxS := hx hxL
      by_cases hxR : x ∈ Icc c A
      · have hxc : x=c := le_antisymm (hxL.2.trans hac) hxR.1
        simp only [Set.indicator_of_mem hxS,Set.indicator_of_mem hxL,Set.indicator_of_mem hxR]
        rw [hxc]
        simp [g]
      · simp [Set.indicator_of_mem hxS,Set.indicator_of_mem hxL,Set.indicator_of_notMem hxR]
    · by_cases hxR : x ∈ Icc c A
      · have hgn : 0 ≤ g x := sub_nonneg.mpr (hmono hc01 (hR01 hxR) hxR.1)
        by_cases hxS : x ∈ S
        · simp [Set.indicator_of_mem hxS,Set.indicator_of_notMem hxL,Set.indicator_of_mem hxR]
        · simpa only [Set.indicator_of_notMem hxS,Set.indicator_of_notMem hxL,
            Set.indicator_of_mem hxR,zero_add] using hgn
      · by_cases hxS : x ∈ S
        · have hxc : x ≤ c := by
            by_contra hxc
            exact hxR ⟨(lt_of_not_ge hxc).le,(hsub hxS).2⟩
          have hgn : g x ≤ 0 := sub_nonpos.mpr (hmono (hS01 hxS) hc01 hxc)
          simpa only [Set.indicator_of_mem hxS,Set.indicator_of_notMem hxL,
            Set.indicator_of_notMem hxR,zero_add] using hgn
        · simp [Set.indicator_of_notMem hxS,Set.indicator_of_notMem hxL,Set.indicator_of_notMem hxR]
  have H := integral_mono_ae hIs (hIL.add hIR) hpoint
  simp only [Pi.add_apply] at H
  rw [integral_add hIL hIR,integral_indicator hS,
    integral_indicator measurableSet_Icc,integral_indicator measurableSet_Icc] at H
  have hconstS : IntegrableOn (fun _ : ℝ => f c) S volume :=
    integrableOn_const (by rw [hvol]; exact ENNReal.ofReal_ne_top)
  have hconstL : IntegrableOn (fun _ : ℝ => f c) (Icc (0 : ℝ) a) volume :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hconstR : IntegrableOn (fun _ : ℝ => f c) (Icc c A) volume :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have heS : (∫ x in S, g x) = (∫ x in S, f x)-p*f c := by
    change (∫ x in S, f x-f c) = _
    rw [integral_sub (hf.integrableOn_Icc.mono_set hS01) hconstS,setIntegral_const]
    simp [measureReal_def,hvol,ENNReal.toReal_ofReal (ha.trans hap),smul_eq_mul]
  have heL : (∫ x in Icc (0 : ℝ) a, g x) = (∫ x in (0 : ℝ)..a, f x)-a*f c := by
    change (∫ x in Icc (0 : ℝ) a, f x-f c) = _
    rw [integral_sub (hf.integrableOn_Icc.mono_set hL01) hconstL,setIntegral_const,
      integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le ha]
    simp [measureReal_def,Real.volume_Icc,ENNReal.toReal_ofReal ha,smul_eq_mul]
  have heR : (∫ x in Icc c A, g x) = (∫ x in c..A, f x)-(A-c)*f c := by
    change (∫ x in Icc c A, f x-f c) = _
    rw [integral_sub (hf.integrableOn_Icc.mono_set hR01) hconstR,setIntegral_const,
      integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hcA]
    simp [measureReal_def,Real.volume_Icc,ENNReal.toReal_ofReal (sub_nonneg.mpr hcA),smul_eq_mul]
  rw [heS,heL,heR] at H
  change (∫ x in S, f x) ≤ (∫ x in (0 : ℝ)..a, f x)+(∫ x in c..A, f x)
  dsimp [c] at H ⊢
  nlinarith

#print axioms proved
end MetricDistortion.Contracts.Analysis_MonotoneSetIntegral
