import Voting.Distortion.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Geometry_IntegratedLocalCut

private lemma mass_bounds {m : ℕ} (P : Lottery m) (H : Set (Fin m)) :
    mass P H ∈ Icc (0 : ℝ) 1 := by
  constructor
  · unfold mass
    apply Finset.sum_nonneg
    intro c _
    split_ifs
    · exact P.property.1 c
    · exact le_rfl
  · calc
      mass P H ≤ ∑ c, P.val c := by
        unfold mass
        apply Finset.sum_le_sum
        intro c _
        split_ifs
        · exact le_rfl
        · exact P.property.1 c
      _ = 1 := P.property.2

theorem from_children (h : Needs) : Statement := by
  intro D w hw n m hn hm σ P d hd o v j hr
  let a := lowerCut σ P d o v
  let A := upperCut σ P d o v
  let p : ℝ → ℝ := fun t => mass P (marked d o t)
  let r := below (σ v) P o
  let M := sSup (Set.range fun c => distance d (.inr o) (.inr c))
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let ν : Measure ℝ := (w.nu j).restrict (Icc (0 : ℝ) 1)
  have hnu := hw.2.2.2.2.2.2.2.2.1 j
  letI : IsFiniteMeasure ν := ⟨by
    dsimp [ν]
    rw [Measure.restrict_apply_univ,hnu.1]
    exact ENNReal.ofReal_lt_top⟩
  have hstep := (h.child_2 n m σ P d o v).2.2.2
  have hzero : ∀ t, M ≤ t → a t=0 ∧ A t=0 := (h.child_2 n m σ P d o v).2.2.1
  let af : Set (Fin m) → ℝ := fun H => sInf {z | ∃ c, c ∉ H ∧ z=below (σ v) P c}
  let Af : Set (Fin m) → ℝ := fun H =>
    if ∃ c, c ∈ H ∧ 0 < P.val c then
      sSup {z | ∃ c, c ∈ H ∧ 0 < P.val c ∧ z=below (σ v) P c+P.val c} else 0
  have hameas : Measurable a := by
    have he : a=(fun t => af (marked d o t)) := by funext t; rfl
    rw [he]
    exact (hstep af).1
  have hAmeas : Measurable A := by
    have he : A=(fun t => Af (marked d o t)) := by funext t; rfl
    rw [he]
    exact (hstep Af).1
  let E : Set (ℝ × ℝ) := {y | y.1 ∈ Ioc (0 : ℝ) M ∧
    a y.1 ≤ min y.2 r ∧ min y.2 r < A y.1}
  let g : ℝ × ℝ → ℝ := E.indicator (fun _ => 1)
  have hmin : Measurable (fun y : ℝ × ℝ => min y.2 r) := measurable_snd.min measurable_const
  have hE : MeasurableSet E :=
    (measurableSet_Ioc.preimage measurable_fst).inter
      ((measurableSet_le (hameas.comp measurable_fst) hmin).inter
        (measurableSet_lt hmin (hAmeas.comp measurable_fst)))
  have hgmeas : Measurable g := measurable_const.indicator hE
  have hdom : Integrable ((Ioc (0 : ℝ) M).indicator (fun _ => (1 : ℝ))) μ := by
    exact ((integrable_indicator_iff measurableSet_Ioc).2
      (integrableOn_const (by simp [Real.volume_Ioc]))).restrict
  have hg : Integrable g (μ.prod ν) := by
    apply (hdom.comp_fst ν).mono' hgmeas.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun y => by
      by_cases hy : y ∈ E
      · have hyt := hy.1
        simp only [g,Set.indicator_of_mem hy,Set.indicator_of_mem hyt,norm_one,le_refl]
      · simp only [g,Set.indicator_of_notMem hy,norm_zero]
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hEiff (t : ℝ) (ht : 0 < t) (z : ℝ) :
      (t,z) ∈ E ↔ t ∈ crossing σ P d o v (min z r) := by
    constructor
    · intro htz
      exact ⟨ht.le,htz.2⟩
    · intro htz
      refine ⟨⟨ht,?_⟩,htz.2⟩
      by_contra htM
      have hz := hzero t (le_of_not_ge htM)
      have hq0 : a t ≤ min z r := htz.2.1
      have hq1 : min z r < A t := htz.2.2
      rw [hz.1] at hq0
      rw [hz.2] at hq1
      exact hq1.not_ge hq0
  have hslice (t : ℝ) (ht : 0 < t) : (∫ z, g (t,z) ∂ν) =
      (w.nu j {z | z ∈ Icc (0 : ℝ) 1 ∧ a t ≤ min z r ∧ min z r < A t}).toReal := by
    let Z : Set ℝ := {z | a t ≤ min z r ∧ min z r < A t}
    have hZ : MeasurableSet Z :=
      (measurableSet_le measurable_const (measurable_id.min measurable_const)).inter
        (measurableSet_lt (measurable_id.min measurable_const) measurable_const)
    have heq : (fun z => g (t,z)) = Z.indicator (fun _ => (1 : ℝ)) := by
      funext z
      by_cases hz : z ∈ Z
      · have htE : (t,z) ∈ E := (hEiff t ht z).2 ⟨ht.le,hz⟩
        simp only [g,Set.indicator_of_mem htE,Set.indicator_of_mem hz]
      · have htE : (t,z) ∉ E := fun he => hz ((hEiff t ht z).1 he).2
        simp only [g,Set.indicator_of_notMem htE,Set.indicator_of_notMem hz]
    rw [heq,integral_indicator_const (1 : ℝ) hZ]
    have heqSet : Z ∩ Icc (0 : ℝ) 1 =
        {z | z ∈ Icc (0 : ℝ) 1 ∧ a t ≤ min z r ∧ min z r < A t} := by
      ext z
      simp only [Set.mem_inter_iff,Z,Set.mem_ofPred_eq,and_comm]
    simp only [smul_eq_mul,mul_one,measureReal_def,ν,Measure.restrict_apply hZ,heqSet]
  have hcross (z : ℝ) : (∫ t, g (t,z) ∂μ) =
      tailIntegral (indicator (crossing σ P d o v (min z r))) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    by_cases hz : t ∈ crossing σ P d o v (min z r)
    · have htE := (hEiff t ht z).2 hz
      simp only [g,indicator,Set.indicator_of_mem htE,Set.indicator_of_mem hz]
    · have htE : (t,z) ∉ E := fun he => hz ((hEiff t ht z).1 he)
      simp only [g,indicator,Set.indicator_of_notMem htE,Set.indicator_of_notMem hz]
  have hRint : IntegrableOn (fun t => w.lambda (p t)*
      (∫ u in region (σ v) P (marked d o t), (phi D u-mu D))) (Ioi (0 : ℝ)) volume := by
    apply (hstep (fun H => w.lambda (mass P H)*
      (∫ u in region (σ v) P H, (phi D u-mu D)))).2
    simp [mass,region,hw.2.2.2.2.1]
  have htauzero : w.tau j 0=0 := hw.2.2.2.2.2.2.2.2.2.2.1 j
  have hTint : IntegrableOn (fun t => w.tau j (p t)) (Ioi (0 : ℝ)) volume := by
    apply (hstep (fun H => w.tau j (mass P H))).2
    simpa [mass] using htauzero
  have haint := (h.child_2 n m σ P d o v).1
  let l : ℝ → ℝ := fun t => a t+w.lambda (p t)*
    (∫ u in region (σ v) P (marked d o t), (phi D u-mu D))+
    w.tau j (p t)*(mu D-phi D r)
  have hlint : Integrable l μ :=
    (haint.fun_add hRint).fun_add (hTint.mul_const (mu D-phi D r))
  have hpoint : ∀ t, 0 < t → l t ≤ ∫ z, g (t,z) ∂ν := by
    intro t ht
    have hc := h.child_3 n m σ P d o v t ht.le
    have hregionMeas : MeasurableSet (region (σ v) P (marked d o t)) := by
      unfold region
      exact MeasurableSet.iUnion fun c => MeasurableSet.iUnion fun _ => measurableSet_Ico
    have hR := h.child_0 D (a t) (p t) (A t) hc.1 (hc.2.1.trans (min_le_left _ _))
      hc.2.2.1 hc.2.2.2.1 (region (σ v) P (marked d o t)) hregionMeas
      hc.2.2.2.2.1 ((h.child_4 m (σ v) P).2.2.1 (marked d o t)) hc.2.2.2.2.2.1
    have hlocal := hw.2.2.2.2.2.2.2.2.2.2.2 j r hr (a t) (p t) (A t)
      hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1
    have hlambda : 0 ≤ w.lambda (p t) := hw.2.2.2.1 _ (mass_bounds P _)
    rw [hslice t ht]
    unfold LocalCut at hlocal
    change a t+w.lambda (p t)*(∫ u in region (σ v) P (marked d o t), (phi D u-mu D))+
      w.tau j (p t)*(mu D-phi D r) ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hR hlambda]
  have H := integral_mono_ae hlint hg.integral_prod_left (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hpoint t ht)
  have hinner : ∀ᵐ z ∂ν, (∫ t, g (t,z) ∂μ) ≤ 2*distance d (.inl v) (.inr o) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
    rw [hcross z]
    have hr01 : r ∈ Icc (0 : ℝ) 1 := mass_bounds P _
    have hmin01 : min z r ∈ Icc (0 : ℝ) 1 :=
      ⟨le_min hz.1 hr01.1,(min_le_left _ _).trans hz.2⟩
    exact (h.child_1 n m hn hm σ P d hd o v).2 _ hmin01
  have HR := integral_mono_ae hg.integral_prod_right
    (integrable_const (2*distance d (.inl v) (.inr o))) hinner
  rw [← integral_integral_swap (f := fun t z => g (t,z)) hg] at HR
  have htotal : (∫ _ : ℝ, 2*distance d (.inl v) (.inr o) ∂ν) =
      2*w.C0*distance d (.inl v) (.inr o) := by
    rw [integral_const]
    simp only [smul_eq_mul,measureReal_def,ν,Measure.restrict_apply_univ,hnu.1,
      ENNReal.toReal_ofReal hw.1]
    ring
  have HH := H.trans (HR.trans_eq htotal)
  change (∫ t in Ioi (0 : ℝ), a t+w.lambda (p t)*
      (∫ u in region (σ v) P (marked d o t), (phi D u-mu D))+
      w.tau j (p t)*(mu D-phi D r)) ≤ _ at HH
  rw [integral_add (haint.fun_add hRint) (hTint.mul_const _),integral_mul_const] at HH
  exact HH

#print axioms from_children
end MetricDistortion.Contracts.Geometry_IntegratedLocalCut
