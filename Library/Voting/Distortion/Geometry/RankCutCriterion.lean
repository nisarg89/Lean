import Voting.Distortion.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Geometry_RankCutCriterion

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

private lemma avg_add {n : ℕ} (f g : Fin n → ℝ) :
    avg (fun v => f v+g v) = avg f+avg g := by
  simp [avg,Finset.sum_add_distrib,add_div]

private lemma avg_sub {n : ℕ} (f g : Fin n → ℝ) :
    avg (fun v => f v-g v) = avg f-avg g := by
  simp [avg,Finset.sum_sub_distrib,sub_div]

private lemma avg_mul {n : ℕ} (a : ℝ) (f : Fin n → ℝ) :
    avg (fun v => a*f v) = a*avg f := by
  unfold avg
  rw [← Finset.mul_sum]
  exact mul_div_assoc _ _ _

private lemma avg_const {n : ℕ} (hn : 0 < n) (a : ℝ) : avg (fun _ : Fin n => a) = a := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  simp [avg,hn0]

private lemma avg_le {n : ℕ} {f g : Fin n → ℝ} (H : ∀ v, f v ≤ g v) : avg f ≤ avg g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun v _ => H v) (Nat.cast_nonneg n)

private lemma avg_tail {n : ℕ} (f : Fin n → ℝ → ℝ)
    (hf : ∀ v, IntegrableOn (f v) (Ioi (0 : ℝ)) volume) :
    avg (fun v => tailIntegral (f v)) = tailIntegral (fun t => avg (fun v => f v t)) := by
  unfold tailIntegral avg
  rw [integral_div,integral_finsetSum Finset.univ (fun v _ => hf v)]

private lemma cost_average {n m : ℕ} (d : Metric n m) (P : Lottery m) (o : Fin m) :
    expectedCost d P-sc d o =
      avg (fun v => (∑ c, P.val c*distance d (.inl v) (.inr c))-distance d (.inl v) (.inr o)) := by
  have he : expectedCost d P = avg (fun v => ∑ c, P.val c*distance d (.inl v) (.inr c)) := by
    change (∑ c, P.val c*((∑ v, distance d (.inl v) (.inr c))/(n : ℝ))) =
      (∑ v, ∑ c, P.val c*distance d (.inl v) (.inr c))/(n : ℝ)
    calc
      _ = ∑ c, (∑ v, P.val c*distance d (.inl v) (.inr c))/(n : ℝ) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [← mul_div_assoc,Finset.mul_sum]
      _ = (∑ c, ∑ v, P.val c*distance d (.inl v) (.inr c))/(n : ℝ) := by
        simp only [Finset.sum_div]
      _ = _ := by rw [Finset.sum_comm]
  rw [avg_sub,← he]
  simp only [sc]

/-- Average the paper's integrated local inequalities using one common minimum
coefficient. The remaining error is the integral of the approximate stability
loss plus the coefficient at index zero. -/
private theorem metric_bound (h : Needs) (D : DrawLaw) (w : CutParameters) (hw : ValidCut D w)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (σ : Profile n m) (P : Lottery m)
    (δ : ℝ) (hδ : 0 ≤ δ) (hs : ApproxStable D σ P δ) (d : Metric n m)
    (hd : Consistent σ d) (o : Fin m) :
    expectedCost d P ≤ (1+2*w.C0)*sc d o + δ*(
      tailIntegral (fun t => (1-mass P (marked d o t))*w.lambda (mass P (marked d o t)))+
      tailIntegral (fun t => w.tau 0 (mass P (marked d o t)))) := by
  let v0 : Fin n := ⟨0,hn⟩
  let p : ℝ → ℝ := fun t => mass P (marked d o t)
  let f : Fin n → ℝ → ℝ := fun v t => w.lambda (p t)*
    (∫ u in region (σ v) P (marked d o t), (phi D u-mu D))
  let I : Fin n → ℝ := fun v => tailIntegral (fun t => lowerCut σ P d o v t+f v t)
  let K : Fin 9 → ℝ := fun j => tailIntegral (fun t => w.tau j (p t))
  let J : ℝ := tailIntegral (fun t => (1-p t)*w.lambda (p t))
  have hstep := (h.child_4 n m σ P d o v0).2.2.2
  have hlambda : ∀ t, 0 ≤ w.lambda (p t) := fun t => hw.2.2.2.1 _ (mass_bounds P _)
  have htau : ∀ j t, 0 ≤ w.tau j (p t) := fun j t => hw.2.2.2.2.2.2.2.2.2.1 j _ (mass_bounds P _)
  have htauzero : ∀ j, w.tau j 0=0 := hw.2.2.2.2.2.2.2.2.2.2.1
  have hlambdazero : w.lambda 0=0 := hw.2.2.2.2.1
  have hKint (j : Fin 9) : IntegrableOn (fun t => w.tau j (p t)) (Ioi (0 : ℝ)) volume := by
    apply (hstep (fun H => w.tau j (mass P H))).2
    simpa [mass] using htauzero j
  have hJint : IntegrableOn (fun t => (1-p t)*w.lambda (p t)) (Ioi (0 : ℝ)) volume := by
    apply (hstep (fun H => (1-mass P H)*w.lambda (mass P H))).2
    simp [mass,hlambdazero]
  have hfint (v : Fin n) : IntegrableOn (f v) (Ioi (0 : ℝ)) volume := by
    apply (hstep (fun H => w.lambda (mass P H)*
      (∫ u in region (σ v) P H, (phi D u-mu D)))).2
    simp [mass,region,hlambdazero]
  have haint (v : Fin n) := (h.child_4 n m σ P d o v).1
  have hKnonneg (j : Fin 9) : 0 ≤ K j := integral_nonneg fun t => htau j t
  obtain ⟨j0,hjmin,hchoose⟩ := h.child_1 K w D hKnonneg hw
  have hper (v : Fin n) : I v+K j0*(mu D-phi D (below (σ v) P o)) ≤
      2*w.C0*distance d (.inl v) (.inr o) := by
    obtain ⟨j,hj,hcoef⟩ := hchoose (below (σ v) P o) (mass_bounds P _)
    have H := h.child_0 D w hw n m hn hm σ P d hd o v j hj
    change I v+K j*(mu D-phi D (below (σ v) P o)) ≤ _ at H
    linarith
  have havg := avg_le hper
  have havgI : avg I = avg (fun v => tailIntegral (lowerCut σ P d o v))+
      avg (fun v => tailIntegral (f v)) := by
    have heq : I=(fun v => tailIntegral (lowerCut σ P d o v)+tailIntegral (f v)) := by
      funext v
      exact integral_add (haint v) (hfint v)
    rw [heq,avg_add]
  have havgPer : avg (fun v => tailIntegral (lowerCut σ P d o v))+
      avg (fun v => tailIntegral (f v))+
      K j0*(mu D-avg (fun v => phi D (below (σ v) P o))) ≤ 2*w.C0*sc d o := by
    simpa only [avg_add,avg_mul,avg_sub,avg_const hn,havgI,sc] using havg
  have hfavgint : IntegrableOn (fun t => avg (fun v => f v t)) (Ioi (0 : ℝ)) volume :=
    (integrable_finsetSum Finset.univ (fun v _ => hfint v)).div_const (n : ℝ)
  have hfbound : -δ*J ≤ avg (fun v => tailIntegral (f v)) := by
    rw [avg_tail f hfint]
    have H := integral_mono_ae (hJint.const_mul (-δ)) hfavgint (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hcancel := (h.child_2 n m hn hm D σ P δ hδ hs (marked d o t) o).1
      change -δ*(1-p t) ≤ avg (fun v => ∫ u in region (σ v) P (marked d o t), (phi D u-mu D)) at hcancel
      change -δ*((1-p t)*w.lambda (p t)) ≤ avg (fun v => w.lambda (p t)*
        (∫ u in region (σ v) P (marked d o t), (phi D u-mu D)))
      rw [avg_mul]
      nlinarith [mul_le_mul_of_nonneg_left hcancel (hlambda t)])
    simpa only [integral_const_mul,J,tailIntegral] using H
  have hposition := (h.child_2 n m hn hm D σ P δ hδ hs ∅ o).2
  have hcoef : -δ*K j0 ≤ K j0*(mu D-avg (fun v => phi D (below (σ v) P o))) := by
    nlinarith [mul_nonneg (hKnonneg j0) (sub_nonneg.mpr hposition)]
  have hcost : expectedCost d P-sc d o ≤ avg (fun v => tailIntegral (lowerCut σ P d o v)) := by
    rw [cost_average]
    exact avg_le (fun v => h.child_5 n m σ P d hd o v)
  have hmin : δ*(J+K j0) ≤ δ*(J+K 0) :=
    mul_le_mul_of_nonneg_left (by linarith [hjmin 0]) hδ
  change expectedCost d P ≤ (1+2*w.C0)*sc d o+δ*(J+K 0)
  nlinarith

theorem from_children (h : Needs) : Statement := by
  intro D w hw
  constructor
  · intro n m hn hm σ P hs
    apply h.child_3 n m hn hm σ P (1+2*w.C0) (by nlinarith [hw.1])
    intro d hd o ho
    have hs0 : ApproxStable D σ P 0 := by simpa [ApproxStable,Stable] using hs
    have H := metric_bound h D w hw n m hn hm σ P 0 le_rfl hs0 d hd o
    simpa using H
  · intro B hB n m hn hm σ P δ hδ hs d hd o ho
    let p : ℝ → ℝ := fun t => mass P (marked d o t)
    let M := sSup (Set.range fun c => distance d (.inr o) (.inr c))
    let v0 : Fin n := ⟨0,hn⟩
    have hstep := (h.child_4 n m σ P d o v0).2.2.2
    have htauzero : w.tau 0 0=0 := hw.2.2.2.2.2.2.2.2.2.2.1 0
    have hlambdazero : w.lambda 0=0 := hw.2.2.2.2.1
    have hsumint : IntegrableOn
        (fun t => (1-p t)*w.lambda (p t)+w.tau 0 (p t)) (Ioi (0 : ℝ)) volume := by
      apply (hstep (fun H => (1-mass P H)*w.lambda (mass P H)+w.tau 0 (mass P H))).2
      simp [mass,htauzero,hlambdazero]
    have hJint : IntegrableOn (fun t => (1-p t)*w.lambda (p t)) (Ioi (0 : ℝ)) volume := by
      apply (hstep (fun H => (1-mass P H)*w.lambda (mass P H))).2
      simp [mass,hlambdazero]
    have hKint : IntegrableOn (fun t => w.tau 0 (p t)) (Ioi (0 : ℝ)) volume := by
      apply (hstep (fun H => w.tau 0 (mass P H))).2
      simp [mass,htauzero]
    have hM0 : 0 ≤ M := by
      exact (@dist_nonneg _ d (.inr o) (.inr o)).trans
        (le_csSup (Set.finite_range (fun c : Fin m => distance d (.inr o) (.inr c))).bddAbove ⟨o,rfl⟩)
    have hdom : Integrable ((Ioc (0 : ℝ) M).indicator (fun _ => B)) volume :=
      (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by simp [Real.volume_Ioc]))
    have hbound : tailIntegral (fun t => (1-p t)*w.lambda (p t))+
        tailIntegral (fun t => w.tau 0 (p t)) ≤ B*M := by
      unfold tailIntegral
      rw [← integral_add hJint hKint]
      have H := integral_mono_ae hsumint hdom.restrict (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        by_cases htM : t ≤ M
        · rw [Set.indicator_of_mem (show t ∈ Ioc (0 : ℝ) M from ⟨ht,htM⟩)]
          exact hB (p t) (mass_bounds P _)
        · have hempty : marked d o t=∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro c hc
            have hcM : distance d (.inr o) (.inr c) ≤ M :=
              le_csSup (Set.finite_range (fun c : Fin m => distance d (.inr o) (.inr c))).bddAbove ⟨c,rfl⟩
            exact (hc.trans_le hcM).not_ge (le_of_not_ge htM)
          have hp0 : p t=0 := by simp [p,hempty,mass]
          simp [hp0,hlambdazero,htauzero,
            Set.indicator_of_notMem (show t ∉ Ioc (0 : ℝ) M from fun hx => htM hx.2)])
      have hI : (∫ t in Ioi (0 : ℝ), (Ioc (0 : ℝ) M).indicator (fun _ => B) t) = B*M := by
        rw [integral_indicator_const B measurableSet_Ioc]
        have hi : Ioc (0 : ℝ) M ∩ Ioi 0 = Ioc 0 M := Set.inter_eq_left.mpr (fun _ ht => ht.1)
        simp only [smul_eq_mul,measureReal_def,Measure.restrict_apply measurableSet_Ioc,hi,
          Real.volume_Ioc,sub_zero,ENNReal.toReal_ofReal hM0]
        ring
      exact H.trans_eq hI
    have H := metric_bound h D w hw n m hn hm σ P δ hδ hs d hd o
    have H' := mul_le_mul_of_nonneg_left hbound hδ
    dsimp [p,M] at hbound H'
    nlinarith

#print axioms from_children
end MetricDistortion.Contracts.Geometry_RankCutCriterion
