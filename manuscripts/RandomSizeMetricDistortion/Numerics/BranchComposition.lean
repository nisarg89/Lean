import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Numerics_BranchComposition

private theorem potential_le (h : Needs) (j : Fin 9) (a : ℝ) :
    rankPotential j a ≤ oldPotential j a := by
  have hs := h.child_4 j
  unfold rankPotential oldPotential
  split_ifs with hab hah
  · exact le_rfl
  · linarith [hs.2.2.2.1]
  · have ht := hs.2.2.2.2.2 a (le_of_not_ge hah)
    linarith

theorem from_children (h : Needs) : Statement := by
  intro hfinite hstrong D hD j r hr p hp a A ha hap hpA hA
  have hb1 : bStar ≤ 1 := by norm_num [bStar]
  have hr1 : r ≤ 1 := by
    rcases hr with hr | hr
    · exact ((h.child_6.2.1 j).2.2 hr).2.trans hb1
    · exact hr.2
  have hap' : a ≤ p := hap.trans (min_le_left _ _)
  have har : a ≤ r := hap.trans (min_le_right _ _)
  have haA : a ≤ A := hap'.trans hpA
  have ha1 : a ≤ 1 := haA.trans hA
  have hlaw := h.child_5.2 D hD
  have hdom := h.child_2 a p A r ⟨ha,hap,hpA,hA⟩
  let q : ℝ := a+lambdaStar p*(HStar (a+A-p)-HStar a-HStar A)+tauStar j p*psiStar r
  have htarget : LocalCut D fixedWitness j a p A r ↔
      q ≤ (nuStar j (if r < A then Icc a 1 else Ico a A)).toReal := by
    unfold LocalCut
    simp only [fixedWitness,hlaw.1,hlaw.2.1,hlaw.2.2.1,hdom]
    dsimp [q,HStar,psiStar]
    ring_nf
  apply htarget.mpr
  have hDnonpos : lambdaStar p*(HStar (a+A-p)-HStar A-HStar (a+1-p)) ≤ 0 := by
    have hb := h.child_0 (a+A-p) (p-a) (1-A) (by linarith) (by linarith) (by linarith)
    have h1 : HStar 1 = 0 := by norm_num [HStar,muStar,PhiStar]
    have hid1 : a+A-p+(1-A) = a+1-p := by ring
    have hid2 : a+A-p+(p-a)+(1-A) = 1 := by ring
    have hid3 : a+A-p+(p-a) = A := by ring
    rw [hid1,hid2,hid3,h1] at hb
    have hl := h.child_8.1 p ⟨hp.1.le,hp.2.le⟩
    have hprod := mul_nonneg hl hb
    nlinarith
  have hfirst := (hfinite j).1 r hr p hp a ha hap
  have hfirstq : q+oldPotential j a-cStar ≤ 0 := by
    dsimp [q]
    unfold firstResidual at hfirst
    linarith
  have hcap : q ≤ cStar-rankPotential j a := by
    have hf := potential_le h j a
    linarith
  by_cases hrA : r < A
  · rw [if_pos hrA,h.child_9.2 j a ha ha1]
    exact hcap
  · rw [if_neg hrA,h.child_9.1 j a A ha haA hA]
    have hAr : A ≤ r := le_of_not_gt hrA
    by_cases hAh : cutoff j < A
    · have hAb : ¬ A ≤ bStar := not_le_of_gt ((h.child_4 j).1.trans hAh)
      simpa [rankPotential,hAb,not_le.mpr hAh] using hcap
    · have hAh' : A ≤ cutoff j := le_of_not_gt hAh
      by_cases hAb : A ≤ bStar
      · have hab : a ≤ bStar := haA.trans hAb
        have hint := (hfinite j).2 r hr p hp a A ha hap' hpA hAr
        simpa [internalResidual,q,oldPotential,hab,hAb,rankPotential] using hint
      · have hbA : bStar < A := lt_of_not_ge hAb
        by_cases hab : a ≤ bStar
        · have hint := hstrong j p hp a A r ha (le_min hap' hab)
            (max_le hpA hbA.le) hbA hAr hr1
          have hnewa : rankPotential j a = 0 := by simp [rankPotential,hab]
          have hnewA : rankPotential j A = oldPotential j A-shift j := by
            simp [rankPotential,oldPotential,hAb,hAh']
          rw [hnewa,hnewA]
          dsimp [q]
          unfold internalResidual oldPotential at hint
          simp only [hab,ite_true,hAb,ite_false] at hint
          simp only [oldPotential,hAb,ite_false]
          linarith
        · have hah : a ≤ cutoff j := haA.trans hAh'
          have hint := (hfinite j).2 r hr p hp a A ha hap' hpA hAr
          have hnewa : rankPotential j a = oldPotential j a-shift j := by
            simp [rankPotential,oldPotential,hab,hah]
          have hnewA : rankPotential j A = oldPotential j A-shift j := by
            simp [rankPotential,oldPotential,hAb,hAh']
          rw [hnewa,hnewA]
          dsimp [q]
          unfold internalResidual at hint
          linarith

#print axioms from_children
end MetricDistortion.Contracts.Numerics_BranchComposition
