import Voting.Distortion.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Geometry_MetricTail

theorem from_children (h : Needs) : Statement := by
  intro n m σ P d hd o v
  let e : Fin m → ℝ := fun c => distance d (.inl v) (.inr c)-distance d (.inl v) (.inr o)
  let g : ℝ → ℝ := fun t => ∑ c, P.val c*(Ioo (0 : ℝ) (e c)).indicator (fun _ => (1 : ℝ)) t
  have hterm (c : Fin m) : Integrable
      (fun t => P.val c*(Ioo (0 : ℝ) (e c)).indicator (fun _ => (1 : ℝ)) t) volume := by
    apply Integrable.const_mul
    exact (integrable_indicator_iff measurableSet_Ioo).2
      (integrableOn_const (by simp [Real.volume_Ioo]))
  have hg : IntegrableOn g (Ioi (0 : ℝ)) volume :=
    (integrable_finsetSum Finset.univ (fun c _ => hterm c)).restrict
  have hintegral : (∫ t in Ioi (0 : ℝ), g t) = ∑ c, P.val c*max (e c) 0 := by
    change (∫ t in Ioi (0 : ℝ), ∑ c, P.val c*(Ioo (0 : ℝ) (e c)).indicator (fun _ => (1 : ℝ)) t) = _
    rw [integral_finsetSum Finset.univ (fun c _ => (hterm c).restrict)]
    apply Finset.sum_congr rfl
    intro c _
    rw [integral_const_mul,integral_indicator_const (1 : ℝ) measurableSet_Ioo]
    have hi : Ioo (0 : ℝ) (e c) ∩ Ioi 0 = Ioo 0 (e c) :=
      Set.inter_eq_left.mpr (fun _ ht => ht.1)
    simp only [smul_eq_mul,mul_one,measureReal_def,
      Measure.restrict_apply measurableSet_Ioo,hi,Real.volume_Ioo,sub_zero,ENNReal.toReal_ofReal']
  have hpoint : ∀ t, 0 < t → g t ≤ lowerCut σ P d o v t := by
    intro t ht
    have hp := h.child_0 n m σ P d o v t ht.le
    obtain ⟨j,hj,hja,hjfirst⟩ := hp.2.2.2.2.2.2.1
    have hjdist : distance d (.inr o) (.inr j) ≤ t := le_of_not_gt hj
    rw [hja]
    change (∑ c, P.val c*(Ioo (0 : ℝ) (e c)).indicator (fun _ => (1 : ℝ)) t) ≤
      ∑ c, if prefers (σ v) j c then P.val c else 0
    apply Finset.sum_le_sum
    intro c _
    by_cases he : t < e c
    · have hbetter : prefers (σ v) j c := by
        change (σ v) c < (σ v) j
        by_contra hn
        have horder : (σ v) j ≤ (σ v) c := le_of_not_gt hn
        have hdcj : distance d (.inl v) (.inr c) ≤ distance d (.inl v) (.inr j) := by
          rcases eq_or_lt_of_le horder with heq|hlt
          · have hc : j=c := (σ v).injective heq
            simpa [hc]
          · exact hd v c j hlt
        have htriangle := (h.child_2 n m d).2.2.1 (.inl v) (.inr o) (.inr j)
        dsimp [e] at he
        linarith
      simp only [Set.indicator_of_mem (show t ∈ Ioo (0 : ℝ) (e c) from ⟨ht,he⟩),
        mul_one,hbetter,ite_true]
      exact le_rfl
    · have hnot : t ∉ Ioo (0 : ℝ) (e c) := fun hmem => he hmem.2
      simp only [Set.indicator_of_notMem hnot,mul_zero]
      split_ifs
      · exact P.property.1 c
      · exact le_rfl
  have hint := (h.child_1 n m σ P d o v).1
  calc
    (∑ c, P.val c*distance d (.inl v) (.inr c))-distance d (.inl v) (.inr o) =
        ∑ c, P.val c*e c := by
      simp [e,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,P.property.2]
    _ ≤ ∑ c, P.val c*max (e c) 0 :=
      Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (P.property.1 c)
    _ = ∫ t in Ioi (0 : ℝ), g t := hintegral.symm
    _ ≤ tailIntegral (lowerCut σ P d o v) := by
      apply integral_mono_ae hg hint
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hpoint t ht

#print axioms from_children
end MetricDistortion.Contracts.Geometry_MetricTail
