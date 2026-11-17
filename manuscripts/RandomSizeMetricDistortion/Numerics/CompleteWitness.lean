import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Numerics_CompleteWitness

theorem from_children (h : Needs) : Statement := by
  have hf : ∀ j, FiniteFamily j := by
    intro j
    fin_cases j
    · exact h.child_8
    · exact h.child_9
    · exact h.child_10
    · exact h.child_11
    · exact h.child_12
    · exact h.child_13
    · exact h.child_14
    · exact h.child_15
    · exact h.child_16
  have hc : ∀ j, StrongCrossing j := by
    intro j
    fin_cases j
    · exact h.child_17
    · exact h.child_18
    · exact h.child_19
    · exact h.child_20
    · exact h.child_21
    · exact h.child_22
    · exact h.child_23
    · exact h.child_24
    · exact h.child_25
  refine ⟨h.child_0.1, ?_, h.child_6⟩
  intro D hD
  have hs := h.child_0.2 D hD
  refine ⟨h.child_7.2.1, h.child_7.2.2, ?_, h.child_2.1,
    h.child_2.2.2.1, h.child_2.2.2.2.1, h.child_1.2.1, h.child_1.1,
    h.child_3, h.child_2.2.1, ?_, ?_⟩
  · change phi D bStar ≤ mu D
    rw [hs.1, hs.2.2.1]
    exact h.child_7.1
  · intro j
    exact (h.child_2.2.2.2.2 j).1
  · intro j r hr a p A ha hap hpA hA
    have hpnon : 0 ≤ p := ha.trans (hap.trans (min_le_left _ _))
    have hple : p ≤ 1 := hpA.trans hA
    by_cases hp0 : p = 0
    · exact h.child_4 j D hD r hr p (by simp [hp0]) a A ha hap hpA hA
    by_cases hp1 : p = 1
    · exact h.child_4 j D hD r hr p (by simp [hp1]) a A ha hap hpA hA
    exact h.child_5 hf hc D hD j r hr p
      ⟨lt_of_le_of_ne hpnon (Ne.symm hp0), lt_of_le_of_ne hple hp1⟩
      a A ha hap hpA hA
#print axioms from_children
end MetricDistortion.Contracts.Numerics_CompleteWitness
