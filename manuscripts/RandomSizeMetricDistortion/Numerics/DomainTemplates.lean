import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Numerics_DomainTemplates

theorem proved : Statement := by
  intro a p A r h
  rcases h with ⟨ha, hap, hpA, hA⟩
  have hap' : a ≤ p := hap.trans (min_le_left _ _)
  have har : a ≤ r := hap.trans (min_le_right _ _)
  have haA : a ≤ A := hap'.trans hpA
  by_cases hr : r < A
  · rw [if_pos hr]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · rintro ⟨⟨hz, hz1⟩, hza, hmin⟩
      exact ⟨(le_min_iff.mp hza).1, hz1⟩
    · rintro ⟨haz, hz1⟩
      exact ⟨⟨ha.trans haz,hz1⟩,le_min haz har, (min_le_right z r).trans_lt hr⟩
  · rw [if_neg hr]
    have hAr : A ≤ r := le_of_not_gt hr
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_Icc, Set.mem_Ico]
    constructor
    · rintro ⟨⟨hz,hz1⟩, hza, hmin⟩
      refine ⟨(le_min_iff.mp hza).1, ?_⟩
      by_contra hnot
      exact (not_lt_of_ge (le_min (le_of_not_gt hnot) hAr)) hmin
    · rintro ⟨haz,hzA⟩
      exact ⟨⟨ha.trans haz,hzA.le.trans hA⟩,le_min haz har,
        (min_le_left z r).trans_lt hzA⟩
#print axioms proved
end MetricDistortion.Contracts.Numerics_DomainTemplates
