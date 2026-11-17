import Voting.Distortion.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Model_OffsetDefinitions

theorem proved : Statement := by
  intro m r x hx
  have hs : ∀ c, 0 ≤ sOffset r x c ∧ sOffset r x c ≤ x c := by
    intro c
    have hne : ({t : ℝ | ∃ j, r j ≤ r c ∧ t = x j}).Nonempty :=
      ⟨x c, c, le_rfl, rfl⟩
    have hbd : BddBelow {t : ℝ | ∃ j, r j ≤ r c ∧ t = x j} := by
      refine ⟨0, ?_⟩
      rintro t ⟨j, _, rfl⟩
      exact hx j
    constructor
    · exact le_csInf hne (by rintro t ⟨j, _, rfl⟩; exact hx j)
    · exact csInf_le hbd ⟨c, le_rfl, rfl⟩
  refine ⟨hs, ?_⟩
  by_cases hm : m = 0
  · subst m
    simp [deltaOffset]
  · let c : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
    have hfinite : ({t : ℝ | ∃ i j, r j ≤ r i ∧ t = x i-x j}).Finite := by
      apply (Set.finite_range fun ij : Fin m × Fin m => x ij.1-x ij.2).subset
      rintro t ⟨i, j, _, rfl⟩
      exact ⟨(i,j), rfl⟩
    exact le_csSup hfinite.bddAbove ⟨c, c, le_rfl, (sub_self _).symm⟩

#print axioms proved
end MetricDistortion.Contracts.Model_OffsetDefinitions
