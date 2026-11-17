import Voting.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Model_Lotteries
theorem proved : Statement := by
  intro m P
  have hc (c : Fin m) : P.val c ∈ Icc (0 : ℝ) 1 := by
    refine ⟨P.property.1 c, ?_⟩
    have := Finset.single_le_sum (s := Finset.univ) (f := P.val)
      (fun i _ => P.property.1 i) (Finset.mem_univ c)
    simpa [P.property.2] using this
  refine ⟨hc, ?_, P.property.2⟩
  intro H
  refine ⟨?_, ?_⟩
  · apply Finset.sum_nonneg
    intro c _
    by_cases hc : c ∈ H
    · simpa [hc] using P.property.1 c
    · simp [hc]
  calc
    mass P H ≤ ∑ c, P.val c := Finset.sum_le_sum (fun c _ => by
      split_ifs <;> simp_all [P.property.1 c])
    _ = 1 := P.property.2
#print axioms proved
end MetricDistortion.Contracts.Model_Lotteries
