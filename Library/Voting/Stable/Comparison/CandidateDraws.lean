import Voting.Stable.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Comparison_CandidateDraws
theorem from_children (h : Needs) : Statement := by
  intro m D r P c
  have hb : 0 ≤ below r P c := by
    unfold below mass
    apply Finset.sum_nonneg
    intro j _
    by_cases hj : prefers r c j
    · simpa [Set.mem_setOf_eq,hj] using P.property.1 j
    · simp [Set.mem_setOf_eq,hj]
  have hz : 0 ≤ P.val c := P.property.1 c
  have htotal : below r P c+P.val c ≤ 1 := by
    calc
      below r P c+P.val c = ∑ j, ((if prefers r c j then P.val j else 0)+
        (if j=c then P.val j else 0)) := by simp [below,mass,Finset.sum_add_distrib]
      _ ≤ ∑ j, P.val j := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : j=c
        · subst j
          simp [prefers]
        · simp only [hj,ite_false,add_zero]
          split_ifs <;> simp_all [P.property.1 j]
      _ = 1 := P.property.2
  have heq : compare D r P c = ambientCompare D r P.val c := by
    rw [h.child_1 m D r P c]
    unfold ambientCompare
    change (∑' k, drawWeight D k*(∫ s in (0 : ℝ)..1,
      (below r P c+s*P.val c)^(k+1))) = _
    exact (h.child_4 D (below r P c) (P.val c) hb hz htotal).symm
  refine ⟨heq, ?_, (h.child_2 m D r c).1, (h.child_2 m D r c).2⟩
  intro hzpos
  rw [heq]
  exact h.child_3 D (below r P c) (P.val c) hb hzpos htotal
#print axioms from_children
end MetricDistortion.Contracts.Comparison_CandidateDraws
