import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Lower_ReferenceLotteries

theorem from_children (_h : Needs) : Statement := by
  intro N hN t ht
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let p : Fin (N+1) → ℝ := fun c => if c.val = 0 then 1-t else t/N
  have hp : ∀ c, 0 ≤ p c := by
    intro c
    dsimp [p]
    split_ifs
    · exact sub_nonneg.mpr ht.2
    · exact div_nonneg ht.1 hNr.le
  have htotal : ∑ c, p c = 1 := by
    rw [Fin.sum_univ_succ]
    simp only [p, Fin.val_zero, ↓reduceIte, Fin.val_succ, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
    <;> ring
  exact ⟨⟨p,hp,htotal⟩,fun c => rfl⟩

#print axioms from_children
end MetricDistortion.Contracts.Lower_ReferenceLotteries
