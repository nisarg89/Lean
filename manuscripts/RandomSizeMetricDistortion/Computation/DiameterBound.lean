import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Computation_DiameterBound

theorem from_children (h : Needs) : Statement := by
  intro n m hn hm σ d hd o ho hnd c
  letI : PseudoMetricSpace (Fin n ⊕ Fin m) := d
  by_cases hco : c = o
  · subst c
    have hs : 0 ≤ sc d o := by
      exact div_nonneg (Finset.sum_nonneg (fun v _ => dist_nonneg)) (Nat.cast_nonneg n)
    simpa [distance] using (mul_nonneg (by positivity : 0 ≤ (2 : ℝ)*n) hs)
  have hnot : ¬ ∀ v, prefers (σ v) o c := fun hc => hnd c ⟨o,hc⟩
  obtain ⟨v,hv⟩ := not_forall.mp hnot
  have hpref : prefers (σ v) c o := by
    have hle : σ v o ≤ σ v c := le_of_not_gt hv
    have hne : σ v o ≠ σ v c := fun heq => hco ((σ v).injective heq).symm
    exact lt_of_le_of_ne hle hne
  have hvc := hd v c o hpref
  have htriangle : distance d (.inr c) (.inr o) ≤
      distance d (.inl v) (.inr c)+distance d (.inl v) (.inr o) := by
    have ht := dist_triangle (Sum.inr c : Fin n ⊕ Fin m) (.inl v) (.inr o)
    simpa only [distance,dist_comm] using ht
  have hsingle : distance d (.inl v) (.inr o) ≤
      ∑ u, distance d (.inl u) (.inr o) :=
    Finset.single_le_sum (fun u _ => dist_nonneg) (Finset.mem_univ v)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hsum : (n : ℝ)*sc d o = ∑ u, distance d (.inl u) (.inr o) := by
    dsimp [sc,avg]
    field_simp [hn0]
  have hsym : distance d (.inr o) (.inr c) = distance d (.inr c) (.inr o) := by
    exact dist_comm _ _
  rw [hsym]
  linarith

#print axioms from_children
end MetricDistortion.Contracts.Computation_DiameterBound
