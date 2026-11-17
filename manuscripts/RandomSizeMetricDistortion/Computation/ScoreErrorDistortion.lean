import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Computation_ScoreErrorDistortion
theorem from_children (h : Needs) : Statement := by
  intro n m hn hm D hD σ hnd Q δ hδ hs
  letI : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  apply h.child_3 n m hn hm σ Q (213609/100000+32*n*δ)
  · have hnon : 0 ≤ 32*(n : ℝ)*δ := by positivity
    linarith
  · intro d hd o ho
    have hcost := (h.child_0 D fixedWitness (h.child_1.2.1 D hD)).2 16 h.child_1.2.2
      n m hn hm σ Q δ hδ hs d hd o ho
    have hmax : sSup (Set.range fun c => distance d (.inr o) (.inr c)) ≤ 2*n*sc d o := by
      apply csSup_le (Set.range_nonempty _)
      rintro x ⟨c,rfl⟩
      exact h.child_2 n m hn hm σ d hd o ho hnd c
    calc
      expectedCost d Q ≤ (1+2*fixedWitness.C0)*sc d o +
        16*δ*sSup (Set.range fun c => distance d (.inr o) (.inr c)) := hcost
      _ ≤ (1+2*fixedWitness.C0)*sc d o +16*δ*(2*n*sc d o) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hmax (by positivity : 0 ≤ 16*δ))
      _ = _ := by dsimp [fixedWitness,cStar]; ring
#print axioms from_children
end MetricDistortion.Contracts.Computation_ScoreErrorDistortion
