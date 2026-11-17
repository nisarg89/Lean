import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Computation_RunRules
theorem proved : Statement := by
  have trans (prog : Program) {k l : ℕ} {s u t : MachineState}
      (h₁ : Runs prog k s u) (h₂ : Runs prog l u t) : Runs prog (k+l) s t := by
    induction h₁ with
    | zero => simpa using h₂
    | @succ k s mid u hs htail ih =>
      simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using Runs.succ hs (ih h₂)
  refine ⟨fun prog k l s u t h₁ h₂ => trans prog h₁ h₂, ?_⟩
  intro prog Inv Done rank K hstep s hs
  have loop : ∀ r : ℕ, ∀ s, rank s=r → Inv s →
      ∃ k t, Runs prog k s t ∧ Done t ∧ k ≤ K*(r+1) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro s hr hs
      obtain ⟨k,u,hk,hcost,hnext⟩ := hstep s hs
      rcases hnext with hdone | ⟨hinv,hrank⟩
      · refine ⟨k,u,hk,hdone,?_⟩
        calc
          k ≤ K := hcost
          _ ≤ K*(r+1) := by nlinarith
      · obtain ⟨l,t,hl,hdone,hlcost⟩ := ih (rank u) (by omega) u rfl hinv
        refine ⟨k+l,t,trans prog hk hl,hdone,?_⟩
        have hsmall : rank u+1 ≤ r := by omega
        calc
          k+l ≤ K+K*(rank u+1) := Nat.add_le_add hcost hlcost
          _ ≤ K+K*r := Nat.add_le_add_left (Nat.mul_le_mul_left K hsmall) K
          _ = K*(r+1) := by ring
  exact loop (rank s) s rfl hs
#print axioms proved
end MetricDistortion.Contracts.Computation_RunRules
