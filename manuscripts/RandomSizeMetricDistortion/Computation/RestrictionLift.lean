import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Computation_RestrictionLift

theorem from_children (h : Needs) : Statement := by
  intro n m hn hm σ R
  have hret (c : Fin R.count) : ¬ Dominated σ (R.embed c) := by
    have hc : R.embed c ∈ Set.range R.embed := ⟨c,rfl⟩
    rw [R.range_eq] at hc
    exact hc
  refine ⟨?_,?_⟩
  · intro c
    rintro ⟨b,hb⟩
    apply hret c
    refine ⟨R.embed b,?_⟩
    intro v
    exact (R.preserves v b c).1 (hb v)
  · intro d hcons
    let E : Fin n ⊕ Fin R.count → Fin n ⊕ Fin m := Sum.map id R.embed
    let d' : Metric n R.count := PseudoMetricSpace.induced E d
    have hdist (v : Fin n) (c : Fin R.count) :
        distance d' (.inl v) (.inr c) = distance d (.inl v) (.inr (R.embed c)) := rfl
    have hcost (c : Fin R.count) : sc d' c = sc d (R.embed c) := rfl
    have hminimum : optimum d' = optimum d := by
      obtain ⟨R0,hR0⟩ := h.child_0 n m hn hm σ
      have hrange : Set.range (fun c => sc d (R.embed c)) = Set.range (fun c => sc d (R0.embed c)) := by
        ext t
        constructor
        · rintro ⟨c,rfl⟩
          have hc : R.embed c ∈ Set.range R0.embed := by
            rw [R0.range_eq]
            exact hret c
          obtain ⟨b,hb⟩ := hc
          exact ⟨b,congrArg (sc d) hb⟩
        · rintro ⟨c,rfl⟩
          have hc0 : ¬ Dominated σ (R0.embed c) := by
            have hc : R0.embed c ∈ Set.range R0.embed := ⟨c,rfl⟩
            rw [R0.range_eq] at hc
            exact hc
          have hc : R0.embed c ∈ Set.range R.embed := by rw [R.range_eq]; exact hc0
          obtain ⟨b,hb⟩ := hc
          exact ⟨b,congrArg (sc d) hb⟩
      calc
        optimum d' = sInf (Set.range fun c => sc d (R.embed c)) := by
          rfl
        _ = sInf (Set.range fun c => sc d (R0.embed c)) := congrArg sInf hrange
        _ = optimum d := hR0 d hcons
    refine ⟨d',?_,hcost,hminimum,?_⟩
    · intro v a b hab
      rw [hdist,hdist]
      exact hcons v (R.embed a) (R.embed b) ((R.preserves v a b).1 hab)
    · intro P Q hLift
      calc
        expectedCost d' P = ∑ c, Q.val (R.embed c)*sc d (R.embed c) := by
          unfold expectedCost
          apply Finset.sum_congr rfl
          intro c hc
          rw [hcost,hLift.1 c]
        _ = ∑ b ∈ Finset.univ.filter (fun b => b ∈ Set.range R.embed), Q.val b*sc d b := by
          apply Finset.sum_bij (fun c hc => R.embed c)
          · intro c hc
            simp only [Finset.mem_filter,Finset.mem_univ,true_and]
            exact ⟨c,rfl⟩
          · intro c hc c' hc' he
            exact R.embed.injective he
          · intro b hb
            obtain ⟨c,hc⟩ := (Finset.mem_filter.mp hb).2
            exact ⟨c,Finset.mem_univ _,hc⟩
          · intro c hc
            rfl
        _ = expectedCost d Q := by
          unfold expectedCost
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro b hb
          by_cases hbr : b ∈ Set.range R.embed
          · simp [hbr]
          · simp [hbr,hLift.2 b hbr]

#print axioms from_children
end MetricDistortion.Contracts.Computation_RestrictionLift
