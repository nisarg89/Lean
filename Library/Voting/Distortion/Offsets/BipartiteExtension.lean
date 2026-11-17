import Voting.Distortion.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Offsets_BipartiteExtension

/- The finite cross-distance matrix is embedded in a sup-norm space.
The coordinate at candidate c certifies equality of the cross distance;
the three-edge hypothesis certifies the upper bound at every coordinate. -/
theorem from_children (_h : Needs) : Statement := by
  intro n m hn hm w hw hthree
  let cc : Fin m → Fin m → ℝ := fun c j =>
    if c = j then 0 else sInf (Set.range fun v => w v c+w v j)
  have hne (c j : Fin m) : (Set.range fun v => w v c+w v j).Nonempty := by
    exact ⟨w ⟨0,hn⟩ c+w ⟨0,hn⟩ j, ⟨0,hn⟩, rfl⟩
  have hb (c j : Fin m) : BddBelow (Set.range fun v => w v c+w v j) := by
    refine ⟨0, ?_⟩
    rintro t ⟨v,rfl⟩
    exact add_nonneg (hw v c) (hw v j)
  have hlo (v : Fin n) (c j : Fin m) : w v j-w v c ≤ cc c j := by
    by_cases hc : c = j
    · subst j
      simp [cc]
    · dsimp [cc]
      rw [if_neg hc]
      apply le_csInf (hne c j)
      rintro t ⟨v',rfl⟩
      linarith [hthree v v' j c]
  have hup (v : Fin n) (c j : Fin m) : cc c j ≤ w v c+w v j := by
    by_cases hc : c = j
    · subst j
      simpa [cc] using add_nonneg (hw v c) (hw v c)
    · dsimp [cc]
      rw [if_neg hc]
      exact csInf_le (hb c j) ⟨v,rfl⟩
  let e : Fin n ⊕ Fin m → (Fin m → ℝ) := Sum.elim w cc
  let d : Metric n m := PseudoMetricSpace.induced e inferInstance
  refine ⟨d, ?_⟩
  intro v c
  change dist (e (.inl v)) (e (.inr c)) = w v c
  apply le_antisymm
  · apply (dist_pi_le_iff (hw v c)).2
    intro j
    change dist (w v j) (cc c j) ≤ w v c
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hlo v c j, hup v c j]
  · have he := dist_le_pi_dist (e (.inl v)) (e (.inr c)) c
    simpa [e, cc, Real.dist_eq, abs_of_nonneg (hw v c)] using he

#print axioms from_children
end MetricDistortion.Contracts.Offsets_BipartiteExtension
