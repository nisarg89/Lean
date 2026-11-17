import Voting.Distortion.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Geometry_AverageAndDistortion

theorem from_children (h : Needs) : Statement := by
  intro n m hn hm σ P R hR H
  unfold distortion
  apply iSup_le
  intro d
  obtain ⟨o,_,hmin⟩ := (Finset.univ : Finset (Fin m)).exists_min_image (sc d.val)
    ⟨⟨0,hm⟩,Finset.mem_univ _⟩
  have ho : Optimal d.val o := fun c => hmin c (Finset.mem_univ c)
  have hopt : optimum d.val = sc d.val o := by
    apply IsLeast.csInf_eq
    refine ⟨⟨o,rfl⟩,?_⟩
    intro z hz
    obtain ⟨c,rfl⟩ := hz
    exact ho c
  have hsc : ∀ c : Fin m, 0 ≤ sc d.val c := by
    intro c
    unfold sc avg
    exact div_nonneg (Finset.sum_nonneg fun v _ =>
      (h.child_1 n m d.val).2.2.2 (.inl v) (.inr c)) (Nat.cast_nonneg n)
  have hcost : 0 ≤ expectedCost d.val P :=
    Finset.sum_nonneg fun c _ => mul_nonneg (P.property.1 c) (hsc c)
  have hb := H d.val d.property o ho
  rw [hopt]
  by_cases hz : sc d.val o=0
  · have he : expectedCost d.val P=0 := le_antisymm (by simpa [hz] using hb) hcost
    rw [he,hz,h.child_0.1]
    exact ENNReal.one_le_ofReal.mpr hR
  · have hpos : 0 < sc d.val o := lt_of_le_of_ne (hsc o) (Ne.symm hz)
    rw [ratio,if_neg hz]
    exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ hpos).2 hb)

#print axioms from_children
end MetricDistortion.Contracts.Geometry_AverageAndDistortion
