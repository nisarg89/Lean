import Voting.Distortion.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Geometry_CommonCharge
theorem from_children (h : Needs) : Statement := by
  intro K w D hK hw
  obtain ⟨j0, _, hj0⟩ := Finset.exists_min_image Finset.univ K (Finset.univ_nonempty)
  have hmin : ∀ j, K j0 ≤ K j := fun j => hj0 j (Finset.mem_univ j)
  refine ⟨j0, hmin, ?_⟩
  intro r hr
  rcases hw with ⟨hC,hb,hphi,hlam,hl0,hl1,hroots,hcover,hmeasure,htau,ht0,hlocal⟩
  by_cases hbr : w.b ≤ r
  · exact ⟨j0, Or.inr ⟨hbr,hr.2⟩, le_rfl⟩
  · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (hcover ⟨hr.1,le_of_lt (lt_of_not_ge hbr)⟩)
    refine ⟨j,Or.inl hj,?_⟩
    have hs : phi D r ≤ mu D :=
      ((h.child_0 D).1 hr hb (le_of_lt (lt_of_not_ge hbr))).trans hphi
    exact mul_le_mul_of_nonneg_right (hmin j) (sub_nonneg.mpr hs)
#print axioms from_children
end MetricDistortion.Contracts.Geometry_CommonCharge
