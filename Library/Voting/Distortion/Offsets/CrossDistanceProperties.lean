import Voting.Distortion.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Offsets_CrossDistanceProperties

private theorem suffix_finite {m : ℕ} (r : Ranking m) (x : Fin m → ℝ) (c : Fin m) :
    ({t : ℝ | ∃ j, r j ≤ r c ∧ t = x j}).Finite := by
  apply (Set.finite_range x).subset
  rintro t ⟨j, _, rfl⟩
  exact ⟨j, rfl⟩

private theorem suffix_attained {m : ℕ} (r : Ranking m) (x : Fin m → ℝ) (c : Fin m) :
    ∃ j, r j ≤ r c ∧ sOffset r x c = x j := by
  have hne : ({t : ℝ | ∃ j, r j ≤ r c ∧ t = x j}).Nonempty :=
    ⟨x c, c, le_rfl, rfl⟩
  exact hne.csInf_mem (suffix_finite r x c)

private theorem delta_bound {m : ℕ} (r : Ranking m) (x : Fin m → ℝ)
    (i j : Fin m) (hji : r j ≤ r i) : x i-x j ≤ deltaOffset r x := by
  have hf : ({t : ℝ | ∃ i j, r j ≤ r i ∧ t = x i-x j}).Finite := by
    apply (Set.finite_range fun ij : Fin m × Fin m => x ij.1-x ij.2).subset
    rintro t ⟨i, j, _, rfl⟩
    exact ⟨(i,j),rfl⟩
  exact le_csSup hf.bddAbove ⟨i,j,hji,rfl⟩

theorem from_children (h : Needs) : Statement := by
  intro n m σ x hx
  dsimp
  have hs (v : Fin n) := h.child_0 m (σ v) x hx
  have hxc (v : Fin n) (c : Fin m) : x c ≤ deltaOffset (σ v) x+sOffset (σ v) x c := by
    obtain ⟨j,hj,he⟩ := suffix_attained (σ v) x c
    have hd := delta_bound (σ v) x c j hj
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro v c
    exact add_nonneg (div_nonneg (hs v).2 (by norm_num)) ((hs v).1 c).1
  · intro v v' c c'
    have h1 := ((hs v).1 c).2
    have h2 := hxc v' c
    have h3 := ((hs v).1 c').1
    have h4 := ((hs v').1 c').1
    linarith
  · intro v a b hab
    obtain ⟨j,hjb,he⟩ := suffix_attained (σ v) x b
    have hja : (σ v) j ≤ (σ v) a := hjb.trans (le_of_lt hab)
    have hbd : BddBelow {t : ℝ | ∃ j, (σ v) j ≤ (σ v) a ∧ t = x j} := by
      refine ⟨0, ?_⟩
      rintro t ⟨j,_,rfl⟩
      exact hx j
    have hh : sOffset (σ v) x a ≤ x j := csInf_le hbd ⟨j,hja,rfl⟩
    linarith

#print axioms from_children
end MetricDistortion.Contracts.Offsets_CrossDistanceProperties
