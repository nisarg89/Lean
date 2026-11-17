import Voting.Distortion.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Offsets_MetricDomination

theorem from_children (h : Needs) : Statement := by
  intro n m hn hm σ P d hcons o hopt
  let x := fun c => distance d (.inr o) (.inr c)
  dsimp
  obtain ⟨hself,hsym,htri,hnonneg⟩ := h.child_1 n m d
  have hcost_order (v : Fin n) (a b : Fin m) (hab : (σ v) b ≤ (σ v) a) :
      distance d (.inl v) (.inr a) ≤ distance d (.inl v) (.inr b) := by
    rcases lt_or_eq_of_le hab with hh | hh
    · exact hcons v a b hh
    · have he : b = a := (σ v).injective hh
      simp [he]
  have hpoint (v : Fin n) (c : Fin m) :
      distance d (.inl v) (.inr c)-distance d (.inl v) (.inr o) ≤ sOffset (σ v) x c := by
    apply le_csInf (show ({t : ℝ | ∃ j, (σ v) j ≤ (σ v) c ∧ t = x j}).Nonempty from
      ⟨x c,c,le_rfl,rfl⟩)
    rintro t ⟨j,hj,rfl⟩
    have hcj := hcost_order v c j hj
    have ht := htri (.inl v) (.inr o) (.inr j)
    dsimp [x]
    linarith
  have hdelta (v : Fin n) : deltaOffset (σ v) x ≤ 2*distance d (.inl v) (.inr o) := by
    apply csSup_le (show ({t : ℝ | ∃ i j, (σ v) j ≤ (σ v) i ∧ t = x i-x j}).Nonempty from
      ⟨0,o,o,le_rfl,(sub_self _).symm⟩)
    rintro t ⟨i,j,hji,rfl⟩
    have hij := hcost_order v i j hji
    have hi := htri (.inr o) (.inl v) (.inr i)
    have hj := htri (.inl v) (.inr o) (.inr j)
    have ho := hsym (.inr o) (.inl v)
    dsimp [x]
    linarith
  have hcandidate (c : Fin m) : sc d c-sc d o ≤ avg (fun v => sOffset (σ v) x c) := by
    have hh := div_le_div_of_nonneg_right
      (Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hpoint v c))
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    simpa [sc,avg,Finset.sum_sub_distrib,sub_div] using hh
  constructor
  · have hh := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (hcandidate c) (P.property.1 c))
    have hleft : (∑ c, P.val c*(sc d c-sc d o)) = expectedCost d P-sc d o := by
      simp_rw [mul_sub,Finset.sum_sub_distrib]
      rw [← Finset.sum_mul,P.property.2,one_mul]
      rfl
    have hright : (∑ c, P.val c*avg (fun v => sOffset (σ v) x c)) = loss σ P x := by
      unfold loss avg
      simp_rw [← mul_div_assoc]
      rw [← Finset.sum_div]
      congr 1
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    rw [hleft,hright] at hh
    exact hh
  · have hh := div_le_div_of_nonneg_right
      (Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hdelta v))
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    unfold scale sc avg
    rw [← Finset.mul_sum] at hh
    convert hh using 1 <;> ring

#print axioms from_children
end MetricDistortion.Contracts.Offsets_MetricDomination
