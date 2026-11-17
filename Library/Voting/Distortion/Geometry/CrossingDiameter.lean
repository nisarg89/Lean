import Voting.Distortion.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Geometry_CrossingDiameter
theorem from_children (h : Needs) : Statement := by
  intro n m σ P d hd o v q t s ht hs
  letI : PseudoMetricSpace (Fin n ⊕ Fin m) := d
  have endpoint {c d : Fin m} (hcd : (σ v) c < (σ v) d) : below (σ v) P c+P.val c ≤ below (σ v) P d := by
    calc
      _ = ∑ j, ((if prefers (σ v) c j then P.val j else 0)+(if j=c then P.val j else 0)) := by
        simp [below,mass,Finset.sum_add_distrib]
      _ ≤ ∑ j, if prefers (σ v) d j then P.val j else 0 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : j=c
        · subst j
          simp [prefers,hcd]
        · simp only [hj,ite_false,add_zero]
          by_cases hsmall : prefers (σ v) c j
          · have hlarge : prefers (σ v) d j := lt_trans hsmall hcd
            simp [hsmall,hlarge]
          · simp only [hsmall,ite_false]
            split_ifs
            · exact P.property.1 j
            · exact le_rfl
      _ = below (σ v) P d := rfl
  have bound (t s : ℝ) (ht : t ∈ crossing σ P d o v q)
      (hs : s ∈ crossing σ P d o v q) : s-t ≤ 2*distance d (.inl v) (.inr o) := by
    obtain ⟨_,_,_,_,_,_,hj, _⟩ := h.child_0 n m σ P d o v t ht.1
    obtain ⟨j,hjnot,hja,hjmin⟩ := hj
    obtain ⟨_,_,_,_,_,_,_,hc⟩ := h.child_0 n m σ P d o v s hs.1
    have hnonneg : 0 ≤ lowerCut σ P d o v t := by
      rw [hja]
      unfold below mass
      exact Finset.sum_nonneg (fun i _ => by split_ifs; exact P.property.1 i; exact le_rfl)
    have hposA : 0 < upperCut σ P d o v s :=
      lt_of_le_of_lt (le_trans hnonneg ht.2.1) hs.2.2
    rcases hc with hc | ⟨c,hcmark,hcp,hcA⟩
    · linarith
    have hrank : (σ v) j ≤ (σ v) c := by
      by_contra hn
      have hh := endpoint (lt_of_not_ge hn)
      rw [← hja, ← hcA] at hh
      linarith [ht.2.1,hs.2.2]
    have hvcompare : distance d (.inl v) (.inr c) ≤ distance d (.inl v) (.inr j) := by
      rcases eq_or_lt_of_le hrank with he | he
      · have hjc : j = c := (σ v).injective he
        simpa [hjc]
      · exact hd v c j he
    have hjdist : distance d (.inr o) (.inr j) ≤ t := le_of_not_gt hjnot
    have hcdist : s < distance d (.inr o) (.inr c) := hcmark
    have h1 := dist_triangle (Sum.inr o : Fin n ⊕ Fin m) (.inl v) (.inr c)
    have h2 := dist_triangle (Sum.inl v : Fin n ⊕ Fin m) (.inr o) (.inr j)
    have hsym : distance d (.inr o) (.inl v) = distance d (.inl v) (.inr o) := dist_comm _ _
    change distance d (.inr o) (.inr c) ≤ distance d (.inr o) (.inl v) + distance d (.inl v) (.inr c) at h1
    change distance d (.inl v) (.inr j) ≤ distance d (.inl v) (.inr o) + distance d (.inr o) (.inr j) at h2
    linarith
  exact abs_le.mpr ⟨by linarith [bound s t hs ht], bound t s ht hs⟩
#print axioms from_children
end MetricDistortion.Contracts.Geometry_CrossingDiameter
