import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Lower_PermutationInvariance

theorem from_children (h : Needs) : Statement := by
  intro n N k hn hk hkN z hz D σ hσ g hg P Q hQ c
  have hgs : g.symm 0 = 0 := by
    apply g.injective
    simp [hg]
  let T : Ranking (N+1) ≃ Ranking (N+1) :=
    {toFun := fun r => g.symm.trans r
     invFun := fun r => g.trans r
     left_inv := by intro r; ext j; simp [Equiv.trans_apply]
     right_inv := by intro r; ext j; simp [Equiv.trans_apply]}
  have hT0 (r : Ranking (N+1)) : T r 0 = r 0 := by
    simp [T,Equiv.trans_apply,hgs]
  have hTi0 (r : Ranking (N+1)) : T.symm r 0 = r 0 := by
    simp [T,Equiv.trans_apply,hg]
  have hbelow (r : Ranking (N+1)) : below r Q c = below (T r) P (g c) := by
    have he := Equiv.sum_comp g (fun j => if r (g.symm j) < r c then P.val j else 0)
    simpa [below,mass,prefers,T,Equiv.trans_apply,hQ] using he
  have hcompare (r : Ranking (N+1)) : compare D r Q c = compare D (T r) P (g c) := by
    have hl := (h.child_0 (N+1) D r Q c).1
    have hr := (h.child_0 (N+1) D (T r) P (g c)).1
    change compare D r Q c = ∫ s in (0 : ℝ)..1, phi D (below r Q c+s*Q.val c) at hl
    change compare D (T r) P (g c) =
      ∫ s in (0 : ℝ)..1, phi D (below (T r) P (g c)+s*P.val (g c)) at hr
    rw [hl,hr,hbelow,hQ]
  have hsum (j : ℕ) :
      (∑ r ∈ Finset.univ.filter (fun r : Ranking (N+1) => (r 0).val = j), compare D r Q c) =
      ∑ r ∈ Finset.univ.filter (fun r : Ranking (N+1) => (r 0).val = j), compare D r P (g c) := by
    apply Finset.sum_bij (fun r hr => T r)
    · intro r hr
      simpa [hT0] using hr
    · intro r hr s hs he
      exact T.injective he
    · intro r hr
      refine ⟨T.symm r,?_,T.apply_symm_apply r⟩
      simpa [hTi0] using hr
    · intro r hr
      exact hcompare r
  have hleft := h.child_1 n N k hn hk hkN z hz σ hσ (fun r => compare D r Q c)
  have hright := h.child_1 n N k hn hk hkN z hz σ hσ (fun r => compare D r P (g c))
  unfold score
  rw [hleft,hright,hsum k,hsum N]

#print axioms from_children
end MetricDistortion.Contracts.Lower_PermutationInvariance
