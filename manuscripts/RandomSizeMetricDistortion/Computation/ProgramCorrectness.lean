import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Computation_ProgramCorrectness

private theorem singleton_distortion {n m : ℕ} (hm : m = 1)
    (σ : Profile n m) (Q : Lottery m) : distortion σ Q ≤ 1 := by
  let c0 : Fin m := ⟨0,by omega⟩
  have hc (c : Fin m) : c = c0 := by
    apply Fin.ext
    have := c.isLt
    dsimp [c0]
    omega
  unfold distortion
  refine iSup_le fun d => ?_
  have he : expectedCost d.val Q = sc d.val c0 := by
    calc
      expectedCost d.val Q = ∑ c, Q.val c * sc d.val c0 := by
        unfold expectedCost
        apply Finset.sum_congr rfl
        intro c hmem
        rw [hc c]
      _ = (∑ c, Q.val c) * sc d.val c0 := by rw [Finset.sum_mul]
      _ = sc d.val c0 := by rw [Q.property.2,one_mul]
  have ho : optimum d.val = sc d.val c0 := by
    have hr : Set.range (sc d.val) = {sc d.val c0} := by
      ext t
      constructor
      · rintro ⟨c,rfl⟩
        simp only [Set.mem_singleton_iff]
        exact congrArg (sc d.val) (hc c)
      · intro ht
        rw [Set.mem_singleton_iff] at ht
        exact ⟨c0,ht.symm⟩
    unfold optimum
    rw [hr,csInf_singleton]
  rw [he,ho]
  by_cases hzero : sc d.val c0 = 0 <;> simp [ratio,hzero]

theorem from_children (h : Needs) : Statement := by
  intro prog himplements n m hn hm σ ε hε k out hrun hhalt
  obtain ⟨k0,out0,Q,hrun0,hhalt0,hout0,hAlg⟩ :=
    himplements n m hn hm σ ε hε
  have heq : out0 = out := h.child_5.2 prog k0 k (inputState σ ε) out0 out
    hrun0 hhalt0 hrun hhalt
  refine ⟨Q,heq ▸ hout0,?_⟩
  obtain ⟨R,Q',hLift,hcase⟩ := hAlg
  have hR := h.child_4 n m hn (by omega) σ R
  have hdist : distortion σ Q ≤ distortion R.profile Q' := by
    unfold distortion
    refine iSup_le fun d => ?_
    obtain ⟨d',hd',hsc,hopt,hcost⟩ := hR.2 d.val d.property
    rw [← hcost Q' Q hLift,← hopt]
    exact le_iSup_of_le ⟨d',hd'⟩ le_rfl
  apply hdist.trans
  by_cases hcount : R.count = 1
  · apply (singleton_distortion hcount R.profile Q').trans
    have hone : (1 : ℝ) ≤ 213609/100000 + ε := by linarith [hε.1]
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hone
  · have hcount2 : 2 ≤ R.count := by have := R.count_pos; omega
    rcases hcase with hsingle | ⟨D,hD,P,htrajectory,haverage⟩
    · exact (hcount hsingle).elim
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hδ : 0 < ε/(32*n) := div_pos hε.1 (by positivity)
    have hstable : ApproxStable D R.profile Q' (ε/(32*n)) :=
      h.child_1 n R.count hn hcount2 D R.profile (ε/(32*n)) P hδ htrajectory
        Q' haverage
    have hbound := h.child_2 n R.count hn R.count_pos D hD R.profile hR.1
      Q' (ε/(32*n)) (le_of_lt hδ) hstable
    have hcancel : (32 : ℝ)*n*(ε/(32*n)) = ε := by
      field_simp [ne_of_gt hnR]
    simpa only [hcancel] using hbound

#print axioms from_children
end MetricDistortion.Contracts.Computation_ProgramCorrectness
