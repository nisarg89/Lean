import Voting.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Model_RankIntervals

theorem from_children (h : Needs) : Statement := by
  intro m r P
  have hb (c : Fin m) : 0 ≤ below r P c := (h.child_1 m P).2.1 {j | prefers r c j} |>.1
  have hupper (c : Fin m) : below r P c+P.val c ≤ 1 := by
    calc
      _ = ∑ j, ((if prefers r c j then P.val j else 0)+(if j=c then P.val j else 0)) := by
        simp [below,mass,Finset.sum_add_distrib]
      _ ≤ ∑ j, P.val j := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : j=c
        · subst j
          simp [prefers]
        · simp only [hj,ite_false,add_zero]
          split_ifs <;> simp_all [P.property.1 j]
      _ = 1 := P.property.2
  have hordered (c d : Fin m) (hcd : r c < r d) : below r P c+P.val c ≤ below r P d := by
    calc
      _ = ∑ j, ((if prefers r c j then P.val j else 0)+(if j=c then P.val j else 0)) := by
        simp [below,mass,Finset.sum_add_distrib]
      _ ≤ ∑ j, if prefers r d j then P.val j else 0 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : j=c
        · subst j
          simp [prefers,hcd]
        · simp only [hj,ite_false,add_zero]
          by_cases hsmall : prefers r c j
          · have hlarge : prefers r d j := lt_trans hsmall hcd
            simp [hsmall,hlarge]
          · simp only [hsmall,ite_false]
            split_ifs
            · exact P.property.1 j
            · exact le_rfl
      _ = below r P d := rfl
  have hvol (c : Fin m) : volume (block r P c) = ENNReal.ofReal (P.val c) := by
    simp [block,Real.volume_Ico]
  have hdisjoint (c d : Fin m) (hne : c ≠ d) : Disjoint (block r P c) (block r P d) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hne' : r c ≠ r d := fun he => hne (r.injective he)
    rcases lt_or_gt_of_ne hne' with hcd|hdc
    · exact (lt_of_lt_of_le hx.2 (hordered c d hcd)).not_ge hy.1
    · exact (lt_of_lt_of_le hy.2 (hordered d c hdc)).not_ge hx.1
  refine ⟨hvol,hdisjoint,?_,?_⟩
  · intro H
    have heq : region r P H = ⋃ c ∈ H.toFinset, block r P c := by
      ext x
      simp [region]
    have hmass : mass P H = ∑ c ∈ H.toFinset, P.val c := by
      unfold mass
      rw [← Finset.sum_filter]
      congr 1
      ext c
      simp
    rw [heq,measure_biUnion_finset
      (fun a _ b _ hab => hdisjoint a b hab) (fun c _ => measurableSet_Ico)]
    simp_rw [hvol]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => P.property.1 c),hmass]
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hx
      exact ⟨le_trans (hb c) hc.1,lt_of_lt_of_le hc.2 (hupper c)⟩
    · let a : ℕ → ℝ := fun i => ∑ j, if (r j).val < i then P.val j else 0
      have hstart : a 0 = 0 := by simp [a]
      have hend : a m = 1 := by
        calc
          a m = ∑ j, P.val j := by
            apply Finset.sum_congr rfl
            intro j _
            exact if_pos (r j).isLt
          _ = 1 := P.property.2
      have hbefore (i : ℕ) (hi : i < m) : below r P (r.symm ⟨i,hi⟩) = a i := by
        simp [below,mass,prefers,a,Fin.lt_def]
      have hstep (i : ℕ) (hi : i < m) : a (i+1) = a i+P.val (r.symm ⟨i,hi⟩) := by
        let c : Fin m := r.symm ⟨i,hi⟩
        have hc : (r c).val = i := by simp [c]
        calc
          a (i+1) = ∑ j, ((if (r j).val < i then P.val j else 0)+
            (if j=c then P.val j else 0)) := by
            apply Finset.sum_congr rfl
            intro j _
            by_cases hj : j=c
            · subst j
              simp [hc]
            · have hr : (r j).val ≠ i := by
                intro he
                apply hj
                apply r.injective
                apply Fin.ext
                simpa [hc] using he
              have hequiv : (r j).val < i+1 ↔ (r j).val < i := by omega
              simp [hequiv,hj]
          _ = a i+P.val c := by simp [a,Finset.sum_add_distrib]
      intro x hx
      have hxc : x ∈ Ico (a 0) (a m) := by simpa [hstart,hend] using hx
      have hcover := Ico_subset_biUnion_Ico m a hxc
      obtain ⟨i,hi,hxi⟩ := Set.mem_iUnion₂.mp hcover
      have him : i < m := Finset.mem_range.mp hi
      apply Set.mem_iUnion.mpr
      refine ⟨r.symm ⟨i,him⟩,?_⟩
      change x ∈ Ico (below r P (r.symm ⟨i,him⟩))
        (below r P (r.symm ⟨i,him⟩)+P.val (r.symm ⟨i,him⟩))
      rw [hbefore i him]
      simpa [hstep i him] using hxi

#print axioms from_children
end MetricDistortion.Contracts.Model_RankIntervals
