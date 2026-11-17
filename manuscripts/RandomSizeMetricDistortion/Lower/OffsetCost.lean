import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Lower_OffsetCost

private theorem suffix_value {N : ℕ} (r : Ranking (N+1)) (c : Fin (N+1)) :
    sOffset r (insertionOffsets N) c = if r c < r 0 then 1 else 0 := by
  have hne : ({t : ℝ | ∃ j, r j ≤ r c ∧ t = insertionOffsets N j}).Nonempty :=
    ⟨insertionOffsets N c,c,le_rfl,rfl⟩
  have hb : BddBelow {t : ℝ | ∃ j, r j ≤ r c ∧ t = insertionOffsets N j} := by
    refine ⟨0,?_⟩
    rintro t ⟨j,hj,rfl⟩
    simp only [insertionOffsets]
    split_ifs <;> norm_num
  by_cases hc : r c < r 0
  · rw [if_pos hc]
    apply le_antisymm
    · have hc0 : c.val ≠ 0 := by intro he; have hc0 : c = 0 := Fin.ext he; simpa [hc0] using hc
      exact csInf_le hb ⟨c,le_rfl,by simp [insertionOffsets,hc0]⟩
    · apply le_csInf hne
      rintro t ⟨j,hj,rfl⟩
      have hj0 : j.val ≠ 0 := by
        intro he
        have : j = 0 := Fin.ext he
        subst j
        exact (not_le_of_gt hc) hj
      simp [insertionOffsets,hj0]
  · rw [if_neg hc]
    apply le_antisymm
    · exact csInf_le hb ⟨0,le_of_not_gt hc,by simp [insertionOffsets]⟩
    · apply le_csInf hne
      rintro t ⟨j,hj,rfl⟩
      simp only [insertionOffsets]
      split_ifs <;> norm_num

private theorem delta_value {N : ℕ} (r : Ranking (N+1)) :
    deltaOffset r (insertionOffsets N) = if (r 0).val = N then 0 else 1 := by
  have hfinite : ({t : ℝ | ∃ i j, r j ≤ r i ∧ t = insertionOffsets N i-insertionOffsets N j}).Finite := by
    apply (Set.finite_range fun ij : Fin (N+1) × Fin (N+1) =>
      insertionOffsets N ij.1-insertionOffsets N ij.2).subset
    rintro t ⟨i,j,hij,rfl⟩
    exact ⟨(i,j),rfl⟩
  have hne : ({t : ℝ | ∃ i j, r j ≤ r i ∧ t = insertionOffsets N i-insertionOffsets N j}).Nonempty :=
    ⟨0,0,0,le_rfl,by simp⟩
  by_cases ht : (r 0).val = N
  · rw [if_pos ht]
    apply le_antisymm
    · apply csSup_le hne
      rintro t ⟨i,j,hji,rfl⟩
      by_cases hj : j.val = 0
      · have hj0 : j = 0 := Fin.ext hj
        subst j
        have hi : i = 0 := r.injective (Fin.ext (by have := (r i).isLt; omega))
        simp [hi,insertionOffsets]
      · simp only [insertionOffsets,hj,if_false]
        split_ifs <;> norm_num
    · exact le_csSup hfinite.bddAbove ⟨0,0,le_rfl,by simp⟩
  · rw [if_neg ht]
    apply le_antisymm
    · apply csSup_le hne
      rintro t ⟨i,j,hji,rfl⟩
      simp only [insertionOffsets]
      split_ifs <;> norm_num
    · let last : Fin (N+1) := ⟨N,Nat.lt_succ_self N⟩
      let i := r.symm last
      have hi : i.val ≠ 0 := by
        intro he
        have hi0 : i = 0 := Fin.ext he
        have heq : r i = last := r.apply_symm_apply last
        rw [hi0] at heq
        exact ht (congrArg Fin.val heq)
      have hr : r 0 ≤ r i := by
        have hii : r i = last := r.apply_symm_apply last
        rw [hii]
        change (r 0).val ≤ N
        have := (r 0).isLt
        omega
      exact le_csSup hfinite.bddAbove ⟨i,0,hr,by simp [insertionOffsets,hi]⟩

private theorem ranking_fiber_card (N : ℕ) (q : Fin (N+1)) :
    (Finset.univ.filter fun r : Ranking (N+1) => (r 0).val = q.val).card = Nat.factorial N := by
  have heq : (Finset.univ.filter fun r : Ranking (N+1) => (r 0).val = q.val) =
      Finset.univ.filter (fun r : Ranking (N+1) => r 0 = q) := by ext r; simp [Fin.ext_iff]
  rw [heq]
  have he := (Equiv.Perm.decomposeFin (n := N)).symm.sum_comp
    (fun r : Ranking (N+1) => if r 0 = q then (1 : ℕ) else 0)
  have hh : (∑ r : Ranking (N+1), if r 0 = q then (1 : ℕ) else 0) = Nat.factorial N := by
    rw [← he,Fintype.sum_prod_type]
    simp only [Equiv.Perm.decomposeFin_symm_apply_zero,Finset.sum_const,
      Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]
    simp [mul_ite]
  simpa [Finset.sum_filter] using hh

theorem from_children (h : Needs) : Statement := by
  intro n N k hn hk hkN z hz σ hσ Q
  have hz0 := hz.1
  have hz1 := hz.2
  let x := insertionOffsets N
  have hN : 0 < N := hk.trans hkN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos (F : ℕ → ℝ) : avg (fun v => F ((σ v) 0).val) = z*F k+(1-z)*F N := by
    have hh := h.child_2 n N k hn hk hkN z hz σ hσ (fun r => F (r 0).val)
    have hs (q : Fin (N+1)) :
        (∑ r ∈ Finset.univ.filter (fun r : Ranking (N+1) => (r 0).val = q.val), F (r 0).val) =
        (Nat.factorial N : ℝ)*F q.val := by
      calc
        _ = ∑ _r ∈ Finset.univ.filter (fun r : Ranking (N+1) => (r 0).val = q.val), F q.val := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [(Finset.mem_filter.mp hr).2]
        _ = _ := by simp [ranking_fiber_card]
    rw [hs ⟨k,hkN.trans (Nat.lt_succ_self N)⟩,hs ⟨N,Nat.lt_succ_self N⟩] at hh
    have hfac : (Nat.factorial N : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
    convert hh using 1 <;> dsimp <;> field_simp <;> ring
  have hscale : scale σ x = z := by
    unfold scale
    simp_rw [x,delta_value]
    have hh := hpos (fun j => if j = N then 0 else 1)
    simpa [Nat.ne_of_lt hkN] using hh
  have hperm (g : Ranking (N+1)) (hg : g 0 = 0) (c : Fin (N+1)) :
      avg (fun v => sOffset (σ v) x c) = avg (fun v => sOffset (σ v) x (g c)) := by
    let T : Ranking (N+1) ≃ Ranking (N+1) :=
      {toFun := fun r => g.trans r
       invFun := fun r => g.symm.trans r
       left_inv := by intro r; ext j; simp [Equiv.trans_apply]
       right_inv := by intro r; ext j; simp [Equiv.trans_apply]}
    have hgs : g.symm 0 = 0 := by apply g.injective; simp [hg]
    have hT0 (r : Ranking (N+1)) : T r 0 = r 0 := by simp [T,Equiv.trans_apply,hg]
    have hTi0 (r : Ranking (N+1)) : T.symm r 0 = r 0 := by simp [T,Equiv.trans_apply,hgs]
    have hf (r : Ranking (N+1)) : sOffset r x (g c) = sOffset (T r) x c := by
      simp [x,suffix_value,T,Equiv.trans_apply,hg]
    have hs (j : ℕ) :
        (∑ r ∈ Finset.univ.filter (fun r : Ranking (N+1) => (r 0).val = j), sOffset r x (g c)) =
        ∑ r ∈ Finset.univ.filter (fun r : Ranking (N+1) => (r 0).val = j), sOffset r x c := by
      apply Finset.sum_bij (fun r hr => T r)
      · intro r hr; simpa [hT0] using hr
      · intro r hr s hs he; exact T.injective he
      · intro r hr; exact ⟨T.symm r,by simpa [hTi0] using hr,T.apply_symm_apply r⟩
      · intro r hr; exact hf r
    have ha := h.child_2 n N k hn hk hkN z hz σ hσ (fun r => sOffset r x c)
    have hb := h.child_2 n N k hn hk hkN z hz σ hσ (fun r => sOffset r x (g c))
    rw [ha,hb,hs k,hs N]
  let i0 : Fin N := ⟨0,hN⟩
  let u := avg (fun v => sOffset (σ v) x i0.succ)
  have hH (i : Fin N) : avg (fun v => sOffset (σ v) x i.succ) = u := by
    have hg : (Equiv.swap i.succ i0.succ) 0 = 0 :=
      Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm (Fin.succ_ne_zero i0).symm
    have hh := hperm (Equiv.swap i.succ i0.succ) hg i.succ
    have hswap : (Equiv.swap i.succ i0.succ) i.succ = i0.succ :=
      Equiv.swap_apply_left _ _
    rw [hswap] at hh
    exact hh
  have hcount (r : Ranking (N+1)) : (∑ c, sOffset r x c) = (r 0).val := by
    simp_rw [x,suffix_value]
    rw [Equiv.sum_comp r (fun j => if j < r 0 then (1 : ℝ) else 0)]
    have hc : (Finset.univ.filter fun j : Fin (N+1) => j < r 0).card = (r 0).val := by
      have heq : (Finset.univ.filter fun j : Fin (N+1) => j < r 0) = Finset.Iio (r 0) := by
        ext j
        simp
      rw [heq]
      exact Fin.card_Iio (r 0)
    rw [← Finset.sum_filter]
    simp [hc]
  have hsum : (N : ℝ)*u = z*k+(1-z)*N := by
    have hz0 (v : Fin n) : sOffset (σ v) x 0 = 0 := by simp [x,suffix_value]
    have hleft : (∑ c, avg (fun v => sOffset (σ v) x c)) = (N : ℝ)*u := by
      rw [Fin.sum_univ_succ]
      simp only [hz0,avg,Finset.sum_const_zero,zero_div,zero_add]
      change (∑ i : Fin N, avg (fun v => sOffset (σ v) x i.succ)) = _
      simp_rw [hH]
      simp
    have he : (∑ c, avg (fun v => sOffset (σ v) x c)) = avg (fun v => (∑ c, sOffset (σ v) x c)) := by
      unfold avg
      rw [← Finset.sum_div,Finset.sum_comm]
    rw [hleft] at he
    simp_rw [hcount] at he
    rw [hpos (fun j => (j : ℝ))] at he
    exact he
  have hu : u = z*k/N+1-z := by
    calc
      u = (z*k+(1-z)*N)/N := (eq_div_iff (ne_of_gt hNr)).2 (by nlinarith [hsum])
      _ = z*k/N+1-z := by field_simp; ring
  have hmass : ∑ i : Fin N, Q.val i.succ = 1-Q.val 0 := by
    have hh := Q.property.2
    rw [Fin.sum_univ_succ] at hh
    linarith
  have hL : loss σ Q x = (1-Q.val 0)*u := by
    unfold loss avg
    rw [Finset.sum_comm,Finset.sum_div,Fin.sum_univ_succ]
    have hz0 (v : Fin n) : sOffset (σ v) x 0 = 0 := by simp [x,suffix_value]
    simp only [hz0,mul_zero,Finset.sum_const_zero,zero_div,zero_add]
    calc
      _ = ∑ i : Fin N, Q.val i.succ*avg (fun v => sOffset (σ v) x i.succ) := by
        apply Finset.sum_congr rfl
        intro i hi
        unfold avg
        rw [← Finset.mul_sum]
        ring
      _ = (1-Q.val 0)*u := by simp_rw [hH]; rw [← Finset.sum_mul,hmass]
  have hx : ∀ c, 0 ≤ x c := by intro c; dsimp [x,insertionOffsets]; split_ifs <;> norm_num
  obtain ⟨d,hcons,hopt,hbase,hdiff,hratio⟩ := h.child_0 n (N+1) hn (by omega) σ x hx 0 (by simp [x,insertionOffsets])
  have hop : optimum d = sc d 0 := by
    have hb : BddBelow (Set.range (sc d)) := ⟨sc d 0,by rintro t ⟨c,rfl⟩; exact hopt c⟩
    exact le_antisymm (csInf_le hb ⟨0,rfl⟩) (le_csInf ⟨sc d 0,0,rfl⟩ (by rintro t ⟨c,rfl⟩; exact hopt c))
  have hQ0 : Q.val 0 ≤ 1 := by
    simpa [Q.property.2] using Finset.single_le_sum (fun c _ => Q.property.1 c) (Finset.mem_univ (0 : Fin (N+1)))
  have hq : 0 ≤ 1-Q.val 0 := sub_nonneg.mpr hQ0
  have hu0 : 0 ≤ u := by
    rw [hu]
    have hh : (0 : ℝ) ≤ z*k/N := by positivity
    linarith [hz.2]
  have heq : ENNReal.ofReal (1+2*(1-Q.val 0)*((k : ℝ)/N+(1-z)/z)) =
      offsetRatio (loss σ Q x) (scale σ x) := by
    rw [hL,hscale]
    have hreal : 1+2*(1-Q.val 0)*((k : ℝ)/N+(1-z)/z) = 1+2*((1-Q.val 0)*u/z) := by
      rw [hu]
      field_simp
      <;> ring
    rw [hreal]
    simp only [offsetRatio,if_neg (ne_of_gt hz.1)]
    rw [ENNReal.ofReal_add (by norm_num) (by positivity),ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [heq,← hratio Q]
  rw [← hop]
  exact le_iSup (fun d : {d : Metric n (N+1) // Consistent σ d} =>
    ratio (expectedCost d.val Q) (optimum d.val)) ⟨d,hcons⟩

#print axioms from_children
end MetricDistortion.Contracts.Lower_OffsetCost
