import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal Topology
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Lower_ForcedMass

theorem from_children (h : Needs) : Statement := by
  intro n N k hn hk hkN z hz D σ hσ p hp P hP hscore Q hQ
  let q : ℝ := 1-Q.val 0
  have hN : 0 < N := hk.trans hkN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hQ0 : Q.val 0 ≤ 1 := by
    simpa [Q.property.2] using Finset.single_le_sum (fun c _ => Q.property.1 c)
      (Finset.mem_univ (0 : Fin (N+1)))
  have hq0 : 0 ≤ q := sub_nonneg.mpr hQ0
  have hq1 : q ≤ 1 := by dsimp [q]; linarith [Q.property.1 0]
  by_contra hnot
  have hqp : q < p := lt_of_not_ge hnot
  have hq1lt : q < 1 := hqp.trans_le hp.2
  obtain ⟨Pq,hPq,hstableq⟩ := h.child_0 n N k hn hk hkN z hz D σ hσ Q hQ
  obtain ⟨P1,hP1⟩ := h.child_4 N hN 1 ⟨by norm_num,le_rfl⟩
  let i0 : Fin N := ⟨0,hN⟩
  have hsame (a b : Fin (N+1)) (ha : a ≠ 0) (hb : b ≠ 0) :
      score D σ P1 a = score D σ P1 b := by
    let g : Ranking (N+1) := Equiv.swap a b
    have hg : g 0 = 0 := Equiv.swap_apply_of_ne_of_ne ha.symm hb.symm
    have hrel : ∀ c, P1.val c = P1.val (g c) := by
      intro c
      have he : (g c).val = 0 ↔ c.val = 0 := by
        constructor
        · intro hc
          have hgc : g c = g 0 := by rw [hg]; exact Fin.ext hc
          exact congrArg Fin.val (g.injective hgc)
        · intro hc
          have hc0 : c = 0 := Fin.ext hc
          simp [hc0,hg]
      rw [hP1 c,hP1 (g c)]
      simp [he]
    have hh := h.child_3 n N k hn hk hkN z hz D σ hσ g hg P1 P1 hrel a
    simpa [g] using hh
  have hH1 (c : Fin (N+1)) (hc : c ≠ 0) : score D σ P1 c = mu D := by
    have hh := h.child_1 n (N+1) hn (by omega) D σ P1
    unfold payoff at hh
    rw [Fin.sum_univ_succ] at hh
    have htail (i : Fin N) : score D σ P1 i.succ = score D σ P1 c :=
      hsame _ _ (by simp) hc
    have hhead : P1.val 0 = 0 := by simpa using hP1 0
    have hm (i : Fin N) : P1.val i.succ = 1/(N : ℝ) := by simpa using hP1 i.succ
    rw [hhead,zero_mul,zero_add] at hh
    have hterm (i : Fin N) : P1.val i.succ*score D σ P1 i.succ =
        (1/(N : ℝ))*score D σ P1 c := by rw [hm,htail]
    simp_rw [hterm] at hh
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
    have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNr
    field_simp at hh
    nlinarith
  let refVec : ℝ → (Fin (N+1) → ℝ) := fun t c => if c.val = 0 then 1-t else t/N
  let G : ℝ → ℝ := fun t => ambientScore D σ (refVec t) 0
  have hrefvec (t : ℝ) (Pt : Lottery (N+1)) (hPt : Reference t Pt) : Pt.val = refVec t := by
    funext c
    exact hPt c
  have hGeq (t : ℝ) (Pt : Lottery (N+1)) (hPt : Reference t Pt) :
      G t = score D σ Pt 0 := by
    unfold G ambientScore score avg
    rw [← hrefvec t Pt hPt]
    congr 1
    apply Finset.sum_congr rfl
    intro v hv
    exact (h.child_2 (N+1) D (σ v) Pt 0).1.symm
  have hGcont : ContinuousOn G (Icc (0 : ℝ) 1) := by
    have hvcont : Continuous refVec := by
      apply continuous_pi
      intro c
      dsimp [refVec]
      split_ifs <;> fun_prop
    have hmaps : MapsTo refVec (Icc (0 : ℝ) 1) (simplex (N+1)) := by
      intro t ht
      obtain ⟨Pt,hPt⟩ := h.child_4 N hN t ht
      rw [← hrefvec t Pt hPt]
      exact Pt.property
    have hv (v : Fin n) : ContinuousOn
        (fun t => ambientCompare D (σ v) (refVec t) 0) (Icc (0 : ℝ) 1) :=
      (h.child_2 (N+1) D (σ v) P 0).2.2.1.comp hvcont.continuousOn hmaps
    exact (continuousOn_finset_sum Finset.univ (fun v hv' => hv v)).div_const n
  have hGlow (t : ℝ) (ht : t ∈ Ico q 1) : mu D ≤ G t := by
    have ht0 : 0 ≤ t := hq0.trans ht.1
    obtain ⟨Pt,hPt⟩ := h.child_4 N hN t ⟨ht0,ht.2.le⟩
    let a : ℝ := (1-t)/(1-q)
    let b : ℝ := (t-q)/(1-q)
    have hd : (0 : ℝ) < 1-q := sub_pos.mpr hq1lt
    have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr ht.2.le) hd.le
    have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr ht.1) hd.le
    have hab : a+b = 1 := by dsimp [a,b]; field_simp; ring
    have hmix : Pt.val = a • Pq.val+b • P1.val := by
      ext c
      change Pt.val c = a*Pq.val c+b*P1.val c
      rw [hPt c,hPq c,hP1 c]
      split_ifs <;> dsimp [a,b] <;> field_simp <;> ring
    have hH (c : Fin (N+1)) (hc : c ≠ 0) : score D σ Pt c ≤ mu D := by
      have hv (v : Fin n) : compare D (σ v) Pt c ≤
          a*compare D (σ v) Pq c+b*compare D (σ v) P1 c := by
        have hh := (h.child_2 (N+1) D (σ v) Pt c).2.2.2.2
          Pq.property P1.property ha hb hab
        rw [← hmix] at hh
        change ambientCompare D (σ v) Pt.val c ≤
          a*ambientCompare D (σ v) Pq.val c+b*ambientCompare D (σ v) P1.val c at hh
        rw [← (h.child_2 (N+1) D (σ v) Pt c).1,
          ← (h.child_2 (N+1) D (σ v) Pq c).1,
          ← (h.child_2 (N+1) D (σ v) P1 c).1] at hh
        simpa only [smul_eq_mul] using hh
      have hh := div_le_div_of_nonneg_right
        (Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hv v)) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      have havg : score D σ Pt c ≤ a*score D σ Pq c+b*score D σ P1 c := by
        unfold score avg
        simp_rw [Finset.sum_add_distrib,← Finset.mul_sum] at hh
        convert hh using 1 <;> ring
      calc
        score D σ Pt c ≤ a*score D σ Pq c+b*score D σ P1 c := havg
        _ ≤ a*mu D+b*mu D := add_le_add
          (mul_le_mul_of_nonneg_left (hstableq c) ha) (by rw [hH1 c hc])
        _ = mu D := by rw [← add_mul,hab,one_mul]
    have hplay := h.child_1 n (N+1) hn (by omega) D σ Pt
    unfold payoff at hplay
    rw [Fin.sum_univ_succ] at hplay
    have hPt0 : Pt.val 0 = 1-t := by simpa using hPt 0
    rw [hPt0] at hplay
    have htailmass : ∑ i : Fin N, Pt.val i.succ = t := by
      have hh := Pt.property.2
      rw [Fin.sum_univ_succ,hPt0] at hh
      linarith
    have htailbound : (∑ i : Fin N, Pt.val i.succ*score D σ Pt i.succ) ≤ t*mu D := by
      calc
        _ ≤ ∑ i : Fin N, Pt.val i.succ*mu D := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (hH i.succ (by simp)) (Pt.property.1 i.succ)
        _ = t*mu D := by rw [← Finset.sum_mul,htailmass]
    rw [hGeq t Pt hPt]
    have ht1 : 0 < 1-t := sub_pos.mpr ht.2
    nlinarith
  have hclosure : closure (Ico q 1) = Icc q 1 := closure_Ico hq1lt.ne
  have hbound : mu D ≤ G p := by
    apply le_on_closure (fun t ht => hGlow t ht) continuousOn_const ?_ ?_
    · apply hGcont.mono
      rw [hclosure]
      exact Icc_subset_Icc hq0 le_rfl
    · rw [hclosure]
      exact ⟨hqp.le,hp.2⟩
  rw [hGeq p P hP] at hbound
  exact (not_lt_of_ge hbound) hscore

#print axioms from_children
end MetricDistortion.Contracts.Lower_ForcedMass
