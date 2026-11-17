import Voting.Distortion.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Geometry_CutoffProperties

private lemma below_nonneg {m : ℕ} (r : Ranking m) (P : Lottery m) (c : Fin m) :
    0 ≤ below r P c := by
  unfold below mass
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact P.property.1 j
  · exact le_rfl

private lemma block_upper {m : ℕ} (r : Ranking m) (P : Lottery m) (c : Fin m) :
    below r P c+P.val c ≤ 1 := by
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

private lemma below_mono {m : ℕ} (r : Ranking m) (P : Lottery m) (c e : Fin m)
    (hce : r c ≤ r e) : below r P c ≤ below r P e := by
  unfold below mass
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : prefers r c j
  · have he : prefers r e j := lt_of_lt_of_le hj hce
    simp [hj,he]
  · simp only [Set.mem_setOf_eq,hj,ite_false]
    split_ifs
    · exact P.property.1 j
    · exact le_rfl

theorem from_children (h : Needs) : Statement := by
  intro n m σ P d o v t ht
  dsimp only
  let r := σ v
  let H := marked d o t
  let a := lowerCut σ P d o v t
  let A := upperCut σ P d o v t
  have ho : o ∉ H := by
    change ¬t < distance d (.inr o) (.inr o)
    rw [(h.child_1 n m d).1 (.inr o)]
    exact not_lt_of_ge ht
  let U : Finset (Fin m) := Finset.univ.filter (fun c => c ∉ H)
  have hUne : U.Nonempty := ⟨o,by simp [U,ho]⟩
  obtain ⟨j,hjU,hjmin⟩ := U.exists_min_image r hUne
  have hj : j ∉ H := (Finset.mem_filter.mp hjU).2
  have hfirst : ∀ c, c ∉ H → r j ≤ r c := by
    intro c hc
    exact hjmin c (by simp [U,hc])
  have haeq : a = below r P j := by
    change sInf {z | ∃ c, c ∉ H ∧ z = below r P c} = below r P j
    apply IsLeast.csInf_eq
    refine ⟨⟨j,hj,rfl⟩,?_⟩
    rintro z ⟨c,hc,rfl⟩
    exact below_mono r P j c (hfirst c hc)
  have ha0 : 0 ≤ a := by rw [haeq]; exact below_nonneg r P j
  have har : a ≤ below r P o := by rw [haeq]; exact below_mono r P j o (hfirst o ho)
  have hap : a ≤ mass P H := by
    rw [haeq]
    unfold below mass
    apply Finset.sum_le_sum
    intro c _
    by_cases hc : prefers r j c
    · have hcH : c ∈ H := by
        by_contra hn
        exact (not_lt_of_ge (hfirst c hn)) hc
      simp [Set.mem_setOf_eq,hc,hcH]
    · simp only [Set.mem_setOf_eq,hc,ite_false]
      split_ifs
      · exact P.property.1 c
      · exact le_rfl
  have hAnonneg_and_upper : 0 ≤ A ∧ A ≤ 1 ∧ region r P H ⊆ Icc 0 A ∧
      (A=0 ∨ ∃ c, c ∈ H ∧ 0 < P.val c ∧ A=below r P c+P.val c) := by
    by_cases hex : ∃ c, c ∈ H ∧ 0 < P.val c
    · let V : Finset (Fin m) := Finset.univ.filter (fun c => c ∈ H ∧ 0 < P.val c)
      have hVne : V.Nonempty := by
        obtain ⟨c,hc,hcp⟩ := hex
        exact ⟨c,by simp [V,hc,hcp]⟩
      obtain ⟨c,hcV,hcmax⟩ := V.exists_max_image (fun c => below r P c+P.val c) hVne
      have hc : c ∈ H ∧ 0 < P.val c := (Finset.mem_filter.mp hcV).2
      have hAeq : A=below r P c+P.val c := by
        change (if ∃ c, c ∈ H ∧ 0 < P.val c then
          sSup {z | ∃ c, c ∈ H ∧ 0 < P.val c ∧ z=below r P c+P.val c} else 0) = _
        rw [if_pos hex]
        apply IsGreatest.csSup_eq
        refine ⟨⟨c,hc.1,hc.2,rfl⟩,?_⟩
        rintro z ⟨e,he,hep,rfl⟩
        exact hcmax e (by simp [V,he,hep])
      refine ⟨?_,?_,?_,Or.inr ⟨c,hc.1,hc.2,hAeq⟩⟩
      · rw [hAeq]
        exact add_nonneg (below_nonneg r P c) hc.2.le
      · rw [hAeq]
        exact block_upper r P c
      · intro x hx
        obtain ⟨e,he,hxe⟩ := Set.mem_iUnion₂.mp hx
        have hep : 0 < P.val e := by
          change x ∈ Ico (below r P e) (below r P e+P.val e) at hxe
          linarith [hxe.1,hxe.2]
        refine ⟨le_trans (below_nonneg r P e) hxe.1,?_⟩
        rw [hAeq]
        exact hxe.2.le.trans (hcmax e (by simp [V,he,hep]))
    · have hAeq : A=0 := by
        change (if ∃ c, c ∈ H ∧ 0 < P.val c then _ else 0) = 0
        rw [if_neg hex]
      refine ⟨by rw [hAeq],by rw [hAeq]; norm_num,?_,Or.inl hAeq⟩
      intro x hx
      obtain ⟨c,hc,hxc⟩ := Set.mem_iUnion₂.mp hx
      have hcp : 0 < P.val c := by
        change x ∈ Ico (below r P c) (below r P c+P.val c) at hxc
        linarith [hxc.1,hxc.2]
      exact (hex ⟨c,hc,hcp⟩).elim
  obtain ⟨hA0,hA1,hregion,hAwitness⟩ := hAnonneg_and_upper
  have hp0 : 0 ≤ mass P H := by
    unfold mass
    apply Finset.sum_nonneg
    intro c _
    split_ifs
    · exact P.property.1 c
    · exact le_rfl
  have hpA : mass P H ≤ A := by
    have hv : volume (region r P H) ≤ volume (Icc 0 A) := measure_mono hregion
    rw [(h.child_0 m r P).2.2.1 H,Real.volume_Icc,sub_zero] at hv
    have hv' := ENNReal.toReal_mono (by simp : ENNReal.ofReal A ≠ ⊤) hv
    simpa only [ENNReal.toReal_ofReal hp0,ENNReal.toReal_ofReal hA0] using hv'
  have hcontains : ∀ᵐ u ∂volume, u ∈ Icc 0 a → u ∈ region r P H := by
    filter_upwards [volume.ae_ne a] with u hne
    intro hu
    have hua : u < a := lt_of_le_of_ne hu.2 hne
    have hau : a ≤ 1 := hap.trans (hpA.trans hA1)
    have hu1 : u ∈ Ico (0 : ℝ) 1 := ⟨hu.1,hua.trans_le hau⟩
    rw [← (h.child_0 m r P).2.2.2] at hu1
    obtain ⟨c,huc⟩ := Set.mem_iUnion.mp hu1
    have hc : c ∈ H := by
      by_contra hc
      have hle : a ≤ below r P c := by rw [haeq]; exact below_mono r P j c (hfirst c hc)
      exact (hua.trans_le hle).not_ge huc.1
    exact Set.mem_iUnion₂.mpr ⟨c,hc,huc⟩
  exact ⟨ha0,le_min hap har,hpA,hA1,hregion,hcontains,
    ⟨j,hj,haeq,hfirst⟩,hAwitness⟩

#print axioms from_children
end MetricDistortion.Contracts.Geometry_CutoffProperties
