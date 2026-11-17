import Voting.Stable.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Geometry_RankStability

theorem from_children (h : Needs) : Statement := by
  intro n m hn hm D σ P hstable H o
  have hphi := h.child_3 D
  have hcont : ContinuousOn (phi D) (Icc (0 : ℝ) 1) := hphi.2.2.1
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hrange (v : Fin n) (c : Fin m) : block (σ v) P c ⊆ Icc (0 : ℝ) 1 := by
    intro x hx
    have hu : x ∈ ⋃ c, block (σ v) P c := Set.mem_iUnion.mpr ⟨c,hx⟩
    rw [(h.child_2 m (σ v) P).2.2.2] at hu
    exact ⟨hu.1,hu.2.le⟩
  have hblockint (v : Fin n) (c : Fin m) : IntegrableOn (phi D) (block (σ v) P c) volume :=
    hcont.integrableOn_Icc.mono_set (hrange v c)
  have hconstint (v : Fin n) (c : Fin m) :
      IntegrableOn (fun _ : ℝ => mu D) (block (σ v) P c) volume :=
    integrableOn_const (by simp [block,Real.volume_Ico])
  have hblock (v : Fin n) (c : Fin m) :
      (∫ u in block (σ v) P c, (phi D u-mu D)) =
        P.val c*(compare D (σ v) P c-mu D) := by
    have hi : (∫ u in block (σ v) P c, phi D u) = P.val c*compare D (σ v) P c := by
      rw [(h.child_1 m D (σ v) P c).1]
      unfold ambientCompare block
      rw [integral_Ico_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (le_add_of_nonneg_right (P.property.1 c))]
      symm
      simpa [below,mass,mul_comm] using
        (intervalIntegral.mul_integral_comp_add_mul (f := phi D) (a := 0) (b := 1)
          (P.val c) (below (σ v) P c))
    rw [integral_sub (hblockint v c) (hconstint v c),hi,setIntegral_const]
    simp only [measureReal_def,(h.child_2 m (σ v) P).1 c,
      ENNReal.toReal_ofReal (P.property.1 c),smul_eq_mul]
    ring
  have hregion (v : Fin n) :
      (∫ u in region (σ v) P H, (phi D u-mu D)) =
        ∑ c ∈ H.toFinset, P.val c*(compare D (σ v) P c-mu D) := by
    have heq : region (σ v) P H = ⋃ c ∈ H.toFinset, block (σ v) P c := by
      ext x
      simp [region]
    rw [heq]
    have hiDiff (c : Fin m) : IntegrableOn (fun u => phi D u-mu D) (block (σ v) P c) volume := by
      exact Integrable.sub' (hblockint v c) (hconstint v c)
    have he : (∫ u in ⋃ c ∈ H.toFinset, block (σ v) P c, (phi D u-mu D)) =
        ∑ c ∈ H.toFinset, ∫ u in block (σ v) P c, (phi D u-mu D) :=
      integral_biUnion_finset (s := fun c => block (σ v) P c)
        (f := fun u => phi D u-mu D) H.toFinset (fun c _ => measurableSet_Ico)
        (fun c _ d _ hcd => (h.child_2 m (σ v) P).2.1 c d hcd) (fun c _ => hiDiff c)
    exact he.trans (Finset.sum_congr rfl fun c _ => hblock v c)
  constructor
  · have haverage (c : Fin m) : avg (fun v => P.val c*(compare D (σ v) P c-mu D)) =
        P.val c*(score D σ P c-mu D) := by
      unfold score avg
      simp_rw [mul_sub,Finset.sum_sub_distrib,← Finset.mul_sum]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp
    calc
      avg (fun v => ∫ u in region (σ v) P H, (phi D u-mu D)) =
        avg (fun v => ∑ c ∈ H.toFinset, P.val c*(compare D (σ v) P c-mu D)) := by
          simp_rw [hregion]
      _ = ∑ c ∈ H.toFinset, avg (fun v => P.val c*(compare D (σ v) P c-mu D)) := by
        unfold avg
        rw [Finset.sum_comm,Finset.sum_div]
      _ = 0 := by
        simp_rw [haverage]
        apply Finset.sum_eq_zero
        intro c _
        by_cases hc : P.val c=0
        · simp [hc]
        · have hpos : 0 < P.val c := lt_of_le_of_ne (P.property.1 c) (Ne.symm hc)
          rw [h.child_0 n m hn hm D σ P hstable c hpos]
          ring
  · have hpoint (v : Fin n) : phi D (below (σ v) P o) ≤ compare D (σ v) P o := by
      have hb : 0 ≤ below (σ v) P o := by
        unfold below mass
        apply Finset.sum_nonneg
        intro j _
        by_cases hj : prefers (σ v) o j
        · simpa [Set.mem_setOf_eq,hj] using P.property.1 j
        · simp [Set.mem_setOf_eq,hj]
      have htotal : below (σ v) P o+P.val o ≤ 1 := by
        calc
          _ = ∑ j, ((if prefers (σ v) o j then P.val j else 0)+(if j=o then P.val j else 0)) := by
            simp [below,mass,Finset.sum_add_distrib]
          _ ≤ ∑ j, P.val j := by
            apply Finset.sum_le_sum
            intro j _
            by_cases hj : j=o
            · subst j
              simp [prefers]
            · simp only [hj,ite_false,add_zero]
              split_ifs <;> simp_all [P.property.1 j]
          _ = 1 := P.property.2
      have hbmem : below (σ v) P o ∈ Icc (0 : ℝ) 1 := ⟨hb,by linarith [P.property.1 o]⟩
      have harg : ∀ s ∈ Icc (0 : ℝ) 1, below (σ v) P o+s*P.val o ∈ Icc (0 : ℝ) 1 := by
        intro s hs
        constructor
        · exact add_nonneg hb (mul_nonneg hs.1 (P.property.1 o))
        · linarith [mul_le_mul_of_nonneg_right hs.2 (P.property.1 o)]
      have hi : IntervalIntegrable (fun s => phi D (below (σ v) P o+s*P.val o)) volume 0 1 :=
        (hcont.comp (by fun_prop) harg).intervalIntegrable_of_Icc zero_le_one
      rw [(h.child_1 m D (σ v) P o).1]
      unfold ambientCompare
      have he := intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const hi
        (fun s hs => hphi.1 hbmem (harg s hs) (le_add_of_nonneg_right (mul_nonneg hs.1 (P.property.1 o))))
      simpa [below,mass] using he
    calc
      avg (fun v => phi D (below (σ v) P o)) ≤ avg (fun v => compare D (σ v) P o) := by
        unfold avg
        exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun v _ => hpoint v) (Nat.cast_nonneg n)
      _ = score D σ P o := rfl
      _ ≤ mu D := hstable o

#print axioms from_children
end MetricDistortion.Contracts.Geometry_RankStability
