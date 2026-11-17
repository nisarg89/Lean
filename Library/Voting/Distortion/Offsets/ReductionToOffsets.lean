import Voting.Distortion.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Offsets_ReductionToOffsets

private theorem ratio_le_offset (E C L S : ℝ) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (hL : 0 ≤ L) (hS : 0 ≤ S) (hdiff : E-C ≤ L) (hscale : S ≤ 2*C) :
    ratio E C ≤ offsetRatio L S := by
  by_cases hL0 : L = 0
  · have hEC : E ≤ C := by linarith
    have hrhs : offsetRatio L S = 1 := by simp [offsetRatio,hL0]
    rw [hrhs]
    by_cases hC0 : C = 0
    · have hE0 : E = 0 := by linarith
      simp [ratio,hC0,hE0]
    · have hCp : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
      simp only [ratio,if_neg hC0]
      calc
        ENNReal.ofReal (E/C) ≤ ENNReal.ofReal 1 :=
          ENNReal.ofReal_le_ofReal ((div_le_one hCp).2 hEC)
        _ = 1 := by norm_num
  · by_cases hS0 : S = 0
    · simp [offsetRatio,hS0,hL0]
    · have hSp : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
      have hCp : 0 < C := by linarith
      have hC0 : C ≠ 0 := ne_of_gt hCp
      have hfrac : L ≤ (2*L*C)/S := by
        apply (le_div_iff₀ hSp).2
        nlinarith
      have hreal : E/C ≤ 1+2*(L/S) := by
        apply (div_le_iff₀ hCp).2
        calc
          E ≤ C+L := by linarith
          _ ≤ C+(2*L*C)/S := add_le_add (le_refl C) hfrac
          _ = (1+2*(L/S))*C := by field_simp <;> ring
      have heq : ENNReal.ofReal (1+2*(L/S)) = offsetRatio L S := by
        simp only [offsetRatio,if_neg hS0]
        rw [ENNReal.ofReal_add (by norm_num) (by positivity),ENNReal.ofReal_mul (by norm_num)]
        norm_num
      rw [ratio,if_neg hC0]
      exact (ENNReal.ofReal_le_ofReal hreal).trans_eq heq

private theorem optimum_eq_of_optimal {n m : ℕ} (d : Metric n m) (o : Fin m)
    (ho : Optimal d o) : optimum d = sc d o := by
  have hne : (Set.range (sc d)).Nonempty := ⟨sc d o,o,rfl⟩
  have hb : BddBelow (Set.range (sc d)) := by
    refine ⟨sc d o,?_⟩
    rintro t ⟨c,rfl⟩
    exact ho c
  exact le_antisymm (csInf_le hb ⟨o,rfl⟩) (le_csInf hne (by
    rintro t ⟨c,rfl⟩
    exact ho c))

theorem from_children (h : Needs) : Statement := by
  intro n m hn hm σ P
  let X := {x : Fin m → ℝ // (∀ c, 0 ≤ x c) ∧ ∃ c, x c = 0}
  apply le_antisymm
  · apply iSup_le
    intro metric
    let d := metric.val
    letI : PseudoMetricSpace (Fin n ⊕ Fin m) := d
    letI : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
    have hne : (Set.range (sc d)).Nonempty := Set.range_nonempty _
    obtain ⟨o,ho⟩ := hne.csInf_mem (Set.finite_range (sc d))
    have hopt : Optimal d o := by
      intro c
      rw [ho]
      exact csInf_le (Set.finite_range (sc d)).bddBelow ⟨c,rfl⟩
    let x := fun c => distance d (.inr o) (.inr c)
    have hx : ∀ c, 0 ≤ x c := by intro c; exact dist_nonneg
    have hxo : x o = 0 := by simp [x,distance]
    let offsets : X := ⟨x,hx,⟨o,hxo⟩⟩
    obtain ⟨hdiff,hscale⟩ := h.child_1 n m hn hm σ P d metric.property o hopt
    have hcost : ∀ c, 0 ≤ sc d c := by
      intro c
      exact div_nonneg (Finset.sum_nonneg fun v _ => dist_nonneg) (Nat.cast_nonneg n)
    have hE : 0 ≤ expectedCost d P := Finset.sum_nonneg fun c _ =>
      mul_nonneg (P.property.1 c) (hcost c)
    have hL : 0 ≤ loss σ P x := by
      unfold loss avg
      exact div_nonneg (Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun c _ =>
        mul_nonneg (P.property.1 c) (((h.child_2 m (σ v) x hx).1 c).1)) (Nat.cast_nonneg n)
    have hS : 0 ≤ scale σ x := by
      unfold scale avg
      exact div_nonneg (Finset.sum_nonneg fun v _ => (h.child_2 m (σ v) x hx).2) (Nat.cast_nonneg n)
    change ratio (expectedCost d P) (optimum d) ≤ _
    rw [optimum_eq_of_optimal d o hopt]
    apply le_trans (ratio_le_offset _ _ _ _ hE (hcost o) hL hS hdiff hscale)
    exact le_iSup (fun x : X => offsetRatio (loss σ P x.val) (scale σ x.val)) offsets
  · apply iSup_le
    intro offsets
    obtain ⟨o,hxo⟩ := offsets.property.2
    obtain ⟨d,hcons,hopt,hbase,hdiff,hratio⟩ :=
      h.child_0 n m hn hm σ offsets.val offsets.property.1 o hxo
    calc
      offsetRatio (loss σ P offsets.val) (scale σ offsets.val) =
        ratio (expectedCost d P) (sc d o) := (hratio P).symm
      _ = ratio (expectedCost d P) (optimum d) := by rw [optimum_eq_of_optimal d o hopt]
      _ ≤ distortion σ P := le_iSup
        (fun d : {d : Metric n m // Consistent σ d} =>
          ratio (expectedCost d.val P) (optimum d.val)) ⟨d,hcons⟩

#print axioms from_children
end MetricDistortion.Contracts.Offsets_ReductionToOffsets
