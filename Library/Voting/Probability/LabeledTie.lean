import Voting.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Comparison_LabeledTie

private def uniformLabel : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
private instance : IsProbabilityMeasure uniformLabel := ⟨by simp [uniformLabel,Real.volume_Icc]⟩

private def winner (N : ℕ) (i : Fin N) : Set (Fin N → ℝ) :=
  {x | ∀ j, j ≠ i → x j < x i}

private lemma winner_measurable (N : ℕ) (i : Fin N) : MeasurableSet (winner N i) := by
  unfold winner
  simp_rw [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro j
  by_cases hj : j=i
  · simp [hj]
  · simpa [hj] using measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)

private lemma uniformLabel_Iio {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    (uniformLabel (Iio u)).toReal = u := by
  have heq : Iio u ∩ Icc (0 : ℝ) 1 = Ico (0 : ℝ) u := by
    ext x
    simp only [mem_inter_iff,mem_Iio,mem_Icc,mem_Ico]
    constructor
    · intro hx
      exact ⟨hx.2.1,hx.1⟩
    · intro hx
      exact ⟨hx.2,hx.1,hx.2.le.trans hu.2⟩
  simp [uniformLabel,Measure.restrict_apply measurableSet_Iio,heq,Real.volume_Ico,
    ENNReal.toReal_ofReal hu.1]

/-- Fix the prospective winner's label and integrate the independent labels of
all other duplicates. The conditional winning probability is u^(N-1). -/
private theorem winner_probability (powerIntegral : Comparison_PowerIntegral.Statement)
    (N : ℕ) (i : Fin N) :
    ((Measure.pi fun _ : Fin N => uniformLabel) (winner N i)).toReal = 1/(N : ℝ) := by
  cases N with
  | zero => exact Fin.elim0 i
  | succ n =>
    let T : Set (ℝ × (Fin n → ℝ)) := {z | ∀ j, z.2 j < z.1}
    have hT : MeasurableSet T := by
      dsimp [T]
      simp_rw [Set.setOf_forall]
      apply MeasurableSet.iInter
      intro j
      exact measurableSet_lt ((measurable_pi_apply j).comp measurable_snd) measurable_fst
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
    have he : winner (n+1) i = e ⁻¹' T := by
      ext x
      change (∀ j, j ≠ i → x j < x i) ↔ ∀ j : Fin n, x (i.succAbove j) < x i
      rw [i.forall_iff_succAbove]
      simp
    have hsingle (u : ℝ) :
        (∫ y : Fin n → ℝ, T.indicator (fun _ => (1 : ℝ)) (u,y)
          ∂(Measure.pi fun _ => uniformLabel)) = (uniformLabel (Iio u)).toReal^n := by
      calc
        _ = ∫ y : Fin n → ℝ, ∏ j, (Iio u).indicator (fun _ => (1 : ℝ)) (y j)
            ∂(Measure.pi fun _ => uniformLabel) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun y => by
            dsimp only
            simp only [Set.indicator_apply,T,Set.mem_ofPred_eq,Set.mem_Iio]
            rw [Fintype.prod_boole]
            by_cases hy : ∀ j : Fin n, y j < u <;> simp [hy]
        _ = ∏ j : Fin n, ∫ t, (Iio u).indicator (fun _ => (1 : ℝ)) t ∂uniformLabel :=
          integral_fintype_prod_eq_prod _
        _ = (uniformLabel (Iio u)).toReal^n := by
          simp only [integral_indicator measurableSet_Iio,setIntegral_const,
            measureReal_def,smul_eq_mul,mul_one,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    calc
      ((Measure.pi fun _ : Fin (n+1) => uniformLabel) (winner (n+1) i)).toReal =
        ∫ x : Fin (n+1) → ℝ, (winner (n+1) i).indicator (fun _ => (1 : ℝ)) x
          ∂(Measure.pi fun _ => uniformLabel) := by
        rw [integral_indicator (winner_measurable _ _),setIntegral_const]
        simp [measureReal_def]
      _ = ∫ x : Fin (n+1) → ℝ, T.indicator (fun _ => (1 : ℝ)) (e x)
          ∂(Measure.pi fun _ => uniformLabel) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by simp [he,Set.indicator]
      _ = ∫ z : ℝ × (Fin n → ℝ), T.indicator (fun _ => (1 : ℝ)) z
          ∂(uniformLabel.prod (Measure.pi fun _ => uniformLabel)) :=
        (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => uniformLabel) i).integral_comp' _
      _ = ∫ u, ∫ y : Fin n → ℝ, T.indicator (fun _ => (1 : ℝ)) (u,y)
          ∂(Measure.pi fun _ => uniformLabel) ∂uniformLabel := by
        rw [integral_prod _ ((integrable_const (1 : ℝ)).indicator hT)]
      _ = ∫ u, (uniformLabel (Iio u)).toReal^n ∂uniformLabel := by simp_rw [hsingle]
      _ = ∫ u in Icc (0 : ℝ) 1, u^n := by
        change (∫ u in Icc (0 : ℝ) 1, (uniformLabel (Iio u)).toReal^n) = _
        apply setIntegral_congr_fun measurableSet_Icc
        intro u hu
        dsimp only
        rw [uniformLabel_Iio hu]
      _ = ∫ u in (0 : ℝ)..1, u^n := by
        rw [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le zero_le_one]
      _ = 1/((n+1 : ℕ) : ℝ) := by simpa using powerIntegral n

theorem from_children (h : Needs) : Statement := by
  intro r s hpos
  let J : Finset (Fin (r+s)) := Finset.univ.filter (fun i => i.val < r)
  have heq : {x : Fin (r+s) → ℝ | ∃ i, i.val < r ∧ ∀ j, j ≠ i → x j < x i} =
      ⋃ i ∈ J, winner (r+s) i := by
    ext x
    simp [J,winner]
  have hdisjoint : Set.PairwiseDisjoint (↑J) (winner (r+s)) := by
    intro i _ j _ hne
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact (hxi j hne.symm).not_ge (hxj i hne).le
  have hcard : J.card = r := by
    let e : {i : Fin (r+s) // i.val < r} ≃ Fin r :=
      { toFun := fun i => ⟨i.val.val,i.property⟩
        invFun := fun i => ⟨⟨i.val,by omega⟩,i.isLt⟩
        left_inv := fun _ => by ext <;> rfl
        right_inv := fun _ => rfl }
    change (Finset.univ.filter fun i : Fin (r+s) => i.val < r).card = r
    rw [← Fintype.card_subtype,Fintype.card_congr e,Fintype.card_fin]
  unfold labelWin
  change ((Measure.pi fun _ : Fin (r+s) => uniformLabel)
    {x | ∃ i : Fin (r+s), i.val < r ∧ ∀ j, j ≠ i → x j < x i}).toReal = _
  rw [heq,measure_biUnion_finset hdisjoint (fun i _ => winner_measurable _ i),
    ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)]
  simp_rw [winner_probability h.child_0]
  simp [hcard,div_eq_mul_inv,Nat.cast_add]

#print axioms from_children
end MetricDistortion.Contracts.Comparison_LabeledTie
