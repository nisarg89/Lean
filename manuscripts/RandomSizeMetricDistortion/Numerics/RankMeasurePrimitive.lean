import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Numerics_RankMeasurePrimitive

set_option maxHeartbeats 8000000

private theorem shift_identity (j : Fin 9) :
    cutoff j+eta j*psiStar (cutoff j) = -shift j := by
  fin_cases j <;> norm_num [cutoff,cutoffs,eta,etas,psiStar,muStar,phiStar,shift,shifts]

private theorem phi_derivative (x : ℝ) : HasDerivAt phiStar (phiStarDeriv x) x := by
  have hd := (((hasDerivAt_id x).const_mul (19/73 : ℝ)).add
    ((hasDerivAt_pow 2 x).const_mul (35/146 : ℝ))).add
      ((hasDerivAt_pow 32 x).div_const 2)
  norm_num only [Nat.cast_ofNat] at hd
  have hcoef : (19/73 : ℝ)+(35/146 : ℝ)*(2*x^1)+(32*x^31)/2 =
      phiStarDeriv x := by norm_num [phiStarDeriv] <;> ring
  rw [hcoef] at hd
  rw [hasDerivAt_iff_isLittleO] at hd ⊢
  simpa only [phiStar,Pi.add_apply,smul_eq_mul,id_eq] using hd

private theorem density_integral (j : Fin 9) (x : ℝ) (hx : bStar ≤ x) :
    (∫ z in Ioo bStar x, (eta j*phiStarDeriv z-1)) =
      eta j*(phiStar x-phiStar bStar)-(x-bStar) := by
  let f : ℝ → ℝ := fun z => eta j*phiStarDeriv z-1
  let g : ℝ → ℝ := fun z => eta j*phiStar z-z
  have hc : Continuous f := by dsimp [f,phiStarDeriv]; fun_prop
  have hd : ∀ z, HasDerivAt g (f z) z := by
    intro z
    have hd := ((phi_derivative z).const_mul (eta j)).sub (hasDerivAt_id z)
    rw [hasDerivAt_iff_isLittleO] at hd ⊢
    simpa only [f,g,Pi.sub_apply,smul_eq_mul,id_eq] using hd
  change (∫ z in Ioo bStar x, f z) = _
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hx]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hd z)
    (hc.intervalIntegrable _ _)]
  dsimp [g]
  ring

private theorem cumulative (h : Needs) (j : Fin 9) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (nuStar j (Ico 0 x)).toReal = rankPotential j x := by
  rw [h.child_0 j 0 x le_rfl hx0 hx1]
  have hb0 : 0 ≤ bStar := by norm_num [bStar]
  have hs := h.child_2 j
  by_cases hxb : x ≤ bStar
  · have he : Ico (0 : ℝ) x ∩ Ioo bStar (cutoff j) = ∅ := by
      ext z
      simp only [mem_inter_iff,mem_Ico,mem_Ioo,mem_empty_iff_false,iff_false,not_and]
      intro hz hz'
      linarith
    simp [rankPotential,hxb,he,not_lt.mpr hxb]
  · have hbx : bStar < x := lt_of_not_ge hxb
    by_cases hxh : x ≤ cutoff j
    · have he : Ico (0 : ℝ) x ∩ Ioo bStar (cutoff j) = Ioo bStar x := by
        ext z
        simp only [mem_inter_iff,mem_Ico,mem_Ioo]
        constructor
        · rintro ⟨hz,hz'⟩; exact ⟨hz'.1,hz.2⟩
        · rintro ⟨hz,hz'⟩; exact ⟨⟨hb0.trans hz.le,hz'⟩,⟨hz,hz'.trans_le hxh⟩⟩
      rw [he,density_integral j x hbx.le]
      simp only [hb0,hbx,and_self,ite_true,rankPotential,hxb,ite_false,hxh]
      have hi := shift_identity j
      dsimp [atom,psiStar] at hi ⊢
      linarith
    · have hhx : cutoff j < x := lt_of_not_ge hxh
      have he : Ico (0 : ℝ) x ∩ Ioo bStar (cutoff j) = Ioo bStar (cutoff j) := by
        ext z
        simp only [mem_inter_iff,mem_Ico,mem_Ioo]
        constructor
        · exact And.right
        · rintro ⟨hz,hz'⟩
          exact ⟨⟨hb0.trans hz.le,hz'.trans hhx⟩,⟨hz,hz'⟩⟩
      rw [he,density_integral j (cutoff j) hs.1.le]
      simp only [hb0,hbx,and_self,ite_true,rankPotential,hxb,ite_false,hxh]
      unfold atom
      ring

private theorem mass_finite (h : Needs) (j : Fin 9) {S : Set ℝ}
    (hS : S ⊆ Icc (0 : ℝ) 1) : nuStar j S ≠ ⊤ := by
  apply ne_of_lt
  exact (measure_mono hS).trans_lt (by rw [(h.child_1 j).1]; exact ENNReal.ofReal_lt_top)

private theorem interval_mass (h : Needs) (j : Fin 9) (a A : ℝ)
    (ha : 0 ≤ a) (haA : a ≤ A) (hA : A ≤ 1) :
    (nuStar j (Ico a A)).toReal = rankPotential j A-rankPotential j a := by
  have hd : Disjoint (Ico (0 : ℝ) a) (Ico a A) := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact (not_lt_of_ge hz'.1) hz.2
  have hm := measure_union (μ := nuStar j) hd measurableSet_Ico
  rw [Ico_union_Ico_eq_Ico ha haA] at hm
  have hfin0 : nuStar j (Ico 0 a) ≠ ⊤ :=
    mass_finite h j (fun z hz => ⟨hz.1,hz.2.le.trans (haA.trans hA)⟩)
  have hfin1 : nuStar j (Ico a A) ≠ ⊤ :=
    mass_finite h j (fun z hz => ⟨ha.trans hz.1,hz.2.le.trans hA⟩)
  have hreal := congrArg ENNReal.toReal hm
  rw [ENNReal.toReal_add hfin0 hfin1,cumulative h j A (ha.trans haA) hA,
    cumulative h j a ha (haA.trans hA)] at hreal
  linarith

private theorem tail_mass (h : Needs) (j : Fin 9) (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (nuStar j (Icc a 1)).toReal = cStar-rankPotential j a := by
  have hd : Disjoint (Ico (0 : ℝ) a) (Icc a 1) := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact (not_lt_of_ge hz'.1) hz.2
  have hm := measure_union (μ := nuStar j) hd measurableSet_Icc
  rw [Ico_union_Icc_eq_Icc ha ha1,(h.child_1 j).1] at hm
  have hfin0 : nuStar j (Ico 0 a) ≠ ⊤ :=
    mass_finite h j (fun z hz => ⟨hz.1,hz.2.le.trans ha1⟩)
  have hfin1 : nuStar j (Icc a 1) ≠ ⊤ :=
    mass_finite h j (fun z hz => ⟨ha.trans hz.1,hz.2⟩)
  have hreal := congrArg ENNReal.toReal hm
  rw [ENNReal.toReal_add hfin0 hfin1,cumulative h j a ha ha1,
    ENNReal.toReal_ofReal (by norm_num [cStar])] at hreal
  linarith

theorem from_children (h : Needs) : Statement := by
  exact ⟨interval_mass h,tail_mass h⟩

#print axioms from_children
end MetricDistortion.Contracts.Numerics_RankMeasurePrimitive
