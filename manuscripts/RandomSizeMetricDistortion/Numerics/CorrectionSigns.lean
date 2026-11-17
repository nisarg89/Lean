import RandomSizeMetricDistortion.Statements
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
namespace MetricDistortion.Contracts.Numerics_CorrectionSigns
private def powerCoeffs (row : List ℚ) (lo hi : ℚ) : Fin 4 → ℚ :=
  let a0 := row.getD 0 0; let a1 := row.getD 1 0
  let a2 := row.getD 2 0; let a3 := row.getD 3 0
  let w := hi-lo
  ![a0+a1*lo+a2*lo^2+a3*lo^3,
    w*(a1+2*a2*lo+3*a3*lo^2), w^2*(a2+3*a3*lo), w^3*a3]

private def beta (row : List ℚ) (lo hi : ℚ) : Fin 4 → ℚ :=
  let c := powerCoeffs row lo hi
  ![c 0,c 0+c 1/3,c 0+2*c 1/3+c 2/3,c 0+c 1+c 2+c 3]

private def polyCheck (row : List ℚ) (lo hi : ℚ) : Bool :=
  decide (row.length ≤ 4 ∧ 0 ≤ beta row lo hi 0 ∧ 0 ≤ beta row lo hi 1 ∧
    0 ≤ beta row lo hi 2 ∧ 0 ≤ beta row lo hi 3)

private theorem eval_four (row : List ℚ) (hlen : row.length ≤ 4) (p : ℝ) :
    evalQPoly row p = (row.getD 0 0 : ℝ)+(row.getD 1 0 : ℝ)*p+
      (row.getD 2 0 : ℝ)*p^2+(row.getD 3 0 : ℝ)*p^3 := by
  unfold evalQPoly
  have heq : (∑ i ∈ Finset.range row.length, (row.getD i 0 : ℝ)*p^i) =
      ∑ i ∈ Finset.range 4, (row.getD i 0 : ℝ)*p^i := by
    apply Finset.sum_subset (Finset.range_mono hlen)
    intro i hi hnot
    have hbig : row.length ≤ i := Nat.le_of_not_gt (by simpa using hnot)
    rw [List.getD_eq_default row 0 hbig]
    simp
  rw [heq]
  norm_num [Finset.sum_range_succ] <;> ring

private theorem polyCheck_sound (hbern : Numerics_RationalBernstein.Statement)
    (row : List ℚ) (lo hi : ℚ) (hlohi : lo < hi) (hcheck : polyCheck row lo hi = true)
    (p : ℝ) (hp : p ∈ Icc (lo : ℝ) (hi : ℝ)) : 0 ≤ evalQPoly row p := by
  have hcheck' : row.length ≤ 4 ∧ 0 ≤ beta row lo hi 0 ∧ 0 ≤ beta row lo hi 1 ∧
      0 ≤ beta row lo hi 2 ∧ 0 ≤ beta row lo hi 3 := of_decide_eq_true hcheck
  let t : ℝ := (p-lo)/((hi : ℝ)-lo)
  have hw : 0 < (hi : ℝ)-lo := sub_pos.mpr (by exact_mod_cast hlohi)
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hp.1) hw.le
    · exact (div_le_one hw).mpr (by linarith [hp.2])
  have hrepr : p = (lo : ℝ)+((hi : ℝ)-lo)*t := by
    dsimp [t]
    field_simp
    ring
  have hb : ∀ k : Fin 4, 0 ≤ (beta row lo hi k : ℝ) := by
    intro k
    fin_cases k
    · exact_mod_cast hcheck'.2.1
    · exact_mod_cast hcheck'.2.2.1
    · exact_mod_cast hcheck'.2.2.2.1
    · exact_mod_cast hcheck'.2.2.2.2
  have hpositive := hbern 3 (fun k => (beta row lo hi k : ℝ)) hb t ht
  have heq : evalQPoly row p =
      ∑ k : Fin 4, (beta row lo hi k : ℝ)*(Nat.choose 3 k.val)*t^k.val*(1-t)^(3-k.val) := by
    rw [eval_four row hcheck'.1, hrepr]
    norm_num [Fin.sum_univ_succ,beta,powerCoeffs] <;> push_cast <;> ring
  rw [heq]
  exact hpositive

private theorem selected_cell (hcover : ∀ p ∈ Ioo (0 : ℝ) 1,
    ∃ c ∈ fixedCells, (c.lo : ℝ) ≤ p ∧ p < (c.hi : ℝ))
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ c, fixedCell p = c ∧ c ∈ fixedCells ∧ (c.lo : ℝ) ≤ p ∧ p < (c.hi : ℝ) := by
  classical
  cases hfind : fixedCells.find? (fun c => decide ((c.lo : ℝ) ≤ p ∧ p < (c.hi : ℝ))) with
  | none =>
    obtain ⟨c,hc,hbounds⟩ := hcover p hp
    have hn := List.find?_eq_none.mp hfind c hc
    exact False.elim (hn (by simpa using hbounds))
  | some c =>
    have hb : (c.lo : ℝ) ≤ p ∧ p < (c.hi : ℝ) :=
      of_decide_eq_true (List.find?_some
        (p := fun d : MassCell => decide ((d.lo : ℝ) ≤ p ∧ p < (d.hi : ℝ)))
        (l := fixedCells) hfind)
    exact ⟨c,by unfold fixedCell; rw [hfind]; rfl,List.mem_of_find?_eq_some hfind,hb.1,hb.2⟩

private def cellCheck (c : MassCell) : Bool :=
  decide (c.lo < c.hi) && polyCheck c.lambdaNum c.lo c.hi &&
    c.tauNums.all (fun row => polyCheck row c.lo c.hi)

private theorem all_checks : fixedCells.all cellCheck = true := by decide +kernel

private theorem numerator_signs (h : Needs) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    0 ≤ evalQPoly (fixedCell p).lambdaNum p ∧
    ∀ j : Fin 9, 0 ≤ evalQPoly ((fixedCell p).tauNums.getD j.val []) p := by
  obtain ⟨c,hc,hmem,hlo,hhi⟩ := selected_cell h.child_0.2.2 p hp
  have hrow := List.all_eq_true.mp all_checks c hmem
  have hrow' : c.lo < c.hi ∧ polyCheck c.lambdaNum c.lo c.hi = true ∧
      c.tauNums.all (fun row => polyCheck row c.lo c.hi) = true := by
    simpa only [cellCheck,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq] using hrow
  rw [hc]
  constructor
  · exact polyCheck_sound h.child_1 c.lambdaNum c.lo c.hi hrow'.1 hrow'.2.1 p ⟨hlo,hhi.le⟩
  · intro j
    have htau : polyCheck (c.tauNums.getD j.val []) c.lo c.hi = true := by
      by_cases hj : j.val < c.tauNums.length
      · rw [List.getD_eq_getElem c.tauNums [] hj]
        exact List.all_eq_true.mp hrow'.2.2 _ (List.getElem_mem hj)
      · rw [List.getD_eq_default c.tauNums [] (Nat.le_of_not_gt hj)]
        norm_num [polyCheck,beta,powerCoeffs]
    exact polyCheck_sound h.child_1 _ c.lo c.hi hrow'.1 htau p ⟨hlo,hhi.le⟩

theorem from_children (h : Needs) : Statement := by
  classical
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro p hp
    by_cases hp0 : p = 0
    · simp [lambdaStar,hp0]
    by_cases hp1 : p = 1
    · simp [lambdaStar,hp1]
    have hpi : p ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hp.1 (Ne.symm hp0),lt_of_le_of_ne hp.2 hp1⟩
    rw [lambdaStar,if_neg (not_or_intro hp0 hp1)]
    exact div_nonneg (numerator_signs h p hpi).1 (mul_nonneg hp.1 (sub_nonneg.mpr hp.2))
  · intro j p hp
    by_cases hp0 : p = 0
    · simp [tauStar,hp0]
    by_cases hp1 : p = 1
    · simp only [tauStar,hp1,if_neg one_ne_zero,if_pos rfl]
      fin_cases j <;> norm_num [eta,etas]
    have hpi : p ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hp.1 (Ne.symm hp0),lt_of_le_of_ne hp.2 hp1⟩
    rw [tauStar,if_neg hp0,if_neg hp1]
    exact div_nonneg ((numerator_signs h p hpi).2 j) (mul_nonneg hp.1 (sub_nonneg.mpr hp.2))
  · simp [lambdaStar]
  · simp [lambdaStar]
  · intro j
    simp [tauStar]

#print axioms from_children
end MetricDistortion.Contracts.Numerics_CorrectionSigns
