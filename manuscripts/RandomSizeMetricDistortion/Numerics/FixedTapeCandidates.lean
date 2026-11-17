import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
namespace MetricDistortion.Contracts.Numerics_FixedTapeCandidates
open MetricDistortion.FixedTape
theorem decode_add (D : Int) (A B : I) : decode D (add A B)=intervalAdd (decode D A) (decode D B) := by
  cases A; cases B
  unfold decode add intervalAdd
  congr 1 <;> push_cast <;> ring


theorem decode_neg (D : Int) (A : I) : decode D (neg A)=intervalNeg (decode D A) := by
  cases A
  unfold decode neg intervalNeg
  congr 1 <;> push_cast <;> ring


private theorem lower (D z : Int) (hD : 0 < D) :
    ((z/D : Int) : ℚ)/(D : ℚ) ≤ (z : ℚ)/(D : ℚ)^2 := by
  have hd : (0 : ℚ) < D := by exact_mod_cast hD
  have hz : ((z/D : Int) : ℚ)*(D : ℚ) ≤ (z : ℚ) := by exact_mod_cast Int.ediv_mul_le z (ne_of_gt hD)
  have hf := (le_div_iff₀ hd).2 hz
  have hh := div_le_div_of_nonneg_right hf hd.le
  convert hh using 1 <;> ring


private theorem upper (D z : Int) (hD : 0 < D) :
    (z : ℚ)/(D : ℚ)^2 ≤ ((-((-z)/D) : Int) : ℚ)/(D : ℚ) := by
  have h := lower D (-z) hD
  simpa only [Int.cast_neg,neg_div,neg_neg] using neg_le_neg h


private theorem lower_product (D z a b : Int) (hD : 0 < D) (hz : z ≤ a*b) :
    ((z/D : Int) : ℚ)/(D : ℚ) ≤ ((a : ℚ)/(D : ℚ))*((b : ℚ)/(D : ℚ)) := by
  have hh : (z : ℚ) ≤ (a : ℚ)*(b : ℚ) := by exact_mod_cast hz
  have hd : (0 : ℚ) ≤ (D : ℚ)^2 := sq_nonneg _
  have h := (lower D z hD).trans (div_le_div_of_nonneg_right hh hd)
  convert h using 1 <;> ring


private theorem upper_product (D z a b : Int) (hD : 0 < D) (hz : a*b ≤ z) :
    ((a : ℚ)/(D : ℚ))*((b : ℚ)/(D : ℚ)) ≤ ((-((-z)/D) : Int) : ℚ)/(D : ℚ) := by
  have hh : (a : ℚ)*(b : ℚ) ≤ (z : ℚ) := by exact_mod_cast hz
  have hd : (0 : ℚ) ≤ (D : ℚ)^2 := sq_nonneg _
  have h := (div_le_div_of_nonneg_right hh hd).trans (upper D z hD)
  convert h using 1 <;> ring


theorem mul_encloses (D : Int) (hD : 0 < D) (A B : I) :
    intervalEncloses (decode D (mul D A B)) (intervalMul (decode D A) (decode D B)) = true := by
  apply decide_eq_true_iff.mpr
  dsimp [decode,mul,intervalMul]
  constructor
  · apply le_min
    · apply le_min
      · apply lower_product D _ _ _ hD
        exact (min_le_left _ _).trans (min_le_left _ _)
      · apply lower_product D _ _ _ hD
        exact (min_le_left _ _).trans (min_le_right _ _)
    · apply le_min
      · apply lower_product D _ _ _ hD
        exact (min_le_right _ _).trans (min_le_left _ _)
      · apply lower_product D _ _ _ hD
        exact (min_le_right _ _).trans (min_le_right _ _)
  · apply max_le
    · apply max_le
      · apply upper_product D _ _ _ hD
        exact (le_max_left _ _).trans (le_max_left _ _)
      · apply upper_product D _ _ _ hD
        exact (le_max_right _ _).trans (le_max_left _ _)
    · apply max_le
      · apply upper_product D _ _ _ hD
        exact (le_max_left _ _).trans (le_max_right _ _)
      · apply upper_product D _ _ _ hD
        exact (le_max_right _ _).trans (le_max_right _ _)


private theorem floor_le_div (a b : Int) (hb : 0 < b) :
    ((a/b : Int) : ℚ) ≤ (a : ℚ)/(b : ℚ) := by
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  apply (le_div_iff₀ hbq).2
  exact_mod_cast Int.ediv_mul_le a (ne_of_gt hb)


theorem fromQ_encloses (D : Int) (hD : 0 < D) (q : ℚ) :
    intervalEncloses (decode D (fromQ D q)) ⟨q,q⟩ = true := by
  have hd : (0 : ℚ) < D := by exact_mod_cast hD
  have hden : (0 : Int) < q.den := by exact_mod_cast q.den_pos
  have hq : ((q.num*D : Int) : ℚ)/((q.den : Int) : ℚ)=q*(D : ℚ) := by
    push_cast
    rw [← div_mul_eq_mul_div, Rat.num_div_den]
  have hqn : (((-q.num)*D : Int) : ℚ)/((q.den : Int) : ℚ)= -q*(D : ℚ) := by
    push_cast
    rw [neg_mul,neg_div,← div_mul_eq_mul_div,Rat.num_div_den]
    ring
  apply decide_eq_true_iff.mpr
  dsimp [decode,fromQ]
  constructor
  · apply (div_le_iff₀ hd).2
    simpa only [hq] using floor_le_div (q.num*D) (q.den : Int) hden
  · apply (le_div_iff₀ hd).2
    have hf := floor_le_div ((-q.num)*D) (q.den : Int) hden
    rw [hqn] at hf
    push_cast
    linarith


theorem decode_zero (D : Int) : decode D zero = ⟨0,0⟩ := by simp [decode,zero]

theorem decode_zeroRow (D : Int) : decodeRow D zeroRow = zeroTapeBounds := by
  simp only [decodeRow,zeroRow,decode_zero,zeroTapeBounds]


theorem decode_get (D : Int) (done : List Row) (i : Nat) :
    ((done.map (decodeRow D)).getD i zeroTapeBounds) = decodeRow D (done.getD i zeroRow) := by
  rw [← decode_zeroRow D]
  exact List.getD_map done zeroRow (decodeRow D)


private theorem encloses_self (A : QInterval) : intervalEncloses A A = true := by simp [intervalEncloses]

private theorem encloses_add {A C A' C' : QInterval}
    (hA : intervalEncloses A' A = true) (hC : intervalEncloses C' C = true) :
    intervalEncloses (intervalAdd A' C') (intervalAdd A C) = true := by
  have ha : A'.lo ≤ A.lo ∧ A.hi ≤ A'.hi := of_decide_eq_true hA
  have hc : C'.lo ≤ C.lo ∧ C.hi ≤ C'.hi := of_decide_eq_true hC
  apply decide_eq_true_iff.mpr
  exact ⟨add_le_add ha.1 hc.1,add_le_add ha.2 hc.2⟩


private theorem step_encloses (D : Int) (hD : 0 < D) (B : Fin 4 → I) (done : List Row) (op : TapeOp) :
    tapeBoundsEnclose (decodeRow D (FixedTape.step D B done op))
      (tapeExpected (decodeBox D B) (done.map (decodeRow D)) op) = true := by
  have hd : (D : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hD
  cases op with
  | const q =>
    apply Bool.and_eq_true_iff.mpr
    refine ⟨fromQ_encloses D hD q,?_⟩
    apply List.all_eq_true.mpr
    intro i _
    simp [decodeRow,FixedTape.step,constRow,varRow,negRow,addRow,mulRow,decode_zero,tapeExpected,intervalEncloses]
  | var i =>
    apply Bool.and_eq_true_iff.mpr
    refine ⟨encloses_self _,?_⟩
    apply List.all_eq_true.mpr
    intro j _
    by_cases hij : i=j
    · subst j; simp [decodeRow,FixedTape.step,constRow,varRow,negRow,addRow,mulRow,decode,decodeBox,tapeExpected,hd,intervalEncloses]
    · simp [decodeRow,FixedTape.step,constRow,varRow,negRow,addRow,mulRow,decode_zero,decodeBox,tapeExpected,hij,intervalEncloses]
  | neg a =>
    simp only [tapeExpected,decode_get,FixedTape.step,constRow,varRow,negRow,addRow,mulRow,decodeRow,decode_neg,tapeBoundsEnclose,
      encloses_self,Bool.true_and]
    exact List.all_eq_true.mpr (fun _ _ => rfl)
  | add a b =>
    simp only [tapeExpected,decode_get,FixedTape.step,constRow,varRow,negRow,addRow,mulRow,decodeRow,decode_add,tapeBoundsEnclose,
      encloses_self,Bool.true_and]
    exact List.all_eq_true.mpr (fun _ _ => rfl)
  | mul a b =>
    apply Bool.and_eq_true_iff.mpr
    constructor
    · simpa only [FixedTape.step,constRow,varRow,negRow,addRow,mulRow,decodeRow,tapeExpected,decode_get] using
        mul_encloses D hD (done.getD a zeroRow).value (done.getD b zeroRow).value
    · apply List.all_eq_true.mpr
      intro i _
      simpa only [FixedTape.step,constRow,varRow,negRow,addRow,mulRow,decodeRow,tapeExpected,decode_get,decode_add] using
        encloses_add (mul_encloses D hD ((done.getD a zeroRow).gradient i) (done.getD b zeroRow).value)
          (mul_encloses D hD (done.getD a zeroRow).value ((done.getD b zeroRow).gradient i))


theorem rows_checked (D : Int) (hD : 0 < D) (B : Fin 4 → I) (done : List Row) (ops : List TapeOp)
    (hv : tapeRefsValidAux done.length ops = true) :
    tapeCheckAux (decodeBox D B) (done.map (decodeRow D)) ops
      ((rowsAux D B done ops).map (decodeRow D)) = true := by
  induction ops generalizing done with
  | nil => rfl
  | cons op ops ih =>
    have hb : tapeRefsValid done.length op = true ∧ tapeRefsValidAux (done.length+1) ops = true := by
      simpa only [tapeRefsValidAux,Bool.and_eq_true_iff] using hv
    simp only [rowsAux,List.map_cons,tapeCheckAux,List.length_map,hb.1,step_encloses D hD,
      Bool.true_and]
    simpa only [List.map_append,List.map_singleton] using
      ih (done++[FixedTape.step D B done op]) (by simpa using hb.2)

theorem decode_abs (D z : ℤ) (hD : 0 < D) :
    |(z : ℚ)/(D : ℚ)| = (z.natAbs : ℚ)/(D : ℚ) := by
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  simp only [abs_div,abs_of_pos hDq,Nat.cast_natAbs,Int.cast_abs]


theorem decode_max (D a b : ℤ) (hD : 0 < D) :
    max |(a : ℚ)/(D : ℚ)| |(b : ℚ)/(D : ℚ)| =
      (max a.natAbs b.natAbs : ℚ)/(D : ℚ) := by
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  rw [decode_abs D a hD,decode_abs D b hD,
    max_div_div_right hDq.le]


theorem centered_identity (D c : ℤ) (gl gu bl bu : Fin 4 → ℤ) (hD : 0 < D) :
    (2*(D : ℚ)^2)*((c : ℚ)/(D : ℚ) +
      ∑ i : Fin 4, max |(gl i : ℚ)/(D : ℚ)| |(gu i : ℚ)/(D : ℚ)| *
        (((bu i : ℚ)/(D : ℚ))-((bl i : ℚ)/(D : ℚ)))/2) =
      ((2*D*c + ∑ i : Fin 4,
        (max (gl i).natAbs (gu i).natAbs : ℤ)*(bu i-bl i) : ℤ) : ℚ) := by
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hDz : (D : ℚ) ≠ 0 := ne_of_gt hDq
  simp_rw [decode_max D _ _ hD]
  calc
    _ = 2*(D : ℚ)*(c : ℚ) + ∑ i : Fin 4,
        (max (gl i).natAbs (gu i).natAbs : ℚ)*((bu i : ℚ)-(bl i : ℚ)) := by
      rw [mul_add,Finset.mul_sum]
      congr 1
      · field_simp [hDz] <;> ring
      · apply Finset.sum_congr rfl
        intro i _
        field_simp [hDz] <;> ring
    _ = _ := by
      simp only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_sum,
        Int.cast_sub,Int.cast_max,Int.cast_natCast]


theorem centered_nonpos (D c : ℤ) (gl gu bl bu : Fin 4 → ℤ) (hD : 0 < D)
    (h : 2*D*c + ∑ i : Fin 4,
      (max (gl i).natAbs (gu i).natAbs : ℤ)*(bu i-bl i) ≤ 0) :
    (c : ℚ)/(D : ℚ) +
      ∑ i : Fin 4, max |(gl i : ℚ)/(D : ℚ)| |(gu i : ℚ)/(D : ℚ)| *
        (((bu i : ℚ)/(D : ℚ))-((bl i : ℚ)/(D : ℚ)))/2 ≤ 0 := by
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hcast : ((2*D*c + ∑ i : Fin 4,
      (max (gl i).natAbs (gu i).natAbs : ℤ)*(bu i-bl i) : ℤ) : ℚ) ≤ 0 := by
    exact_mod_cast h
  rw [← centered_identity D c gl gu bl bu hD] at hcast
  apply le_of_mul_le_mul_left ?_ (show (0 : ℚ) < 2*(D : ℚ)^2 by positivity)
  simpa only [mul_zero] using hcast

theorem decode_midpoint (D lo hi : ℤ) (heven : 2 ∣ lo+hi) :
    ((((lo+hi)/2 : ℤ) : ℚ)/(D : ℚ)) =
      (((lo : ℚ)/(D : ℚ))+((hi : ℚ)/(D : ℚ)))/2 := by
  rw [Int.cast_div_charZero heven]
  push_cast
  ring


theorem decode_nonpos (D z : ℤ) (hD : 0 < D) (hz : z ≤ 0) :
    (z : ℚ)/(D : ℚ) ≤ 0 := by
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hzq : (z : ℚ) ≤ 0 := by exact_mod_cast hz
  apply (div_le_iff₀ hDq).2
  simpa only [zero_mul] using hzq


theorem decode_nonneg (D z : ℤ) (hD : 0 < D) (hz : 0 ≤ z) :
    0 ≤ (z : ℚ)/(D : ℚ) := by
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hzq : (0 : ℚ) ≤ z := by exact_mod_cast hz
  apply (le_div_iff₀ hDq).2
  simpa only [zero_mul] using hzq


private theorem centered_checked (D : ℤ) (hD : 0 < D) (B : Fin 4 → I) (root : ℕ) (rows centers : List Row)
    (h : centeredNumerator D B root rows centers ≤ 0) :
    tapeCenteredBound (decodeBox D B) root
      (rows.map (decodeRow D)) (centers.map (decodeRow D)) ≤ 0 := by
  have hh := centered_nonpos D (centers.getD root zeroRow).value.hi
    (fun i => ((rows.getD root zeroRow).gradient i).lo)
    (fun i => ((rows.getD root zeroRow).gradient i).hi)
    (fun i => (B i).lo) (fun i => (B i).hi) hD h
  simpa only [tapeCenteredBound,decode_get,decodeRow,decodeBox,decode] using hh

private theorem midpoint_checked (D : ℤ) (B : Fin 4 → I)
    (heven : ∀ i, 2 ∣ (B i).lo+(B i).hi) :
    midpointBox (decodeBox D B) = decodeBox D (midBox B) := by
  funext i
  dsimp [midpointBox,decodeBox,midBox,decode]
  rw [decode_midpoint D _ _ (heven i)]

private theorem box_checked (D : ℤ) (hD : 0 < D) (B : Fin 4 → I)
    (hB : ∀ i, (B i).lo ≤ (B i).hi) : ValidBox (decodeBox D B) := by
  have hd : (0 : ℚ) ≤ D := by exact_mod_cast hD.le
  intro i
  exact div_le_div_of_nonneg_right (by exact_mod_cast hB i) hd

theorem proved : Statement := by
  refine ⟨?_,centered_checked,midpoint_checked,?_,box_checked⟩
  · intro D hD B tape hv
    exact rows_checked D hD B [] tape hv
  · intro D z hD
    exact ⟨decode_nonpos D z hD,decode_nonneg D z hD⟩

#print axioms proved
end MetricDistortion.Contracts.Numerics_FixedTapeCandidates
