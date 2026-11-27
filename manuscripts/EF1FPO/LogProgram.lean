import EF1FPO.Algorithm
import EF1FPO.HeaderProcedures
import EF1FPO.LogSeries
import EF1FPO.ProcedureTime
import OAI.Computability.QuantumFactoring.BitStackRationalDivision
import OAI.Optimization.LinearProgramming.OracleSpec.Arithmetic
import OAI.Optimization.LinearProgramming.OracleSpec.GuardedIteration
import OAI.Optimization.LinearProgramming.PriceGame.TrialWeightArithmetic

/-! Normalize a rational, use the checked series twice, and serialize its approximation. -/

set_option autoImplicit false

namespace EF1FPO

open OAI.ExactQuantumFactoring.BitStackProgram
open OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec
open PricePacketProcedures

def logNormalize (d : LogInput) : ℤ × (ℚ × ℕ) :=
  let numeratorBits := d.q.num.natAbs.size
  let denominatorBits := d.q.den.size
  let rawExponent := (numeratorBits : ℤ) - denominatorBits
  let shifted := d.q * ((2 : ℚ) ^ denominatorBits / 2 ^ numeratorBits)
  let termCount := d.precision + (numeratorBits + denominatorBits + 2)
  if shifted < 1 then (rawExponent - 1, 2 * shifted, termCount)
  else (rawExponent, shifted, termCount)

def logApproximation (d : LogInput) : ℚ :=
  let data := logNormalize d
  data.1 * logSeries 2 data.2.2 + logSeries data.2.1 data.2.2

theorem logNormalize_correct (d : LogInput) :
    let data := logNormalize d
    (1 ≤ data.2.1 ∧ data.2.1 ≤ 2) ∧
      Real.log (d.q : ℝ) = (data.1 : ℝ) * Real.log 2 + Real.log (data.2.1 : ℝ) ∧
      data.1.natAbs + 1 ≤ d.q.num.natAbs.size + d.q.den.size + 2 ∧
      data.2.2 = d.precision + (d.q.num.natAbs.size + d.q.den.size + 2) := by
  let num := d.q.num.natAbs
  let den := d.q.den
  let n := num.size
  let m := den.size
  let exponent : ℤ := (n : ℤ) - m
  let shifted : ℚ := d.q * ((2 : ℚ) ^ m / 2 ^ n)
  let terms := d.precision + (n + m + 2)
  have hq : 0 < d.q := d.positive
  have hNum : 0 < d.q.num := Rat.num_pos.mpr hq
  have hNumPos : 0 < num := Int.natAbs_pos.mpr hNum.ne'
  have hDenPos : 0 < den := d.q.den_pos
  have castNum : (num : ℤ) = d.q.num := Int.natAbs_of_nonneg hNum.le
  have rationalValue : (num : ℚ) / den = d.q := by
    rw [← Int.cast_natCast, castNum]
    exact Rat.num_div_den _
  have normalize (value : ℕ) (positive : 0 < value) :
      (1 / 2 : ℚ) ≤ (value : ℚ) / 2 ^ value.size ∧ (value : ℚ) / 2 ^ value.size < 1 := by
    have hSize := Nat.size_pos.mpr positive
    have hLower : 2 ^ (value.size - 1) ≤ value := Nat.lt_size.mp (by omega)
    have hPower : (2 : ℚ) ^ value.size ≤ 2 * (value : ℚ) := by
      have doubled := Nat.mul_le_mul_left 2 hLower
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ value.size)] at doubled
      exact_mod_cast doubled
    have hDiv : (0 : ℚ) < 2 ^ value.size := by positivity
    refine ⟨(le_div_iff₀ hDiv).mpr (by linarith), (div_lt_iff₀ hDiv).mpr ?_⟩
    rw [one_mul]
    exact_mod_cast Nat.lt_size_self value
  have hNormalizedNum := normalize num hNumPos
  have hNormalizedDen := normalize den hDenPos
  have scaleAsRatio : shifted = ((num : ℚ) / 2 ^ n) / ((den : ℚ) / 2 ^ m) := by
    unfold shifted
    rw [← rationalValue]
    have hDenominator : (den : ℚ) ≠ 0 := by exact_mod_cast hDenPos.ne'
    field_simp [hDenominator]
  have hDivisor : 0 < (den : ℚ) / 2 ^ m := by positivity
  have hLow : (1 / 2 : ℚ) < shifted := by
    rw [scaleAsRatio]
    apply (lt_div_iff₀ hDivisor).mpr
    exact by linarith only [hNormalizedNum.1, hNormalizedDen.2]
  have hHigh : shifted < 2 := by
    rw [scaleAsRatio]
    apply (div_lt_iff₀ hDivisor).mpr
    exact by linarith only [hNormalizedNum.2, hNormalizedDen.1]
  have qReal : 0 < (d.q : ℝ) := by exact_mod_cast hq
  have shiftedReal : 0 < (shifted : ℝ) := by exact_mod_cast (show 0 < shifted by linarith)
  have logShifted :
      Real.log (d.q : ℝ) = (exponent : ℝ) * Real.log 2 + Real.log (shifted : ℝ) := by
    have hCast : (shifted : ℝ) = (d.q : ℝ) * ((2 : ℝ) ^ m / 2 ^ n) := by simp [shifted]
    have castExponent : (exponent : ℝ) = (n : ℝ) - (m : ℝ) := by simp [exponent]
    rw [hCast, Real.log_mul qReal.ne' (by positivity), Real.log_div (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, castExponent]
    ring
  have hAbs : exponent.natAbs ≤ n + m := by
    simpa only [exponent, Int.natAbs_natCast] using Int.natAbs_sub_le (n : ℤ) (m : ℤ)
  have hDefinition : logNormalize d =
      if shifted < 1 then (exponent - 1, 2 * shifted, terms) else (exponent, shifted, terms) := rfl
  dsimp only
  rw [hDefinition]
  by_cases fit : shifted < 1
  · rw [ite_eq_left fit]
    have hExp : (exponent - 1).natAbs + 1 ≤ n + m + 2 := by
      have h := Int.natAbs_sub_le exponent 1
      norm_num at h
      omega
    refine ⟨⟨by linarith only [hLow], by linarith only [fit]⟩, ?_, hExp, rfl⟩
    rw [Rat.cast_mul, Rat.cast_ofNat, Real.log_mul (by norm_num) shiftedReal.ne',
      Int.cast_sub, Int.cast_one, logShifted]
    ring
  · rw [ite_eq_right fit]
    refine ⟨⟨le_of_not_gt fit, hHigh.le⟩, logShifted, ?_, rfl⟩
    change exponent.natAbs + 1 ≤ n + m + 2
    omega

theorem logApproximation_correct (d : LogInput) :
    |(logApproximation d : ℝ) - Real.log (d.q : ℝ)| ≤ precisionError d.precision := by
  let data := logNormalize d
  let extra := d.q.num.natAbs.size + d.q.den.size + 2
  rcases logNormalize_correct d with ⟨range, decomposition, exponentBound, termCount⟩
  have hUnitError := logSeries_error data.2.1 data.2.2 range.1 range.2
  have hTwoError := logSeries_error 2 data.2.2 (by norm_num) (by norm_num)
  have hExp : data.1.natAbs + 1 ≤ 2 ^ extra :=
    exponentBound.trans (show extra < 2 ^ extra from Nat.lt_two_pow_self).le
  have hCoeff : |(data.1 : ℝ)| + 1 ≤ (2 : ℝ) ^ extra := by
    have hCast : ((data.1.natAbs + 1 : ℕ) : ℝ) ≤ ((2 ^ extra : ℕ) : ℝ) := by
      exact_mod_cast hExp
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_natAbs, Int.cast_abs, Nat.cast_pow,
      Nat.cast_ofNat] using hCast
  have hPrecision : 0 ≤ precisionError data.2.2 := by unfold precisionError; positivity
  have hCancel : (2 : ℝ) ^ extra * precisionError data.2.2 = precisionError d.precision := by
    unfold precisionError
    rw [show data.2.2 = d.precision + extra from termCount, pow_add]
    have h₁ : (2 : ℝ) ^ extra ≠ 0 := by positivity
    have h₂ : (2 : ℝ) ^ d.precision ≠ 0 := by positivity
    dsimp [extra] at h₁ ⊢
    field_simp [h₁, h₂]
    simp only [pow_add]
    ring
  have hCast : (logApproximation d : ℝ) =
      (data.1 : ℝ) * (logSeries 2 data.2.2 : ℝ) + (logSeries data.2.1 data.2.2 : ℝ) := by
    simp [logApproximation, data]
  let errorTwo := (logSeries 2 data.2.2 : ℝ) - Real.log 2
  let errorUnit := (logSeries data.2.1 data.2.2 : ℝ) - Real.log (data.2.1 : ℝ)
  have hError :
      (logApproximation d : ℝ) - Real.log (d.q : ℝ) = (data.1 : ℝ) * errorTwo + errorUnit := by
    rw [hCast, show Real.log (d.q : ℝ) =
      (data.1 : ℝ) * Real.log 2 + Real.log (data.2.1 : ℝ) from decomposition]
    dsimp only [errorTwo, errorUnit]
    ring
  rw [hError]
  calc
    |(data.1 : ℝ) * errorTwo + errorUnit| ≤ |(data.1 : ℝ) * errorTwo| + |errorUnit| :=
      abs_add_le _ _
    _ = |(data.1 : ℝ)| * |errorTwo| + |errorUnit| := by rw [abs_mul]
    _ ≤ (|(data.1 : ℝ)| + 1) * precisionError data.2.2 := by
      rw [add_mul, one_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hTwoError (abs_nonneg _)) hUnitError
    _ ≤ (2 : ℝ) ^ extra * precisionError data.2.2 := mul_le_mul_of_nonneg_right hCoeff hPrecision
    _ = precisionError d.precision := hCancel

abbrev UnitLogInput := {a : ℚ // 1 ≤ a ∧ a ≤ 2} × ℕ

def encodeUnitLogInput (d : UnitLogInput) : Word :=
  prodCode ratCode unaryCode (d.1.val, d.2)

noncomputable def logNormalizedP :
    Procedure encodeLogInput (prodCode intCode (prodCode ratCode unaryCode)) logNormalize := by
  let data : Procedure encodeLogInput nativeRatField (fun d => (d.q, encodeUnary d.precision)) :=
    decodeRatField.precompose (fun d : LogInput => (d.q, encodeUnary d.precision))
  let q := (first ratCode id).comp data
  let rawPrecision := (second ratCode id).comp data
  let decodeCount : Procedure (fun d : LogInput => encodeUnary d.precision) (prodCode unaryCode id)
      (fun d => (d.precision, [])) :=
    (decodeUnaryField.precompose (fun d : LogInput => (d.precision, []))).congrEncoding
      (by intro d; simp [rawUnaryField, encodeUnary]) (fun _ => rfl)
  let count := (first unaryCode id).comp (readSuffix rawPrecision decodeCount)
  let absolute : Procedure intCode Nat.bits Int.natAbs :=
    (second boolCode Nat.bits).precompose intData
  let binarySize : Procedure Nat.bits unaryCode Nat.size :=
    (Fuel.lengthInUnary Nat.bits).congrFun Nat.size_eq_bits_len
  let numeratorBits := binarySize.comp (absolute.comp (ratNum.comp q))
  let denominatorBits := binarySize.comp (ratDen.comp q)
  let unaryInt := natToInt.comp unaryToBits
  let exponent := intSub.comp ((unaryInt.comp numeratorBits).pair (unaryInt.comp denominatorBits))
  let power := natToRat.comp powTwo
  let scale := ratDiv.comp ((power.comp denominatorBits).pair (power.comp numeratorBits))
  let shifted := ratMul.comp (q.pair scale)
  let totalBits := unaryAdd.comp (numeratorBits.pair denominatorBits)
  let padding := unaryAdd.comp (totalBits.pair (constant encodeLogInput unaryCode 2))
  let terms := unaryAdd.comp (count.pair padding)
  let noShift := exponent.pair (shifted.pair terms)
  let decrease := intSub.comp (exponent.pair (constant encodeLogInput intCode (1 : ℤ)))
  let double := ratMul.comp ((constant encodeLogInput ratCode (2 : ℚ)).pair shifted)
  let shift := decrease.pair (double.pair terms)
  let needsNoShift := Arithmetic.ratLe.comp ((constant encodeLogInput ratCode (1 : ℚ)).pair shifted)
  exact (conditional needsNoShift noShift shift).congrFun (by
    intro d
    by_cases h : d.q * ((2 : ℚ) ^ d.q.den.size / 2 ^ d.q.num.natAbs.size) < 1
    · simp [Function.comp_apply, logNormalize, Nat.cast_pow, h, not_le_of_gt h]
    · simp [Function.comp_apply, logNormalize, Nat.cast_pow, h, le_of_not_gt h])

set_option maxHeartbeats 1000000 in
noncomputable def logSeriesP :
    Procedure encodeUnitLogInput ratCode (fun d => logSeries d.1.val d.2) := by
  let State := {x : ℚ // 0 ≤ x ∧ x ≤ 1} × ℕ
  let term (x : ℚ) (i : ℕ) := x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℚ)
  let halfSeries (x : ℚ) (n : ℕ) := ∑ i ∈ Finset.range n, term x i
  let valuesCode := prodCode ratCode ratCode
  let indexCode := prodCode unaryCode valuesCode
  let fields (s : State) := (s.1.val, s.2, s.1.val ^ (2 * s.2 + 1), halfSeries s.1.val s.2)
  let stateCode (s : State) := prodCode ratCode indexCode (fields s)
  let advance (s : State) : State := (s.1, s.2 + 1)
  let readBase := (first ratCode indexCode).precompose fields
  let remainder := (second ratCode indexCode).precompose fields
  let readIndex := (first unaryCode valuesCode).comp remainder
  let values := (second unaryCode valuesCode).comp remainder
  let readPower := (first ratCode ratCode).comp values
  let readSum := (second ratCode ratCode).comp values
  let nextIndex := unarySuccessor.comp readIndex
  let twiceIndex := unaryAdd.comp (readIndex.pair readIndex)
  let divisor := natToRat.comp (unaryToBits.comp (unarySuccessor.comp twiceIndex))
  let contribution := ratDiv.comp (readPower.pair divisor)
  let nextSum := ratAdd.comp (readSum.pair contribution)
  let baseSquared := ratMul.comp (readBase.pair readBase)
  let nextPower := ratMul.comp (readPower.pair baseSquared)
  let stepP : Procedure stateCode stateCode advance :=
    (readBase.pair (nextIndex.pair (nextPower.pair nextSum))).result (by
      intro s
      have hPower : s.1.val ^ (2 * s.2 + 1) * (s.1.val * s.1.val) =
          s.1.val ^ (2 * (s.2 + 1) + 1) := by
        rw [← pow_two, ← pow_add]
        congr 1 <;> omega
      have hSum : halfSeries s.1.val (s.2 + 1) =
          halfSeries s.1.val s.2 + term s.1.val s.2 := by
        exact Finset.sum_range_succ _ _
      have hPower' := hPower
      simp only [two_mul] at hPower'
      simp [stateCode, fields, advance, indexCode, valuesCode, Function.comp_apply,
        Nat.succ_eq_add_one, hPower', hSum, term, two_mul])
  have iterateIndex (s : State) (i : ℕ) : (advance^[i]) s = (s.1, s.2 + i) := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih]
      rfl
  let X : Polynomial ℕ := Polynomial.X
  let denominatorWidth := (X + 1) * ((X + 1) * (2 * X + 1))
  let width := 10 * denominatorWidth + 10 * X + 40
  have fits (n : ℕ) (s : State) (i : ℕ) (hi : i ≤ n) :
      (stateCode ((advance^[i]) s)).length ≤ width.eval (n + (stateCode s).length) := by
    let L := n + (stateCode s).length
    let k := s.2 + i
    let x := s.1.val
    let B := (L + 1) * (2 * L + 1)
    let D := (L + 1) * B
    have hNativeBase : (ratCode x).length ≤ (stateCode s).length := by
      simp only [stateCode, fields, prodCode, pairBits_length, x]
      omega
    have hIndex : s.2 ≤ (stateCode s).length := by
      simp only [stateCode, fields, indexCode, prodCode, pairBits_length, unaryCode, List.length_replicate]
      omega
    have hK : k ≤ L := by dsimp [k, L]; omega
    have hLBase : (ratCode x).length ≤ L := hNativeBase.trans (Nat.le_add_left _ _)
    have hDenSize : x.den.size ≤ L := by
      have hEq := Nat.size_eq_bits_len x.den
      simp only [ratCode, prodCode, pairBits_length] at hLBase
      omega
    have hBaseDen : x.den ≤ 2 ^ L :=
      (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hDenSize)
    have hBaseNat : 0 ≤ x := s.1.property.1
    have hBaseOne : x ≤ 1 := s.1.property.2
    have termDen (j : ℕ) (hj : j ≤ L) : (term x j).den ≤ 2 ^ B := by
      let e := 2 * j + 1
      have hDvd : (term x j).den ∣ x.den ^ e * e := by
        have hNonzero : ((e : ℕ) : ℚ) ≠ 0 := by dsimp [e]; positivity
        have hInverse : (((e : ℕ) : ℚ)⁻¹).den = e := by
          rw [Rat.den_inv_of_ne_zero hNonzero]
          simp
        simpa only [term, div_eq_mul_inv, Rat.den_pow, hInverse, e] using
          Rat.mul_den_dvd (x ^ e) ((e : ℚ)⁻¹)
      have hPos : 0 < x.den ^ e * e := by
        have hp : 0 < x.den := x.den_pos
        dsimp [e]
        positivity
      calc
        (term x j).den ≤ x.den ^ e * e := Nat.le_of_dvd hPos hDvd
        _ ≤ (2 ^ L) ^ e * 2 ^ e :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hBaseDen _) (show e < 2 ^ e from Nat.lt_two_pow_self).le
        _ = 2 ^ (L * e) * 2 ^ e := by rw [pow_mul (2 : ℕ) L e]
        _ = 2 ^ ((L + 1) * e) := by rw [Nat.add_mul L 1 e, Nat.one_mul, pow_add (2 : ℕ) (L * e) e]
        _ ≤ 2 ^ B := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (by dsimp [e]; omega))
    have halfSeriesDen (j : ℕ) (hj : j ≤ L) : (halfSeries x j).den ≤ 2 ^ (j * B) := by
      induction j with
      | zero => simp [halfSeries]
      | succ j ih =>
        have hRec : halfSeries x (j + 1) = halfSeries x j + term x j := Finset.sum_range_succ _ _
        rw [hRec]
        calc
          ((halfSeries x j) + term x j).den ≤ (halfSeries x j).den * (term x j).den := by
            exact Nat.le_of_dvd (Nat.mul_pos (halfSeries x j).den_pos (term x j).den_pos) (Rat.add_den_dvd _ _)
          _ ≤ 2 ^ (j * B) * 2 ^ B := Nat.mul_le_mul (ih (by omega)) (termDen j (by omega))
          _ = 2 ^ ((j + 1) * B) := by rw [Nat.add_mul, Nat.one_mul, pow_add]
    have hPowerDen : (x ^ (2 * k + 1)).den ≤ 2 ^ D := by
      rw [Rat.den_pow]
      calc
        x.den ^ (2 * k + 1) ≤ (2 ^ L) ^ (2 * k + 1) := Nat.pow_le_pow_left hBaseDen _
        _ = 2 ^ (L * (2 * k + 1)) := by rw [pow_mul]
        _ ≤ 2 ^ D := by
          apply Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
          have hB : L * (2 * k + 1) ≤ B :=
            Nat.mul_le_mul (by omega) (by omega)
          exact hB.trans (by
            simpa only [Nat.one_mul, D] using Nat.mul_le_mul_right B (show 1 ≤ L + 1 by omega))
    have hSumDen : (halfSeries x k).den ≤ 2 ^ D :=
      (halfSeriesDen k hK).trans
        (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
          (Nat.mul_le_mul_right B (by omega : k ≤ L + 1)))
    have termMagnitude (j : ℕ) : 0 ≤ term x j ∧ term x j ≤ 1 := by
      have hDen : (1 : ℚ) ≤ ((2 * j + 1 : ℕ) : ℚ) := by exact_mod_cast (show 1 ≤ 2 * j + 1 by omega)
      have hPos := zero_lt_one.trans_le hDen
      refine ⟨div_nonneg (pow_nonneg hBaseNat _) hPos.le, (div_le_iff₀ hPos).mpr ?_⟩
      rw [one_mul]
      exact (pow_le_one₀ hBaseNat hBaseOne).trans hDen
    have hSumPos : 0 ≤ halfSeries x k := Finset.sum_nonneg (fun j _ => (termMagnitude j).1)
    have hSumMagnitude : halfSeries x k ≤ (k : ℚ) := by
      calc
        halfSeries x k ≤ ∑ _j ∈ Finset.range k, (1 : ℚ) :=
          Finset.sum_le_sum (fun j _ => (termMagnitude j).2)
        _ = (k : ℚ) := by simp
    have hSumMagnitudePower : |halfSeries x k| ≤ (2 : ℚ) ^ L := by
      rw [abs_of_nonneg hSumPos]
      apply hSumMagnitude.trans
      exact_mod_cast hK.trans (show L < 2 ^ L from Nat.lt_two_pow_self).le
    have hPowerMagnitude : |x ^ (2 * k + 1)| ≤ (2 : ℚ) ^ L := by
      rw [abs_of_nonneg (pow_nonneg hBaseNat _)]
      exact (pow_le_one₀ hBaseNat hBaseOne).trans (one_le_pow₀ (by norm_num))
    have ratWordWidth (q : ℚ) (hDen : q.den ≤ 2 ^ D) (hMagnitude : |q| ≤ (2 : ℚ) ^ L) :
        (ratCode q).length ≤ 3 * D + 2 * L + 10 := by
      obtain ⟨hNum, hD, _⟩ :=
        OAI.Optimization.LinearProgramming.PriceGame.TrialExecution.dyadic_encoding_bounds
          q q.den L D q.den_pos hDen (dvd_refl _) hMagnitude
      have numBits := (Nat.size_le_size hNum).trans_eq Nat.size_pow
      have denBits := (Nat.size_le_size hD).trans_eq Nat.size_pow
      have numEq := Nat.size_eq_bits_len q.num.natAbs
      have denEq := Nat.size_eq_bits_len q.den
      simp only [ratCode, intCode, intData, prodCode, pairBits_length, boolCode,
        List.length_cons, List.length_nil]
      omega
    have hPowerWord := ratWordWidth (x ^ (2 * k + 1)) hPowerDen hPowerMagnitude
    have hSumWord := ratWordWidth (halfSeries x k) hSumDen hSumMagnitudePower
    rw [iterateIndex]
    change (stateCode (s.1, k)).length ≤ width.eval L
    simp only [width, denominatorWidth, X, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
    change (stateCode (s.1, k)).length ≤ 10 * D + 10 * L + 40
    simp only [stateCode, fields, indexCode, valuesCode, prodCode, pairBits_length,
      unaryCode, List.length_replicate]
    dsimp [x] at hLBase hPowerWord hSumWord
    omega
  let input (d : UnitLogInput) := (d.1.val, d.2)
  let value := (first ratCode unaryCode).precompose input
  let terms := (second ratCode unaryCode).precompose input
  let one := constant encodeUnitLogInput ratCode (1 : ℚ)
  let numerator := ratSub.comp (value.pair one)
  let denominator := ratAdd.comp (value.pair one)
  let baseP := ratDiv.comp (numerator.pair denominator)
  let base (d : UnitLogInput) : ℚ := (d.1.val - 1) / (d.1.val + 1)
  let source (d : UnitLogInput) : State := (⟨base d, by
    have low := d.1.property.1
    have pos : 0 < d.1.val + 1 := by linarith
    exact ⟨div_nonneg (sub_nonneg.mpr low) pos.le, (div_le_iff₀ pos).mpr (by linarith)⟩⟩, 0)
  let zeroIndex := constant encodeUnitLogInput unaryCode 0
  let zeroSum := constant encodeUnitLogInput ratCode (0 : ℚ)
  let startP : Procedure encodeUnitLogInput stateCode source :=
    (baseP.pair (zeroIndex.pair (baseP.pair zeroSum))).result (by
      intro d
      simp [stateCode, fields, source, base, halfSeries, input, indexCode, valuesCode,
        Function.comp_apply])
  let loop := (stepP.iterate width fits).comp (terms.pair startP)
  let series := readSum.comp loop
  exact (ratMul.comp ((constant encodeUnitLogInput ratCode (2 : ℚ)).pair series)).congrFun (by
    intro d
    change 2 * halfSeries (((advance^[d.2]) (source d)).1.val) (((advance^[d.2]) (source d)).2) =
      logSeries d.1.val d.2
    rw [iterateIndex]
    simp [source, base, logSeries, halfSeries, term, Nat.cast_add, Nat.cast_mul])

noncomputable def evaluateLogProcedure :
    Procedure encodeLogInput id (encodeRat ∘ logApproximation) := by
  let dataCode := prodCode ratCode unaryCode
  let exponent := (first intCode dataCode).comp logNormalizedP
  let data := (second intCode dataCode).comp logNormalizedP
  let terms := (second ratCode unaryCode).comp data
  let unitInput (d : LogInput) : UnitLogInput :=
    (⟨(logNormalize d).2.1, (logNormalize_correct d).1⟩, (logNormalize d).2.2)
  let twoInput (d : LogInput) : UnitLogInput :=
    (⟨2, by norm_num⟩, (logNormalize d).2.2)
  let unitP : Procedure encodeLogInput encodeUnitLogInput unitInput :=
    data.result (fun _ => rfl)
  let twoP : Procedure encodeLogInput encodeUnitLogInput twoInput :=
    ((constant encodeLogInput ratCode (2 : ℚ)).pair terms).result (fun _ => rfl)
  let scaled := ratMul.comp ((intToRat.comp exponent).pair (logSeriesP.comp twoP))
  let value : Procedure encodeLogInput ratCode logApproximation :=
    (ratAdd.comp (scaled.pair (logSeriesP.comp unitP))).congrFun (fun _ => rfl)
  exact OAI.Optimization.LinearProgramming.OracleSpec.Wire.writeRat.comp value

end EF1FPO
