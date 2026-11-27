import EF1FPO.Contraction
import Mathlib.Data.Rat.Floor

/-! The two closed arithmetic calls around a dyadic evaluation. -/

set_option autoImplicit false

namespace EF1FPO

open OAI.Optimization.LinearProgramming.OracleSpec

structure AnchoredPriceRequest where
  n : ℕ
  precision : ℕ
  anchor : Fin n
  designated : Fin n
  threshold : ℚ
  prices : Fin n → ℚ

namespace AnchoredPriceRequest

def raw (q : AnchoredPriceRequest) (i : Fin q.n) : ℚ :=
  q.threshold + ((2 : ℚ) ^ q.precision)⁻¹ * (q.prices i - q.prices q.anchor)

def grid (q : AnchoredPriceRequest) (i : Fin q.n) : ℤ :=
  ⌊max (-1) (min 1 (q.raw i)) * (2 : ℚ) ^ q.precision⌋

def encode (q : AnchoredPriceRequest) : Word :=
  encodeUnary q.n ++ encodeUnary q.precision ++ encodeNat q.anchor.val ++
    encodeRat q.threshold ++ priceQuery q.designated q.prices

def encodeResult (q : AnchoredPriceRequest) : Word :=
  frame (dyadicQuery q.precision q.precision q.grid) ++ encodeRat (q.raw q.designated)

theorem raw_cast (q : AnchoredPriceRequest) (i : Fin q.n) :
    (q.raw i : ℝ) = anchoredPoint q.anchor q.threshold q.precision q.prices i := by
  simp [raw, anchoredPoint, precisionError]

theorem grid_correct (q : AnchoredPriceRequest) :
    unitCube (dyadicPoint q.precision q.grid) ∧
    dist (dyadicPoint q.precision q.grid)
      (clipCube (anchoredPoint q.anchor q.threshold q.precision q.prices)) ≤
        precisionError q.precision := by
  let clipped := clipCube (anchoredPoint q.anchor q.threshold q.precision q.prices)
  let δ := precisionError q.precision
  have hPow : (0 : ℝ) < 2 ^ q.precision := by positivity
  have hδ : 0 < δ := inv_pos.mpr hPow
  have hFloor (i : Fin q.n) : q.grid i = ⌊clipped i / δ⌋ := by
    unfold grid
    rw [← Rat.floor_cast (α := ℝ), Rat.cast_mul, Rat.cast_max, Rat.cast_min, Rat.cast_pow, q.raw_cast i]
    simp [clipped, clipCube, δ, precisionError, div_inv_eq_mul]
  have hGridLe (i : Fin q.n) : dyadicPoint q.precision q.grid i ≤ clipped i := by
    unfold dyadicPoint
    rw [hFloor i]
    exact (le_div_iff₀ hδ).mp (Int.floor_le (clipped i / δ))
  have hGridLo (i : Fin q.n) : -1 ≤ dyadicPoint q.precision q.grid i := by
    have hClipped : -1 ≤ clipped i := le_max_left _ _
    have hScaled : ((-((2 : ℤ) ^ q.precision) : ℤ) : ℝ) ≤ clipped i / δ := by
      simpa [δ, precisionError, div_inv_eq_mul] using mul_le_mul_of_nonneg_right hClipped hPow.le
    have hInt : -((2 : ℤ) ^ q.precision) ≤ q.grid i := by
      rw [hFloor i]
      exact Int.le_floor.mpr hScaled
    have hReal : -(2 : ℝ) ^ q.precision ≤ (q.grid i : ℝ) := by exact_mod_cast hInt
    have hMul := mul_le_mul_of_nonneg_right hReal hδ.le
    simpa [dyadicPoint, δ, precisionError, neg_mul, mul_inv_cancel₀ hPow.ne'] using hMul
  refine ⟨fun i => ⟨hGridLo i, (hGridLe i).trans (max_le (by norm_num) (min_le_left _ _))⟩,
    (dist_pi_le_iff hδ.le).mpr (fun i => ?_)⟩
  change dist (dyadicPoint q.precision q.grid i) (clipped i) ≤ δ
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hGridLe i))]
  have h := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (clipped i / δ))
  rw [← hFloor i] at h
  change -((q.grid i : ℝ) * δ - clipped i) ≤ δ
  nlinarith only [h]

end AnchoredPriceRequest

structure AnchoredPriceAnswer where
  n : ℕ
  precision : ℕ
  designated : Fin n
  rawCoordinate : ℚ
  numerator : GridNumerator n

namespace AnchoredPriceAnswer

def encode (a : AnchoredPriceAnswer) : Word :=
  encodeUnary a.n ++ encodeUnary a.precision ++ encodeNat a.designated.val ++
    encodeRat a.rawCoordinate ++ encodeGrid a.numerator

def compare (a : AnchoredPriceAnswer) : Bool :=
  decide (a.rawCoordinate ≤ (a.numerator a.designated : ℚ) * ((2 : ℚ) ^ a.precision)⁻¹)

end AnchoredPriceAnswer

end EF1FPO
