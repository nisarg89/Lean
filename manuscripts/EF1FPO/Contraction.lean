import EF1FPO.Computation
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.MetricSpace.Contracting

/-! The dyadic oracle interface and the monotone specialization of Section 8. -/

set_option autoImplicit false

namespace EF1FPO

open OAI.Optimization.LinearProgramming.OracleSpec

noncomputable section

abbrev Vector (n : ℕ) := Fin n → ℝ
abbrev GridNumerator (n : ℕ) := Fin n → ℤ

def unitCube {n : ℕ} (x : Vector n) : Prop := ∀ i, -1 ≤ x i ∧ x i ≤ 1

def precisionError (s : ℕ) : ℝ := ((2 : ℝ) ^ s)⁻¹

def dyadicPoint {n : ℕ} (s : ℕ) (a : GridNumerator n) : Vector n :=
  fun i => (a i : ℝ) * precisionError s

def encodeUnary (a : ℕ) : Word := List.replicate a true ++ [false]

def encodeGrid {n : ℕ} (a : GridNumerator n) : Word :=
  (List.ofFn (fun i => (a i : ℚ))).flatMap encodeRat

def dyadicQuery {n : ℕ} (p s : ℕ) (a : GridNumerator n) : Word :=
  encodeUnary p ++ encodeUnary s ++ encodeGrid a

def ApproximationOracle {n : ℕ} (f : Vector n → Vector n) (reply : WordOracle) : Prop :=
  ∀ history p s (a : GridNumerator n), unitCube (dyadicPoint p a) →
    ∃ q : GridNumerator n, unitCube (dyadicPoint s q) ∧
      dist (dyadicPoint s q) (f (dyadicPoint p a)) ≤ precisionError s ∧
      reply history (dyadicQuery p s a) = encodeGrid q

def MonotoneContraction {n : ℕ} (f : Vector n → Vector n) (b : ℕ) : Prop :=
  (∀ x, unitCube x → unitCube (f x)) ∧
  (∀ x y, unitCube x → unitCube y → x ≤ y → f x ≤ f y) ∧
  ∀ x y, unitCube x → unitCube y →
    dist (f x) (f y) ≤ (1 - precisionError b) * dist x y

def clipCube {n : ℕ} (x : Vector n) : Vector n := fun i => max (-1) (min 1 (x i))

def signFactor (up : Bool) : ℝ := if up then 1 else -1

def anchoredPoint {n : ℕ} (a : Fin n) (t : ℚ) (s : ℕ) (prices : Fin n → ℚ) : Vector n :=
  fun i => (t : ℝ) + precisionError s * ((prices i : ℝ) - prices a)

def anchoredCost {n : ℕ} (v : Vector n) (up : Bool) (s : ℕ) (i : Fin n) : ℕ :=
  ((2 : ℤ) ^ s + ⌊-signFactor up * v i / precisionError s⌋).toNat

theorem monotone_contraction_fixed_point {n b : ℕ} (f : Vector n → Vector n)
    (hf : MonotoneContraction f b) : ∃! v, unitCube v ∧ f v = v := by
  have hClip (x : Vector n) : unitCube (clipCube x) := fun i =>
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hClipId {x : Vector n} (hx : unitCube x) : clipCube x = x := by
    funext i
    exact (congrArg (max (-1)) (min_eq_right (hx i).2)).trans (max_eq_right (hx i).1)
  have hClipDist (x y : Vector n) : dist (clipCube x) (clipCube y) ≤ dist x y :=
    (dist_pi_le_iff dist_nonneg).mpr fun i => by
      rw [Real.dist_eq]
      have hmin := abs_min_sub_min_le_max (1 : ℝ) (x i) 1 (y i)
      have hmax := abs_max_sub_max_le_max (-1 : ℝ) (min 1 (x i)) (-1) (min 1 (y i))
      simp only [sub_self, abs_zero] at hmin hmax
      rw [max_eq_right (abs_nonneg (x i - y i))] at hmin
      rw [max_eq_right (abs_nonneg (min 1 (x i) - min 1 (y i)))] at hmax
      exact hmax.trans (hmin.trans (by simpa only [Real.dist_eq] using dist_le_pi_dist x y i))
  have hPow : (0 : ℝ) < 2 ^ b := by positivity
  have hFactor : 0 ≤ 1 - precisionError b :=
    sub_nonneg.mpr ((inv_le_one₀ hPow).mpr (one_le_pow₀ (by norm_num)))
  let K : NNReal := Real.toNNReal (1 - precisionError b)
  have hK : (K : ℝ) = 1 - precisionError b := Real.coe_toNNReal _ hFactor
  let g : Vector n → Vector n := f ∘ clipCube
  have hg : ContractingWith K g := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
    · have hPos : 0 < precisionError b := inv_pos.mpr hPow
      have hLt : (K : ℝ) < 1 := by rw [hK]; linarith
      exact_mod_cast hLt
    · dsimp [g]
      rw [hK]
      exact (hf.2.2 _ _ (hClip x) (hClip y)).trans
        (mul_le_mul_of_nonneg_left (hClipDist x y) hFactor)
  let v := ContractingWith.fixedPoint g hg
  have hvFix : g v = v := hg.fixedPoint_isFixedPt
  have hv : unitCube v := hvFix ▸ hf.1 _ (hClip v)
  refine ⟨v, ⟨hv, ?_⟩, ?_⟩
  · change f (clipCube v) = v at hvFix
    rwa [hClipId hv] at hvFix
  · intro y hy
    have hyFix : g y = y := by
      change f (clipCube y) = y
      rw [hClipId hy.1, hy.2]
    exact hg.fixedPoint_unique' hyFix hvFix

theorem anchored_cost_le {n : ℕ} (v : Vector n) (hv : unitCube v) (up : Bool) (s : ℕ)
    (i : Fin n) : anchoredCost v up s i ≤ 2 * 2 ^ s := by
  have hi : -signFactor up * v i ≤ 1 := by
    cases up
    · simpa [signFactor] using (hv i).2
    · simpa [signFactor] using neg_le_neg (hv i).1
  have hi' : -signFactor up * v i / precisionError s ≤ (((2 : ℤ) ^ s : ℤ) : ℝ) := by
    simpa [precisionError, div_inv_eq_mul] using
      mul_le_mul_of_nonneg_right hi (show (0 : ℝ) ≤ 2 ^ s by positivity)
  have hf := Int.floor_mono hi'
  rw [Int.floor_intCast] at hf
  rw [anchoredCost, Int.toNat_le]
  push_cast
  omega

theorem anchored_minimum_error {n : ℕ} (v : Vector n) (hv : unitCube v)
    (a i j : Fin n) (t : ℚ) (up : Bool) (s : ℕ) (prices : Fin n → ℚ)
    (hMin : adjustedCost up (anchoredCost v up s) prices i ≤
      adjustedCost up (anchoredCost v up s) prices j) :
    let x := anchoredPoint a t s prices
    signFactor up * (v j - x j) ≤ signFactor up * (v i - x i) + precisionError s := by
  let h := signFactor up
  let δ := precisionError s
  have hδ : 0 < δ := by dsimp [δ, precisionError]; positivity
  have hCost (l : Fin n) : (anchoredCost v up s l : ℝ) =
      (2 : ℝ) ^ s + (⌊-h * v l / δ⌋ : ℝ) := by
    have hLow : -1 ≤ -h * v l := by
      cases up
      · simpa [h, signFactor] using (hv l).1
      · simpa [h, signFactor] using neg_le_neg (hv l).2
    have hLow' : ((-((2 : ℤ) ^ s) : ℤ) : ℝ) ≤ -h * v l / δ := by
      simpa [δ, precisionError, div_inv_eq_mul] using
        mul_le_mul_of_nonneg_right hLow (show (0 : ℝ) ≤ 2 ^ s by positivity)
    have hFloor := Int.le_floor.mpr hLow'
    have hn : 0 ≤ (2 : ℤ) ^ s + ⌊-h * v l / δ⌋ := by omega
    change (((2 : ℤ) ^ s + ⌊-h * v l / δ⌋).toNat : ℝ) = _
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hn]
    push_cast
    rfl
  have hAdjusted (l : Fin n) : ((adjustedCost up (anchoredCost v up s) prices l : ℚ) : ℝ) =
      (2 : ℝ) ^ s + (⌊-h * v l / δ⌋ : ℝ) + h * (prices l : ℝ) := by
    rw [adjustedCost, Rat.cast_add, Rat.cast_natCast, hCost]
    cases up <;> simp [h, signFactor]
  have hMinReal : ((adjustedCost up (anchoredCost v up s) prices i : ℚ) : ℝ) ≤
      ((adjustedCost up (anchoredCost v up s) prices j : ℚ) : ℝ) := by exact_mod_cast hMin
  rw [hAdjusted, hAdjusted] at hMinReal
  have hError : -h * v i / δ + h * (prices i : ℝ) ≤
      -h * v j / δ + h * (prices j : ℝ) + 1 := by
    linarith only [hMinReal, Int.lt_floor_add_one (-h * v i / δ), Int.floor_le (-h * v j / δ)]
  have hScaled := mul_le_mul_of_nonneg_right hError hδ.le
  simp only [add_mul, div_mul_cancel₀ _ hδ.ne', one_mul] at hScaled
  change h * (v j - ((t : ℝ) + δ * ((prices j : ℝ) - prices a))) ≤
    h * (v i - ((t : ℝ) + δ * ((prices i : ℝ) - prices a))) + δ
  nlinarith only [hScaled]

theorem one_sided_clipped_contraction {n b : ℕ} (f : Vector n → Vector n) (v x : Vector n)
    (hf : MonotoneContraction f b) (hv : unitCube v) (hFixed : f v = v)
    (up : Bool) (r : ℝ) (hr : 0 ≤ r) (hMax : ∀ j, signFactor up * (v j - x j) ≤ r)
    (i : Fin n) :
    -(1 - precisionError b) * r ≤ signFactor up * (f (clipCube x) i - v i) := by
  have hClip : unitCube (clipCube x) := fun j =>
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hPow : (0 : ℝ) < 2 ^ b := by positivity
  have hFactor : 0 ≤ 1 - precisionError b := by
    exact sub_nonneg.mpr ((inv_le_one₀ hPow).mpr (one_le_pow₀ (by norm_num)))
  have compareAt (y : Vector n) (hy : unitCube y) (hDist : dist y v ≤ r) :
      |f y i - v i| ≤ (1 - precisionError b) * r := by
    rw [← Real.dist_eq, ← congrFun hFixed i]
    exact (dist_le_pi_dist (f y) (f v) i).trans
      ((hf.2.2 y v hy hv).trans (mul_le_mul_of_nonneg_left hDist hFactor))
  cases up
  · let y : Vector n := fun j => max (clipCube x j) (v j)
    have hxy : clipCube x ≤ y := fun j => le_max_left _ _
    have hy : unitCube y := fun j =>
      ⟨(hv j).1.trans (le_max_right _ _), max_le (hClip j).2 (hv j).2⟩
    have hDist : dist y v ≤ r := (dist_pi_le_iff hr).mpr fun j => by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (le_max_right _ _))]
      have hRaw : x j ≤ v j + r := by
        have h := hMax j
        simp only [signFactor, Bool.false_eq_true, if_false, neg_one_mul] at h
        linarith
      have hClipped : clipCube x j ≤ v j + r :=
        max_le (by linarith [(hv j).1]) ((min_le_right _ _).trans hRaw)
      have hUpper : y j ≤ v j + r := max_le hClipped (by linarith)
      linarith
    have hMono : f (clipCube x) i ≤ f y i := hf.2.1 _ _ hClip hy hxy i
    have hBound := (abs_le.mp (compareAt y hy hDist)).2
    simp only [signFactor, Bool.false_eq_true, if_false, neg_one_mul]
    linarith
  · let y : Vector n := fun j => min (clipCube x j) (v j)
    have hyx : y ≤ clipCube x := fun j => min_le_left _ _
    have hy : unitCube y := fun j =>
      ⟨le_min (hClip j).1 (hv j).1, (min_le_right _ _).trans (hv j).2⟩
    have hDist : dist y v ≤ r := (dist_pi_le_iff hr).mpr fun j => by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (min_le_right _ _))]
      have hRaw : v j - r ≤ x j := by
        have h := hMax j
        simp only [signFactor, if_true, one_mul] at h
        linarith
      have hClipped : v j - r ≤ clipCube x j :=
        (le_min (by linarith [(hv j).2]) hRaw).trans (le_max_right _ _)
      have hLower : v j - r ≤ y j := le_min hClipped (by linarith)
      linarith
    have hMono : f y i ≤ f (clipCube x) i := hf.2.1 _ _ hy hClip hyx i
    have hBound := (abs_le.mp (compareAt y hy hDist)).1
    simp only [signFactor, if_true, one_mul]
    linarith

theorem dyadic_clip_approximates {n : ℕ} (x : Vector n) (s : ℕ) :
    ∃ a : GridNumerator n, unitCube (dyadicPoint s a) ∧
      dist (dyadicPoint s a) (clipCube x) ≤ precisionError s := by
  let y := clipCube x
  let δ := precisionError s
  let a : GridNumerator n := fun i => ⌊y i / δ⌋
  have hPow : (0 : ℝ) < 2 ^ s := by positivity
  have hδ : 0 < δ := inv_pos.mpr hPow
  have hGrid (i : Fin n) : dyadicPoint s a i ≤ y i :=
    (le_div_iff₀ hδ).mp (Int.floor_le (y i / δ))
  have hLower (i : Fin n) : -1 ≤ dyadicPoint s a i := by
    have hy : -1 ≤ y i := le_max_left _ _
    have hScaled : ((-((2 : ℤ) ^ s) : ℤ) : ℝ) ≤ y i / δ := by
      simpa [δ, precisionError, div_inv_eq_mul] using mul_le_mul_of_nonneg_right hy hPow.le
    have ha : -((2 : ℤ) ^ s) ≤ a i := Int.le_floor.mpr hScaled
    have haReal := mul_le_mul_of_nonneg_right (show -(2 : ℝ) ^ s ≤ (a i : ℝ) by exact_mod_cast ha) hδ.le
    simpa [dyadicPoint, δ, precisionError, neg_mul, mul_inv_cancel₀ hPow.ne'] using haReal
  refine ⟨a, fun i => ⟨hLower i, (hGrid i).trans (max_le (by norm_num) (min_le_left _ _))⟩,
    (dist_pi_le_iff hδ.le).mpr (fun i => ?_)⟩
  change dist (dyadicPoint s a i) (y i) ≤ δ
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hGrid i))]
  have h := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (y i / δ))
  change y i < ((a i : ℝ) + 1) * δ at h
  change -( (a i : ℝ) * δ - y i) ≤ δ
  nlinarith only [h]

/-- At a forced query, approximate output has the prescribed sign against the raw input. -/
theorem anchored_residual {n b k : ℕ} (f : Vector n → Vector n) (v : Vector n)
    (hf : MonotoneContraction f b) (hv : unitCube v) (hFixed : f v = v)
    (a i : Fin n) (t : ℚ) (up : Bool) (prices : Fin n → ℚ)
    (hGap : precisionError (k + 2) ≤ signFactor up * (v a - (t : ℝ)))
    (hMin : ∀ j, adjustedCost up (anchoredCost v up (b + k + 6)) prices i ≤
      adjustedCost up (anchoredCost v up (b + k + 6)) prices j) :
    let s := b + k + 6
    let x := anchoredPoint a t s prices
    15 * precisionError s ≤ signFactor up * (f (clipCube x) i - x i) := by
  let s := b + k + 6
  let x := anchoredPoint a t s prices
  let errorAt (j : Fin n) := signFactor up * (v j - x j)
  have hNonempty : (Finset.univ : Finset (Fin n)).Nonempty := ⟨a, Finset.mem_univ a⟩
  let r := Finset.univ.sup' hNonempty errorAt
  have hErrorLe (j : Fin n) : errorAt j ≤ r :=
    Finset.le_sup' errorAt (Finset.mem_univ j)
  have hAnchor : precisionError (k + 2) ≤ errorAt a := by
    simpa only [errorAt, x, anchoredPoint, sub_self, mul_zero, add_zero] using hGap
  have hMax : precisionError (k + 2) ≤ r := hAnchor.trans (hErrorLe a)
  have hMaxNonneg : 0 ≤ r :=
    (show 0 ≤ precisionError (k + 2) by unfold precisionError; positivity).trans hMax
  have hMinimizes : r ≤ errorAt i + precisionError s := by
    refine Finset.sup'_le hNonempty _ (fun j _ => ?_)
    exact anchored_minimum_error v hv a i j t up s prices (hMin j)
  have hMovement := one_sided_clipped_contraction f v x hf hv hFixed up r hMaxNonneg hErrorLe i
  have hγ : 0 < precisionError b := by unfold precisionError; positivity
  have hProduct : precisionError b * precisionError (k + 2) = 16 * precisionError s := by
    have hPow : (2 : ℝ) ^ s = 2 ^ b * 2 ^ (k + 2) * 16 := by
      dsimp only [s]
      rw [show b + k + 6 = b + (k + 2) + 4 by omega, pow_add, pow_add]
      norm_num
    unfold precisionError
    rw [hPow]
    field_simp
  have hMargin : 16 * precisionError s ≤ precisionError b * r := by
    rw [← hProduct]
    exact mul_le_mul_of_nonneg_left hMax hγ.le
  change 15 * precisionError s ≤ signFactor up * (f (clipCube x) i - x i)
  rw [show signFactor up * (f (clipCube x) i - x i) =
    signFactor up * (f (clipCube x) i - v i) + errorAt i by dsimp [errorAt]; ring]
  nlinarith only [hMovement, hMinimizes, hMargin]

theorem anchored_dyadic_reply {n b k : ℕ} (f : Vector n → Vector n) (v : Vector n)
    (hf : MonotoneContraction f b) (hv : unitCube v) (hFixed : f v = v)
    (a i : Fin n) (t : ℚ) (up : Bool) (prices : Fin n → ℚ)
    (hGap : precisionError (k + 2) ≤ signFactor up * (v a - (t : ℝ)))
    (hMin : ∀ j, adjustedCost up (anchoredCost v up (b + k + 6)) prices i ≤
      adjustedCost up (anchoredCost v up (b + k + 6)) prices j)
    (query answer : GridNumerator n) :
    let s := b + k + 6
    let x := anchoredPoint a t s prices
    unitCube (dyadicPoint s query) →
    dist (dyadicPoint s query) (clipCube x) ≤ precisionError s →
    dist (dyadicPoint s answer) (f (dyadicPoint s query)) ≤ precisionError s →
    decide (t + ((2 : ℚ) ^ s)⁻¹ * (prices i - prices a) ≤
        (answer i : ℚ) * ((2 : ℚ) ^ s)⁻¹) = up := by
  let s := b + k + 6
  let x := anchoredPoint a t s prices
  let raw := t + ((2 : ℚ) ^ s)⁻¹ * (prices i - prices a)
  let returned := (answer i : ℚ) * ((2 : ℚ) ^ s)⁻¹
  change unitCube (dyadicPoint s query) →
    dist (dyadicPoint s query) (clipCube x) ≤ precisionError s →
    dist (dyadicPoint s answer) (f (dyadicPoint s query)) ≤ precisionError s →
    decide (raw ≤ returned) = up
  intro hQuery hRound hAnswer
  have hMove : 15 * precisionError s ≤ signFactor up * (f (clipCube x) i - x i) :=
    anchored_residual f v hf hv hFixed a i t up prices hGap hMin
  have hClip : unitCube (clipCube x) := fun j =>
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hPow : (0 : ℝ) < 2 ^ b := by positivity
  have hFactor : 0 ≤ 1 - precisionError b :=
    sub_nonneg.mpr ((inv_le_one₀ hPow).mpr (one_le_pow₀ (by norm_num)))
  have hγ : 0 ≤ precisionError b := (inv_pos.mpr hPow).le
  have hδ : 0 < precisionError s := by unfold precisionError; positivity
  have hRoundImage : dist (f (dyadicPoint s query)) (f (clipCube x)) ≤ precisionError s :=
    (hf.2.2 _ _ hQuery hClip).trans <| (mul_le_mul_of_nonneg_left hRound hFactor).trans <| by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (sub_le_self (1 : ℝ) hγ) hδ.le
  have hDist : dist (dyadicPoint s answer) (f (clipCube x)) ≤ 2 * precisionError s := by
    refine (dist_triangle _ (f (dyadicPoint s query)) _).trans ?_
    linarith only [hAnswer, hRoundImage]
  have hCoordinate := (dist_le_pi_dist (dyadicPoint s answer) (f (clipCube x)) i).trans hDist
  rw [Real.dist_eq] at hCoordinate
  have hErr := abs_le.mp hCoordinate
  have hRaw : (raw : ℝ) = x i := by simp [raw, x, anchoredPoint, precisionError]
  have hReturned : (returned : ℝ) = dyadicPoint s answer i := by
    simp [returned, dyadicPoint, precisionError]
  have hTransfer : raw ≤ returned ↔ x i ≤ dyadicPoint s answer i := by
    rw [← hRaw, ← hReturned, Rat.cast_le]
  cases up
  · simp only [signFactor, Bool.false_eq_true, ite_false, neg_one_mul] at hMove
    have hReject : ¬ raw ≤ returned := fun hLe => by
      have hReal := hTransfer.mp hLe
      linarith only [hReal, hMove, hErr.2, hδ]
    simp [hReject]
  · simp only [signFactor, ite_true, one_mul] at hMove
    have hAccept : raw ≤ returned := hTransfer.mpr (by linarith only [hMove, hErr.1, hδ])
    simp [hAccept]

theorem anchored_post_decodes {n s : ℕ} (a : Fin n) (v : Vector n) (hv : unitCube v)
    (up : Bool) (history : Transcript) (output : Word)
    (hPost : pricePost (2 * 2 ^ s) a history output)
    (hObserved : ∀ (i : Fin n) (prices : Fin n → ℚ) (answer : Word),
      (priceQuery i prices, answer) ∈ history →
      (∀ j, adjustedCost up (anchoredCost v up s) prices i ≤
        adjustedCost up (anchoredCost v up s) prices j) → answer = [up]) :
    output = [up] := by
  refine hPost.2.2 up Set.univ (anchoredCost v up s) (Set.mem_univ a)
    (fun j _ => anchored_cost_le v hv up s j) ?_
  intro i prices answer hEntry _ hMin
  exact hObserved i prices answer hEntry (fun j => hMin j (Set.mem_univ j))

theorem overlap_bisection_step (lo hi v η : ℝ) (reply : Bool) (hlo : lo ≤ v) (hhi : v ≤ hi)
    (hη : 0 ≤ η) (hBelow : v ≤ (lo + hi) / 2 - η → reply = false)
    (hAbove : (lo + hi) / 2 + η ≤ v → reply = true) :
    let mid := (lo + hi) / 2
    let lo' := if reply then max lo (mid - η) else lo
    let hi' := if reply then hi else min hi (mid + η)
    lo' ≤ v ∧ v ≤ hi' ∧ hi' - lo' ≤ (hi - lo) / 2 + η := by
  dsimp only
  cases reply
  · simp only [Bool.false_eq_true, ite_false]
    have hUpper : v ≤ (lo + hi) / 2 + η := by
      by_contra! h
      cases hAbove h.le
    have hMid : min hi ((lo + hi) / 2 + η) ≤ (lo + hi) / 2 + η := min_le_right _ _
    exact ⟨hlo, le_min hhi hUpper, by linarith⟩
  · simp only [ite_true]
    have hLower : (lo + hi) / 2 - η ≤ v := by
      by_contra! h
      cases hBelow h.le
    have hMid : (lo + hi) / 2 - η ≤ max lo ((lo + hi) / 2 - η) := le_max_right _ _
    exact ⟨max_le hlo hLower, hhi, by linarith⟩

theorem overlap_bisection_width (k : ℕ) (width : ℕ → ℝ) (hStart : width 0 ≤ 2)
    (hStep : ∀ j < k + 2,
      width (j + 1) ≤ width j / 2 + precisionError (k + 2)) :
    width (k + 2) ≤ precisionError k := by
  let η := precisionError (k + 2)
  have hη : 0 ≤ η := by dsimp [η, precisionError]; positivity
  have halve (j : ℕ) : precisionError (j + 1) = precisionError j / 2 := by
    unfold precisionError
    rw [pow_succ]
    have hPow : (2 : ℝ) ^ j ≠ 0 := by positivity
    field_simp
  have hWidth (j : ℕ) (hj : j ≤ k + 2) : width j ≤ 2 * precisionError j + 2 * η := by
    induction j with
    | zero =>
      simp only [precisionError, pow_zero, inv_one, mul_one]
      linarith
    | succ j ih =>
      have hBefore := ih (by omega)
      have hNext : width (j + 1) ≤ width j / 2 + η := hStep j (by omega)
      rw [halve]
      linarith only [hBefore, hNext]
  have hEnd : width (k + 2) ≤ 2 * η + 2 * η := hWidth _ le_rfl
  have hAccuracy : η = precisionError k / 4 := by
    dsimp only [η]
    rw [halve (k + 1), halve k]
    ring
  linarith

def contractionInput (n b k : ℕ) : Word := encodeUnary n ++ encodeUnary b ++ encodeUnary k

end

end EF1FPO
