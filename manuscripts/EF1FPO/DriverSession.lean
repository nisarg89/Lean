import EF1FPO.BisectionDriver
import EF1FPO.RequestProcedure
import EF1FPO.AnswerProcedure

/-! The bisection invariant and the charged, adaptive machine session. -/

set_option autoImplicit false

namespace EF1FPO.BisectionDriver

open OAI.Optimization.LinearProgramming.OracleSpec

noncomputable section

def Progress.lo (p : Progress) : ℝ := bisectionCoordinate p.input.k p.bounds.1
def Progress.hi (p : Progress) : ℝ := bisectionCoordinate p.input.k p.bounds.2

def Progress.remaining (p : Progress) : ℕ :=
  (p.input.n - p.index.val) * (p.input.k + 2) - p.round

def GoodCoordinate (k : ℕ) (z : ℤ) (v : ℝ) : Prop :=
  -1 ≤ bisectionCoordinate k z ∧ bisectionCoordinate k z ≤ 1 ∧
    |bisectionCoordinate k z - v| ≤ precisionError k

def Progress.Valid (p : Progress) (v : ℕ → ℝ) : Prop :=
  p.round < p.input.k + 2 ∧
    bisectionAligned p.input.k p.round p.bounds ∧
    -1 ≤ p.lo ∧ p.lo ≤ v p.index.val ∧ v p.index.val ≤ p.hi ∧ p.hi ≤ 1 ∧
    p.hi - p.lo ≤ 2 * precisionError p.round + 2 * precisionError (p.input.k + 2) ∧
    p.completed.length = p.index.val ∧
    ∀ j < p.index.val, ∃ z, p.completed.reverse[j]? = some z ∧ GoodCoordinate p.input.k z (v j)

def Progress.AdvancePost (p : Progress) (v : ℕ → ℝ) : List ℤ ⊕ Progress → Prop
  | .inl output => output.length = p.input.n ∧
      ∀ j < p.input.n, ∃ z, output.reverse[j]? = some z ∧ GoodCoordinate p.input.k z (v j)
  | .inr q => q.input = p.input ∧ q.remaining + 1 = p.remaining ∧ q.Valid v

theorem initial_valid (input : Input) (v : ℕ → ℝ) (h : ∀ j < input.n, -1 ≤ v j ∧ v j ≤ 1) :
    (initial input).Valid v := by
  have hLo : (initial input).lo = -1 := by
    simp [Progress.lo, initial, bisectionInitial, bisectionCoordinate, precisionError, neg_mul]
  have hHi : (initial input).hi = 1 := by
    simp [Progress.hi, initial, bisectionInitial, bisectionCoordinate, precisionError]
  have hOrigin := h 0 input.nonempty
  refine ⟨by simp [initial], bisection_initial_aligned _, hLo.ge, ?_, ?_, hHi.le, ?_, rfl, ?_⟩
  · change (initial input).lo ≤ v 0
    rw [hLo]
    exact hOrigin.1
  · change v 0 ≤ (initial input).hi
    rw [hHi]
    exact hOrigin.2
  · change (initial input).hi - (initial input).lo ≤
      2 * precisionError 0 + 2 * precisionError (input.k + 2)
    have hTol : 0 ≤ precisionError (input.k + 2) := by unfold precisionError; positivity
    rw [hLo, hHi]
    simp only [precisionError, pow_zero, inv_one, mul_one]
    unfold precisionError at hTol
    linarith
  · intro j hj
    change j < 0 at hj
    omega

theorem advance_valid (p : Progress) (v : ℕ → ℝ)
    (hCube : ∀ j < p.input.n, -1 ≤ v j ∧ v j ≤ 1) (h : p.Valid v) (bit : Bool)
    (hDown : v p.index.val ≤ (p.threshold : ℝ) - precisionError (p.input.k + 2) → bit = false)
    (hUp : (p.threshold : ℝ) + precisionError (p.input.k + 2) ≤ v p.index.val → bit = true) :
    p.AdvancePost v (p.advance bit) := by
  rcases h with ⟨roundFits, aligned, loCube, loContains, hiContains, hiCube, width, count, prior⟩
  let k := p.input.k
  let η := precisionError (k + 2)
  let coordinate := bisectionCoordinate k
  let updated := bisectionNext k p.bounds bit
  have hη : 0 ≤ η := by dsimp [η, precisionError]; positivity
  have hScale : 0 ≤ precisionError (bisectionGrid k) := by unfold precisionError; positivity
  have hMidCast : (p.threshold : ℝ) = coordinate (bisectionMidpoint p.bounds) := by
    simp [Progress.threshold, bisectionThreshold, coordinate, k, bisectionCoordinate,
      precisionError, div_eq_mul_inv]
  have hMid : (p.threshold : ℝ) = (p.lo + p.hi) / 2 :=
    hMidCast.trans (bisection_midpoint_coordinate p.bounds roundFits aligned)
  have hMargin : coordinate (bisectionMargin k) = η := bisection_margin_coordinate k
  have hMax (a b : ℤ) : coordinate (max a b) = max (coordinate a) (coordinate b) := by
    change (↑(max a b) : ℝ) * precisionError (bisectionGrid k) = _
    rw [Int.cast_max, max_mul_of_nonneg _ _ hScale] <;> rfl
  have hMin (a b : ℤ) : coordinate (min a b) = min (coordinate a) (coordinate b) := by
    change (↑(min a b) : ℝ) * precisionError (bisectionGrid k) = _
    rw [Int.cast_min, min_mul_of_nonneg _ _ hScale] <;> rfl
  have hSub (a b : ℤ) : coordinate (a - b) = coordinate a - coordinate b := by
    simp [coordinate, bisectionCoordinate, sub_mul]
  have hAdd (a b : ℤ) : coordinate (a + b) = coordinate a + coordinate b := by
    simp [coordinate, bisectionCoordinate, add_mul]
  have newLo : coordinate updated.1 =
      if bit then max p.lo ((p.threshold : ℝ) - η) else p.lo := by
    cases bit with
    | false => rfl
    | true =>
      change coordinate (max p.bounds.1 (bisectionMidpoint p.bounds - bisectionMargin k)) = _
      rw [hMax, hSub, ← hMidCast, hMargin] <;> rfl
  have newHi : coordinate updated.2 =
      if bit then p.hi else min p.hi ((p.threshold : ℝ) + η) := by
    cases bit with
    | false =>
      change coordinate (min p.bounds.2 (bisectionMidpoint p.bounds + bisectionMargin k)) = _
      rw [hMin, hAdd, ← hMidCast, hMargin] <;> rfl
    | true => rfl
  have step := overlap_bisection_step p.lo p.hi (v p.index.val) η bit loContains hiContains
    hη (by simpa only [hMid] using hDown) (by simpa only [hMid] using hUp)
  have hContains : coordinate updated.1 ≤ v p.index.val ∧ v p.index.val ≤ coordinate updated.2 ∧
      coordinate updated.2 - coordinate updated.1 ≤ (p.hi - p.lo) / 2 + η := by
    simpa only [newLo, newHi, hMid] using step
  have hLoGrow : p.lo ≤ coordinate updated.1 := by
    rw [newLo]
    cases bit
    · exact le_rfl
    · exact le_max_left _ _
  have hHiShrink : coordinate updated.2 ≤ p.hi := by
    rw [newHi]
    cases bit
    · exact min_le_left _ _
    · exact le_rfl
  have half (j : ℕ) : precisionError (j + 1) = precisionError j / 2 := by
    unfold precisionError
    rw [pow_succ]
    have hPow : (2 : ℝ) ^ j ≠ 0 := by positivity
    field_simp
  have newWidth : coordinate updated.2 - coordinate updated.1 ≤
      2 * precisionError (p.round + 1) + 2 * η := by
    rw [half]
    change p.hi - p.lo ≤ 2 * precisionError p.round + 2 * η at width
    linarith only [width, hContains.2.2]
  have hIndex := p.index.isLt
  have hAvailable : p.round + 1 ≤ (p.input.n - p.index.val) * (k + 2) := by
    have first : 1 ≤ p.input.n - p.index.val := by omega
    refine (Nat.succ_le_iff.mpr roundFits).trans ?_
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (k + 2) first
  by_cases hRound : p.round + 1 < k + 2
  · let progress := { p with round := p.round + 1, bounds := updated }
    have hRound' : p.round + 1 < p.input.k + 2 := hRound
    have hBranch : p.advance bit = .inr progress := by
      simp [Progress.advance, hRound', progress, updated, k]
    rw [hBranch]
    change progress.input = p.input ∧ progress.remaining + 1 = p.remaining ∧ progress.Valid v
    refine ⟨rfl, ?_, hRound, bisection_next_aligned p.bounds bit roundFits aligned,
      loCube.trans hLoGrow, hContains.1, hContains.2.1, hHiShrink.trans hiCube, newWidth, count, prior⟩
    change (p.input.n - p.index.val) * (k + 2) - (p.round + 1) + 1 =
      (p.input.n - p.index.val) * (k + 2) - p.round
    omega
  · have hRoundDone : p.round + 1 = k + 2 := by omega
    have hAccuracy : 4 * η = precisionError k := by
      rw [show η = precisionError (k + 1 + 1) by rfl, half, half]
      ring
    have hGood : GoodCoordinate k updated.1 (v p.index.val) := by
      refine ⟨loCube.trans hLoGrow, hContains.1.trans (hContains.2.1.trans (hHiShrink.trans hiCube)), ?_⟩
      change |coordinate updated.1 - v p.index.val| ≤ precisionError k
      rw [abs_of_nonpos (sub_nonpos.mpr hContains.1)]
      rw [hRoundDone] at newWidth
      change coordinate updated.2 - coordinate updated.1 ≤ 2 * η + 2 * η at newWidth
      linarith only [newWidth, hContains.2.1, hAccuracy]
    let done := updated.1 :: p.completed
    have doneLength : done.length = p.index.val + 1 := by simp [done, count]
    have donePrefix (j : ℕ) (hj : j < p.index.val + 1) :
        ∃ z, done.reverse[j]? = some z ∧ GoodCoordinate k z (v j) := by
      have hLength : p.completed.reverse.length = p.index.val := by simpa using count
      by_cases hjOld : j < p.index.val
      · obtain ⟨z, hz, good⟩ := prior j hjOld
        have hjLength : j < p.completed.reverse.length := hLength.symm ▸ hjOld
        exact ⟨z, by simpa only [done, List.reverse_cons, List.getElem?_append_left hjLength] using hz, good⟩
      · have hNew : j = p.index.val := by omega
        subst j
        have hjLength : p.completed.reverse.length ≤ p.index.val := hLength.le
        refine ⟨updated.1, ?_, hGood⟩
        simp only [done, List.reverse_cons, List.getElem?_append_right hjLength, hLength, Nat.sub_self] <;> rfl
    have hRound' : ¬p.round + 1 < p.input.k + 2 := hRound
    by_cases nextFits : p.index.val + 1 < p.input.n
    · let progress : Progress :=
        ⟨p.input, ⟨p.index.val + 1, nextFits⟩, 0, bisectionInitial k, done⟩
      have hBranch : p.advance bit = .inr progress := by
        simp [Progress.advance, hRound', nextFits, progress, k, done, updated]
      rw [hBranch]
      let nextValue := v (p.index.val + 1)
      have reset := initial_valid p.input (fun _ => nextValue) (fun _ _ => hCube _ nextFits)
      rcases reset with ⟨resetRound, resetAligned, resetLo, resetContainsLo, resetContainsHi,
        resetHi, resetWidth, _, _⟩
      refine ⟨rfl, ?_, resetRound, resetAligned, resetLo, resetContainsLo, resetContainsHi,
        resetHi, resetWidth, doneLength, donePrefix⟩
      have hCount : p.input.n - (p.index.val + 1) + 1 = p.input.n - p.index.val := by omega
      have hTotal :
          (p.input.n - (p.index.val + 1)) * (k + 2) + (k + 2) =
            (p.input.n - p.index.val) * (k + 2) := by
        rw [← hCount, Nat.add_mul, Nat.one_mul]
      change (p.input.n - (p.index.val + 1)) * (k + 2) - 0 + 1 =
        (p.input.n - p.index.val) * (k + 2) - p.round
      omega
    · have hIndexDone : p.index.val + 1 = p.input.n := by omega
      have hBranch : p.advance bit = .inl done := by simp [Progress.advance, hRound', nextFits, done, updated, k]
      rw [hBranch]
      exact ⟨doneLength.trans hIndexDone, fun j hj => donePrefix j (hIndexDone.symm ▸ hj)⟩

end

end EF1FPO.BisectionDriver
