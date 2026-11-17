import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Lean.Elab.Tactic.Omega

/-!
# The first threshold crossing of a complete finite sequence

The sequence is supplied in full, independently of its values. We choose the
least index at or above the threshold and retain the preceding step. This is
the first-crossing selection used after constructing the complete exchange
sequence in Section 3 of the balanced envy-freeness manuscript.
-/

set_option autoImplicit false

namespace FairDivision.Finite

/-- A complete sequence with its first value below `t` and its last value at
least `t` has a neighboring pair across `t`. The proof chooses the first high
index; no monotonicity of the sequence is required. -/
theorem exists_first_threshold_crossing {length : ℕ}
    (value : Fin (length + 1) → ℝ) (t : ℝ)
    (hLow : value 0 < t) (hHigh : t ≤ value (Fin.last length)) :
    ∃ j : Fin length, value j.castSucc < t ∧ t ≤ value j.succ := by
  classical
  let P : ℕ → Prop := fun k => ∃ hk : k < length + 1, t ≤ value ⟨k, hk⟩
  have hExists : ∃ k, P k := ⟨length, Nat.lt_succ_self length, hHigh⟩
  let k := Nat.find hExists
  obtain ⟨hkBound, hkHigh⟩ := Nat.find_spec hExists
  change k < length + 1 at hkBound
  change t ≤ value ⟨k, hkBound⟩ at hkHigh
  have hkNe : k ≠ 0 := by
    intro hkZero
    have hIndex : (⟨k, hkBound⟩ : Fin (length + 1)) = 0 :=
      Fin.ext hkZero
    rw [hIndex] at hkHigh
    exact (not_le_of_gt hLow) hkHigh
  have hjBound : k - 1 < length := by omega
  have hPrevNot : ¬ P (k - 1) :=
    Nat.find_min hExists (by change k - 1 < k; omega)
  have hPrevLow : value ⟨k - 1, by omega⟩ < t := by
    apply lt_of_not_ge
    intro hPrevHigh
    exact hPrevNot ⟨by omega, hPrevHigh⟩
  let j : Fin length := ⟨k - 1, hjBound⟩
  have hSucc : j.succ = (⟨k, hkBound⟩ : Fin (length + 1)) := by
    apply Fin.ext
    change k - 1 + 1 = k
    omega
  refine ⟨j, hPrevLow, ?_⟩
  rw [hSucc]
  exact hkHigh

end FairDivision.Finite
