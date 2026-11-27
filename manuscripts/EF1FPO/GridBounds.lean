import EF1FPO.Contraction

/-! Binary width of actual dyadic oracle replies. -/

set_option autoImplicit false

namespace EF1FPO

open OAI.Optimization.LinearProgramming.OracleSpec

theorem dyadic_numerator_bound (s : ℕ) (z : ℤ)
    (h₁ : -1 ≤ (z : ℝ) * precisionError s) (h₂ : (z : ℝ) * precisionError s ≤ 1) :
    z.natAbs ≤ 2 ^ s := by
  have hScale : 0 < precisionError s := by unfold precisionError; positivity
  have hAbs := abs_le.mpr ⟨h₁, h₂⟩
  rw [abs_mul, abs_of_nonneg hScale.le] at hAbs
  have hMagnitude := (le_div_iff₀ hScale).mpr hAbs
  rw [precisionError, div_inv_eq_mul, one_mul] at hMagnitude
  have hCast : (z.natAbs : ℝ) ≤ (2 : ℝ) ^ s := by
    rwa [Nat.cast_natAbs, Int.cast_abs]
  exact_mod_cast hCast

theorem encodeGrid_length_of_cube {n : ℕ} (s : ℕ) (a : GridNumerator n)
    (h : unitCube (dyadicPoint s a)) : (encodeGrid a).length ≤ n * (2 * s + 7) := by
  let limit := 2 * s + 7
  have hEntry (i : Fin n) : (encodeRat (a i : ℚ)).length ≤ limit := by
    have hBit : (a i).natAbs.size ≤ s + 1 :=
      (Nat.size_le_size (dyadic_numerator_bound s (a i) (h i).1 (h i).2)).trans_eq Nat.size_pow
    have hDenominator : (1 : ℕ).size = 1 := by decide
    simp only [encodeRat, List.length_cons, List.length_append, Rat.num_intCast, Rat.den_intCast,
      encodeNat_length, hDenominator, limit]
    omega
  have hList (xs : List ℚ) (fits : ∀ q ∈ xs, (encodeRat q).length ≤ limit) :
      (xs.flatMap encodeRat).length ≤ xs.length * limit := by
    induction xs with
    | nil => simp
    | cons q rest ih =>
      have head := fits q (List.mem_cons_self)
      have tail := ih (fun r hr => fits r (List.mem_cons_of_mem _ hr))
      rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul,
        Nat.add_comm (rest.length * limit) limit]
      exact Nat.add_le_add head tail
  have fits : ∀ q ∈ List.ofFn (fun i => (a i : ℚ)), (encodeRat q).length ≤ limit := by
    intro q hq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
    exact hEntry i
  simpa only [encodeGrid, List.length_ofFn, limit] using hList _ fits

end EF1FPO
