import FairDivision.Finite.ProjectedBalance

/-!
# Balanced allocations from supported slot permutations

The cardinality bounds become exact balance when the item count is divisible
by the number of agents, because complete allocation fixes the total size.
-/

set_option autoImplicit false

namespace FairDivision

/-- Bundle cardinalities sum to the number of items in a complete allocation. -/
theorem sum_bundle_card {n m : ℕ} (A : Allocation n m) :
    (∑ i : Fin n, (bundle A i).card) = m := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (f := A) (s := Finset.univ) (t := Finset.univ)
    (by simp : Set.MapsTo A (Finset.univ : Finset (Fin m))
      (Finset.univ : Finset (Fin n)))
  simpa [bundle] using h.symm

/-- If all bundles have at least their floor quota, exact divisibility
forces every bundle to have exactly that quota. -/
theorem exact_bundle_card_of_divisible {n m : ℕ} (hn : 0 < n)
    (A : Allocation n m) (hdiv : n ∣ m)
    (hlo : ∀ i : Fin n, m / n ≤ (bundle A i).card)
    (i : Fin n) : (bundle A i).card = m / n := by
  have hm : m = n * (m / n) := by
    exact (Nat.mul_div_cancel' hdiv).symm
  have htotal := sum_bundle_card A
  have hhi : (bundle A i).card ≤ m / n := by
    by_contra h
    have hstrict : m / n < (bundle A i).card := Nat.lt_of_not_ge h
    have hsumlt : (∑ j : Fin n, m / n) <
        ∑ j : Fin n, (bundle A j).card := by
      apply Finset.sum_lt_sum
      · intro j _
        exact hlo j
      · exact ⟨i, Finset.mem_univ _, hstrict⟩
    have hconst : (∑ j : Fin n, m / n) = n * (m / n) := by simp
    rw [hconst, ← hm, htotal] at hsumlt
    exact (lt_irrefl m) hsumlt
  exact le_antisymm hhi (hlo i)

/-- A supported slot permutation projects to a balanced integral allocation. -/
theorem slotPermAllocation_balanced {n m : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (AssignmentSlot n m))
    (hσ : PermRespectsDummy hn σ) :
    IsBalanced (slotPermAllocation hn σ) := by
  intro i
  by_cases hdiv : n ∣ m
  · left
    exact exact_bundle_card_of_divisible hn _ hdiv
      (slotPermAllocation_lower hn σ hσ) i
  · have hlo := slotPermAllocation_lower hn σ hσ i
    have hhi := slotPermAllocation_upper hn σ i
    have hmod : m % n ≠ 0 := by
      intro hzero
      exact hdiv (Nat.dvd_of_mod_eq_zero hzero)
    have hupper : upperSize n m = m / n + 1 := by
      simp [upperSize, hmod]
    rw [hupper]
    omega

end FairDivision
