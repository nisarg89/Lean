import FairDivision.BF.HeterogeneousFiniteEndpoint
import FairDivision.BF.HeterogeneousBalanceCount

/-!
# BF Section 5: exactly divisible item count

When no dummy is needed, completing unused real items already makes every
bundle full. The manuscript's final donor-shortening phase is unnecessary,
so no shortening certificate is required from a selected bundle in this
branch. The placeholder used to define virtual valuations need not occur in
the actual item stock.
-/

set_option autoImplicit false

namespace FairDivision.BF

open FairDivision.Finite

/-- Without dummies, the real-item completion state alone yields a balanced
EF[1,1] allocation. -/
theorem hetero_no_dummy_partial_exists_balanced_ef11
    {n N r : ℕ}
    (v : Fin n → Finset (Fin (N - (∅ : Finset (Fin N)).card)) → ℝ)
    (τ : Fin n → ℝ)
    (B : Fin n → Finset (Fin N))
    (hr : 1 ≤ r)
    (hN : N = n * (r + 1))
    (hn : 0 < n)
    (hB : HeteroPartialState r
      (Finset.univ : Finset (Fin N)) (∅ : Finset (Fin N))
      (fun j S => v j (pullbackRealBundle ∅ S)) τ B) :
    ∃ A : FairDivision.Allocation n (N - (∅ : Finset (Fin N)).card),
      FairDivision.IsBalanced A ∧ FairDivision.IsEF11 v A := by
  classical
  let w : Fin n → Finset (Fin N) → ℝ :=
    fun j S => v j (pullbackRealBundle ∅ S)
  have hTotal : (Finset.univ : Finset (Fin N)).card =
      n * (r + 1) := by simpa using hN
  obtain ⟨C, hC, hCovered⟩ :=
    complete_hetero_real_items
      (Finset.univ : Finset (Fin N)) (∅ : Finset (Fin N))
      w τ hTotal B hB
  have hCount := real_full_small_count
    (Finset.univ : Finset (Fin N)) (∅ : Finset (Fin N))
    w τ C hr (Finset.empty_subset _) hTotal hC hCovered
  have hSmallEmpty :
      (Finset.univ.filter
        (fun i : Fin n => (C i \ (∅ : Finset (Fin N))).card = r - 1)) = ∅ := by
    ext i
    constructor
    · intro hi
      have hiSmall := (Finset.mem_filter.mp hi).2
      simp only [Finset.sdiff_empty] at hiSmall
      rcases hC.size i with hiSize | hiSize <;> omega
    · simp
  have hFullCard :
      (Finset.univ.filter
        (fun i : Fin n => (C i \ (∅ : Finset (Fin N))).card = r + 1)).card = n := by
    rw [hSmallEmpty] at hCount
    simpa only [Finset.card_empty, zero_add, Finset.card_empty, add_zero] using hCount.symm
  have hFullSet :
      (Finset.univ.filter
        (fun i : Fin n => (C i \ (∅ : Finset (Fin N))).card = r + 1)) =
      Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    simpa using hFullCard.ge
  have hAllFull (i : Fin n) : (C i).card = r + 1 := by
    have hiMem : i ∈ (Finset.univ.filter
        (fun j : Fin n => (C j \ (∅ : Finset (Fin N))).card = r + 1)) := by
      rw [hFullSet]
      exact Finset.mem_univ i
    simpa using (Finset.mem_filter.mp hiMem).2
  have hSubset (i : Fin n) :
      C i ⊆ (Finset.univ : Finset (Fin N)) \ (∅ : Finset (Fin N)) := by
    simpa using (hC.1 i).1
  have hBrackets (i : Fin n) : HeteroBrackets w τ i (C i) :=
    hC.full_brackets i (hAllFull i)
  obtain ⟨A, _, hCard, _, hEF⟩ :=
    exists_allocation_of_hetero_real_family
      (∅ : Finset (Fin N)) v τ C hSubset hC.2.1 hCovered
      (fun i => Or.inr (hAllFull i)) hBrackets
  refine ⟨A, ?_, hEF⟩
  intro i
  left
  rw [hCard i]
  have hFloor : (N - (∅ : Finset (Fin N)).card) / n = r + 1 := by
    simp [hN, Nat.mul_div_cancel_left (r + 1) hn]
  rw [hFloor]
  exact hAllFull i

/-- Selected virtual-valuation witnesses imply the BF heterogeneous result
in the exactly divisible case without requiring a dummy item. -/
theorem hetero_selectedWitness_no_dummy_exists_balanced_ef11
    {n N q : ℕ}
    (dummy : Fin N)
    (v : Fin n → Finset (Fin (N - (∅ : Finset (Fin N)).card)) → ℝ)
    (E : Fin n → Finset (Fin N))
    (u : Fin n → Fin n → ℝ)
    (w : ∀ s : Fin n,
      OwnerWitness q dummy
        (fun j S => v j (pullbackRealBundle ∅ S))
        (E s) (u s) s)
    (hq : 2 ≤ q)
    (hN : N = n * q)
    (hn : 0 < n)
    (hEF : ∀ i j : Fin n, u j i ≤ u i i)
    (hPools : ∀ i j : Fin n, i ≠ j → Disjoint (E i) (E j)) :
    ∃ A : FairDivision.Allocation n (N - (∅ : Finset (Fin N)).card),
      FairDivision.IsBalanced A ∧ FairDivision.IsEF11 v A := by
  have hState : HeteroPartialState (q - 1)
      (Finset.univ : Finset (Fin N)) (∅ : Finset (Fin N))
      (fun j S => v j (pullbackRealBundle ∅ S))
      (fun j => u j j) (fun i => (w i).B) :=
    heteroState_of_selectedWitness w hEF hPools
      (Finset.univ : Finset (Fin N)) (∅ : Finset (Fin N))
      (fun i => Finset.subset_univ (E i))
      (by intro i; simp) (by omega)
  have hN' : N = n * (q - 1 + 1) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ q)] using hN
  exact hetero_no_dummy_partial_exists_balanced_ef11 v
    (fun j => u j j) (fun i => (w i).B)
    (by omega) hN' hn hState

end FairDivision.BF
