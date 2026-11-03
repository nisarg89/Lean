import FairDivision.BF.HeterogeneousRealState

/-!
# BF Section 5: counting donors in every real rebalancing state

The manuscript's identity between full and deficient bundle counts depends
only on the real item total. Rebalancing preserves that total, so the same
identity supplies a fresh donor at every step.
-/

set_option autoImplicit false

namespace FairDivision.BF

/-- At any real rebalancing stage, the number of full bundles exceeds the
number of deficient bundles by `n-d`, where `d` is the dummy count. -/
theorem HeteroRealState.full_small_count
    {n m r d : ℕ} {Rstock : Finset (Fin m)}
    {v : Fin n → Finset (Fin m) → ℝ} {τ : Fin n → ℝ}
    {R : Fin n → Finset (Fin m)}
    (h : HeteroRealState r Rstock v τ R)
    (hr : 1 ≤ r)
    (hTotal : Rstock.card + d = n * (r + 1)) :
    (Finset.univ.filter (fun i : Fin n => (R i).card = r - 1)).card + n =
    (Finset.univ.filter (fun i : Fin n => (R i).card = r + 1)).card + d := by
  classical
  have hSize (i : Fin n) :
      (R i).card = r - 1 ∨ (R i).card = r ∨ (R i).card = r + 1 := by
    rcases (h.1 i).2 with hs | hm | hf
    · exact Or.inl hs.1
    · exact Or.inr (Or.inl hm.1)
    · exact Or.inr (Or.inr hf.1)
  have hPer (i : Fin n) :
      (R i).card + (if (R i).card = r - 1 then 1 else 0) =
        r + (if (R i).card = r + 1 then 1 else 0) := by
    rcases hSize i with hLow | hMid | hHigh
    · have hne : r - 1 ≠ r + 1 := by omega
      simp [hLow, hne] <;> omega
    · have hne : r ≠ r - 1 := by omega
      simp [hMid, hne]
    · have hne : r + 1 ≠ r - 1 := by omega
      simp [hHigh, hne]
  have hPairSet :
      ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint R := by
    intro i _ j _ hij
    exact h.2.1 i j hij
  have hCardUnion : (Finset.univ.biUnion R).card =
      ∑ i : Fin n, (R i).card := Finset.card_biUnion hPairSet
  have hRealUnion : Finset.univ.biUnion R = Rstock := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, _, hRi⟩ := Finset.mem_biUnion.mp hx
      exact (h.1 i).1 hRi
    · exact fun hx => h.2.2 hx
  have hSumReal : (∑ i : Fin n, (R i).card) + d = n * (r + 1) := by
    calc
      (∑ i : Fin n, (R i).card) + d = Rstock.card + d := by
        rw [← hCardUnion, hRealUnion]
      _ = n * (r + 1) := hTotal
  have hSumPer :
      (∑ i : Fin n, ((R i).card +
        (if (R i).card = r - 1 then 1 else 0))) =
      (∑ i : Fin n, (r +
        (if (R i).card = r + 1 then 1 else 0))) := by
    apply Finset.sum_congr rfl
    intro i _
    exact hPer i
  have hSmallSum :
      (∑ i : Fin n, if (R i).card = r - 1 then 1 else 0) =
      (Finset.univ.filter
        (fun i : Fin n => (R i).card = r - 1)).card := by simp
  have hFullSum :
      (∑ i : Fin n, if (R i).card = r + 1 then 1 else 0) =
      (Finset.univ.filter
        (fun i : Fin n => (R i).card = r + 1)).card := by simp
  have hConstSum : (∑ _ : Fin n, r) = n * r := by simp
  have hSum :
      (∑ i : Fin n, (R i).card) +
        (Finset.univ.filter
          (fun i : Fin n => (R i).card = r - 1)).card =
      n * r +
        (Finset.univ.filter
          (fun i : Fin n => (R i).card = r + 1)).card := by
    simpa only [Finset.sum_add_distrib, hSmallSum, hFullSum,
      hConstSum] using hSumPer
  have hMul : n * (r + 1) = n * r + n := by ring
  omega

/-- If a deficient real bundle remains and fewer than `n` dummies were
introduced, a full real donor remains as well. -/
theorem HeteroRealState.exists_full_of_small
    {n m r d : ℕ} {Rstock : Finset (Fin m)}
    {v : Fin n → Finset (Fin m) → ℝ} {τ : Fin n → ℝ}
    {R : Fin n → Finset (Fin m)}
    (h : HeteroRealState r Rstock v τ R)
    (hr : 1 ≤ r)
    (hTotal : Rstock.card + d = n * (r + 1))
    (hDlt : d < n)
    (hSmall : (Finset.univ.filter
      (fun i : Fin n => (R i).card = r - 1)).Nonempty) :
    ∃ j : Fin n, (R j).card = r + 1 := by
  classical
  have hCount := h.full_small_count hr hTotal
  have hPos : 0 < (Finset.univ.filter
      (fun j : Fin n => (R j).card = r + 1)).card := by
    have hSmallPos := Finset.card_pos.mpr hSmall
    omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hPos
  exact ⟨j, (Finset.mem_filter.mp hj).2⟩

end FairDivision.BF
