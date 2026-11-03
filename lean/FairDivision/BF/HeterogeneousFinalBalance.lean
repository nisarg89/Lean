import FairDivision.BF.HeterogeneousReindex

/-!
# BF Section 5: final balance arithmetic

After the donor transfers, each real bundle has size `q-1` or `q`.
For a positive number of dummies these are exactly the floor and ceiling
sizes. With no dummies, the item count forces every bundle to have size `q`.
-/

set_option autoImplicit false

namespace FairDivision.BF

/-- The final real bundle sizes are the floor or ceiling of the real item
count, including the zero-dummy case where floor and ceiling coincide. -/
theorem HeteroRealState.final_balanced_size
    {n N r : ℕ} (D : Finset (Fin N))
    {v : Fin n → Finset (Fin N) → ℝ} {τ : Fin n → ℝ}
    {R : Fin n → Finset (Fin N)}
    (h : HeteroRealState r
      ((Finset.univ : Finset (Fin N)) \ D) v τ R)
    (hr : 1 ≤ r)
    (hN : N = n * (r + 1))
    (hDlt : D.card < n)
    (hSizes : ∀ i : Fin n, (R i).card = r ∨ (R i).card = r + 1)
    (i : Fin n) :
    (R i).card = (N - D.card) / n ∨
      (R i).card = FairDivision.upperSize n (N - D.card) := by
  have hn : 0 < n := by omega
  by_cases hD0 : D.card = 0
  · have hTotal :
        (((Finset.univ : Finset (Fin N)) \ D).card) + D.card =
          n * (r + 1) := by
      rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)]
      simpa using hN
    have hCount := h.full_small_count hr hTotal
    have hSmallEmpty :
        (Finset.univ.filter
          (fun j : Fin n => (R j).card = r - 1)) = ∅ := by
      ext j
      constructor
      · intro hj
        have hjSmall := (Finset.mem_filter.mp hj).2
        rcases hSizes j with hjSize | hjSize <;> omega
      · simp
    have hFullCard :
        (Finset.univ.filter
          (fun j : Fin n => (R j).card = r + 1)).card = n := by
      rw [hSmallEmpty] at hCount
      simp [hD0] at hCount
      omega
    have hFullSet :
        (Finset.univ.filter
          (fun j : Fin n => (R j).card = r + 1)) = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      simpa using hFullCard.ge
    have hiMem : i ∈ (Finset.univ.filter
        (fun j : Fin n => (R j).card = r + 1)) := by
      rw [hFullSet]
      exact Finset.mem_univ i
    have hiFull : (R i).card = r + 1 :=
      (Finset.mem_filter.mp hiMem).2
    have hFloor : (N - D.card) / n = r + 1 := by
      rw [hD0, Nat.sub_zero, hN]
      exact Nat.mul_div_cancel_left (r + 1) hn
    exact Or.inl (by rw [hFloor]; exact hiFull)
  · have hDpos : 0 < D.card := Nat.pos_of_ne_zero hD0
    have hRemPos : 0 < n - D.card := Nat.sub_pos_of_lt hDlt
    have hRemLt : n - D.card < n := Nat.sub_lt hn hDpos
    have hDecomp : N - D.card = n * r + (n - D.card) := by
      have hMul : n * (r + 1) = n * r + n := by ring
      omega
    have hFloor : (N - D.card) / n = r := by
      rw [hDecomp, Nat.mul_add_div hn r (n - D.card)]
      simp [Nat.div_eq_of_lt hRemLt]
    have hMod : (N - D.card) % n = n - D.card := by
      rw [hDecomp, Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt hRemLt
    have hUpper : FairDivision.upperSize n (N - D.card) = r + 1 := by
      simp [FairDivision.upperSize, hFloor, hMod,
        Nat.ne_of_gt hRemPos]
    rcases hSizes i with hiSize | hiSize
    · exact Or.inl (by rw [hFloor]; exact hiSize)
    · exact Or.inr (by rw [hUpper]; exact hiSize)

end FairDivision.BF
