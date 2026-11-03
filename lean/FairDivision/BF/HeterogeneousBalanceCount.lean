import FairDivision.BF.HeterogeneousRealCompletion

/-!
# BF Section 5: counting real full and undersized bundles

After all real items have been assigned, removing dummies leaves bundles of
sizes `q`, `q-1`, or `q-2`. The manuscript's item count says that the number
of size-`q` donors exceeds the number of size-`q-2` recipients by `n-d`,
where `d` is the number of dummies. This file proves the exact finite count.
-/

set_option autoImplicit false

namespace FairDivision.BF

/-- The exact donor/recipient count after removing dummies. Here `r=q-1`;
real full bundles have size `r+1`, while undersized bundles have size `r-1`.
The equality is stated without subtraction so it also covers edge cases. -/
theorem real_full_small_count
    {n m r : ℕ} (U D : Finset (Fin m))
    (v : Fin n → Finset (Fin m) → ℝ) (τ : Fin n → ℝ)
    (B : Fin n → Finset (Fin m))
    (hr : 1 ≤ r) (hDU : D ⊆ U)
    (hTotal : U.card = n * (r + 1))
    (hB : HeteroPartialState r U D v τ B)
    (hRealCovered : U \ D ⊆ Finset.univ.biUnion B) :
    (Finset.univ.filter
      (fun i : Fin n => (B i \ D).card = r - 1)).card + n =
    (Finset.univ.filter
      (fun i : Fin n => (B i \ D).card = r + 1)).card + D.card := by
  classical
  let R : Fin n → Finset (Fin m) := fun i => B i \ D
  have hSize (i : Fin n) :
      (R i).card = r - 1 ∨ (R i).card = r ∨ (R i).card = r + 1 := by
    have hCard := Finset.card_sdiff_add_card_inter (B i) D
    have hCap := hB.2.2 i
    rcases hB.size i with hShort | hFull
    · by_cases hZero : (B i ∩ D).card = 0
      · exact Or.inr (Or.inl (by dsimp [R]; omega))
      · exact Or.inl (by dsimp [R]; omega)
    · by_cases hZero : (B i ∩ D).card = 0
      · exact Or.inr (Or.inr (by dsimp [R]; omega))
      · exact Or.inr (Or.inl (by dsimp [R]; omega))
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
  have hPair : ∀ i j : Fin n, i ≠ j → Disjoint (R i) (R j) := by
    intro i j hij
    exact (hB.2.1 i j hij).mono Finset.sdiff_subset Finset.sdiff_subset
  have hPairSet :
      ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint R := by
    intro i _ j _ hij
    exact hPair i j hij
  have hCardUnion : (Finset.univ.biUnion R).card =
      ∑ i : Fin n, (R i).card := Finset.card_biUnion hPairSet
  have hRealUnion : Finset.univ.biUnion R = U \ D := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, _, hRi⟩ := Finset.mem_biUnion.mp hx
      have hCi : x ∈ B i := (Finset.mem_sdiff.mp hRi).1
      have hNotD : x ∉ D := (Finset.mem_sdiff.mp hRi).2
      exact Finset.mem_sdiff.mpr ⟨(hB.1 i).1 hCi, hNotD⟩
    · intro hx
      have hIn : x ∈ Finset.univ.biUnion B := hRealCovered hx
      obtain ⟨i, _, hCi⟩ := Finset.mem_biUnion.mp hIn
      exact Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ _,
          Finset.mem_sdiff.mpr ⟨hCi, (Finset.mem_sdiff.mp hx).2⟩⟩
  have hSumReal : (∑ i : Fin n, (R i).card) + D.card = n * (r + 1) := by
    calc
      (∑ i : Fin n, (R i).card) + D.card =
          (U \ D).card + D.card := by rw [← hCardUnion, hRealUnion]
      _ = U.card := Finset.card_sdiff_add_card_eq_card hDU
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
  change (Finset.univ.filter
    (fun i : Fin n => (R i).card = r - 1)).card + n =
    (Finset.univ.filter
      (fun i : Fin n => (R i).card = r + 1)).card + D.card
  omega


/-- The manuscript's count `f-k=n-d>0` pairs every deficient real bundle
with a distinct full real donor. The embedding records precisely that pairing. -/
theorem real_small_full_matching
    {n m r : ℕ} (U D : Finset (Fin m))
    (v : Fin n → Finset (Fin m) → ℝ) (τ : Fin n → ℝ)
    (B : Fin n → Finset (Fin m))
    (hr : 1 ≤ r) (hDU : D ⊆ U)
    (hTotal : U.card = n * (r + 1))
    (hDlt : D.card < n)
    (hB : HeteroPartialState r U D v τ B)
    (hRealCovered : U \ D ⊆ Finset.univ.biUnion B) :
    Nonempty
      ({i : Fin n // (B i \ D).card = r - 1} ↪
        {i : Fin n // (B i \ D).card = r + 1}) := by
  classical
  have hCount := real_full_small_count U D v τ B hr hDU hTotal hB hRealCovered
  have hCard :
      (Finset.univ.filter
        (fun i : Fin n => (B i \ D).card = r - 1)).card ≤
      (Finset.univ.filter
        (fun i : Fin n => (B i \ D).card = r + 1)).card := by
    omega
  apply Function.Embedding.nonempty_of_card_le
  simpa [Fintype.card_subtype] using hCard

end FairDivision.BF
