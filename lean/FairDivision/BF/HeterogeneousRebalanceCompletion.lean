import FairDivision.BF.HeterogeneousRebalanceStep

/-!
# BF Section 5: completing the real-bundle rebalancing

The manuscript repeatedly shortens a distinct full real donor and gives its
removed item to a deficient recipient. The exact item count guarantees a
donor at every stage. Strong induction on the deficient-bundle count ends
with all bundles having one of the two balanced sizes.
-/

set_option autoImplicit false

namespace FairDivision.BF

/-- Repeated donor-to-recipient transfers leave no size-`r-1` bundle. -/
theorem complete_hetero_real_rebalancing
    {n m r d : ℕ} {Rstock : Finset (Fin m)}
    {v : Fin n → Finset (Fin m) → ℝ} {τ : Fin n → ℝ}
    (R : Fin n → Finset (Fin m))
    (hr : 1 ≤ r)
    (hTotal : Rstock.card + d = n * (r + 1))
    (hDlt : d < n)
    (hR : HeteroRealState r Rstock v τ R) :
    ∃ A : Fin n → Finset (Fin m),
      HeteroRealState r Rstock v τ A ∧
      ∀ i : Fin n, (A i).card = r ∨ (A i).card = r + 1 := by
  classical
  let smallCount (A : Fin n → Finset (Fin m)) : ℕ :=
    (Finset.univ.filter (fun i : Fin n => (A i).card = r - 1)).card
  let P : ℕ → Prop := fun s =>
    ∀ A : Fin n → Finset (Fin m),
      HeteroRealState r Rstock v τ A → smallCount A = s →
      ∃ C : Fin n → Finset (Fin m),
        HeteroRealState r Rstock v τ C ∧
        ∀ i : Fin n, (C i).card = r ∨ (C i).card = r + 1
  have hMain : ∀ s : ℕ, P s := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro A hA hs
      by_cases hSmall : (Finset.univ.filter
          (fun i : Fin n => (A i).card = r - 1)).Nonempty
      · obtain ⟨A', hA', hDecrease⟩ :=
          hA.rebalance_one hr hTotal hDlt hSmall
        have hLt : smallCount A' < s := by
          change smallCount A' < smallCount A at hDecrease
          rw [hs] at hDecrease
          exact hDecrease
        exact ih (smallCount A') hLt A' hA' rfl
      · refine ⟨A, hA, ?_⟩
        intro i
        rcases (hA.1 i).2 with hLow | hMid | hHigh
        · exfalso
          exact hSmall ⟨i, Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hLow.1⟩⟩
        · exact Or.inl hMid.1
        · exact Or.inr hHigh.1
  exact hMain (smallCount R) R hR rfl

/-- The terminal rebalanced state has deletion brackets for every owner. -/
theorem HeteroRealState.balanced_brackets
    {n m r : ℕ} {Rstock : Finset (Fin m)}
    {v : Fin n → Finset (Fin m) → ℝ} {τ : Fin n → ℝ}
    {A : Fin n → Finset (Fin m)}
    (hA : HeteroRealState r Rstock v τ A)
    (hr : 1 ≤ r)
    (hSizes : ∀ i : Fin n, (A i).card = r ∨ (A i).card = r + 1) :
    ∀ i : Fin n, HeteroBrackets v τ i (A i) := by
  intro i
  rcases (hA.1 i).2 with hLow | hMid | hHigh
  · rcases hSizes i with hSize | hSize <;> omega
  · exact hMid.2
  · exact hHigh.2.1

end FairDivision.BF
