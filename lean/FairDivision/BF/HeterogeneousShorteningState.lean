import FairDivision.BF.HeterogeneousRealCompletion

/-!
# BF Section 5: retaining certified shortening during real-item completion

A dummy-free full bundle can donate one item in the manuscript's final
rebalancing step. Selected full bundles have the virtual valuation's
shortening certificate. A full bundle made by appending a real item to a
short selected bundle can be shortened back to that earlier bundle. This
file keeps that property explicit while the real-item completion proceeds.
-/

set_option autoImplicit false

namespace FairDivision.BF

/-- Every dummy-free full bundle has a certified short subbundle preserving
all observer and owner threshold comparisons. -/
def HeteroShortenable {n m : ℕ}
    (r : ℕ) (D : Finset (Fin m))
    (v : Fin n → Finset (Fin m) → ℝ) (τ : Fin n → ℝ)
    (B : Fin n → Finset (Fin m)) : Prop :=
  ∀ i : Fin n, (B i).card = r + 1 → B i ∩ D = ∅ →
    ∃ C : Finset (Fin m),
      C ⊆ B i ∧ C.card = r ∧ HeteroBrackets v τ i C

/-- The manuscript's virtual-valuation shortening witnesses establish the
initial donor property. The placeholder dummy belongs to the dummy set. -/
theorem heteroShortenable_of_selectedWitness
    {n m q : ℕ} {dummy : Fin m}
    {v : Fin n → Finset (Fin m) → ℝ}
    {E : Fin n → Finset (Fin m)}
    {u : Fin n → Fin n → ℝ}
    (w : ∀ s : Fin n, OwnerWitness q dummy v (E s) (u s) s)
    (hEF : ∀ i j : Fin n, u j i ≤ u i i)
    (D : Finset (Fin m)) (hDummyD : dummy ∈ D)
    (hq : 1 ≤ q) :
    HeteroShortenable (q - 1) D v (fun j => u j j)
      (fun i => (w i).B) := by
  intro i hFull hNoDummySet
  have hFull' : (w i).B.card = q := by
    simpa only [Nat.sub_add_cancel hq] using hFull
  have hNoDummy : dummy ∉ (w i).B := by
    intro hd
    have hmem : dummy ∈ (w i).B ∩ D :=
      Finset.mem_inter.mpr ⟨hd, hDummyD⟩
    simpa [hNoDummySet] using hmem
  exact selectedWitness_dummyFree_shorten w hEF i hFull' hNoDummy

/-- Filling an unused real item preserves the donor property. At the filled
position, the original short bundle is the certified shortening. -/
theorem HeteroShortenable.fill_real_unused
    {n m r : ℕ} {U D : Finset (Fin m)}
    {v : Fin n → Finset (Fin m) → ℝ} {τ : Fin n → ℝ}
    {B : Fin n → Finset (Fin m)}
    (hState : HeteroPartialState r U D v τ B)
    (hShorten : HeteroShortenable r D v τ B)
    (i : Fin n) (hi : (B i).card = r)
    (e : Fin m) :
    HeteroShortenable r D v τ
      (Function.update B i (insert e (B i))) := by
  classical
  intro j hFull hNoDummy
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self] at hFull hNoDummy ⊢
    obtain ⟨hLower, hUpper⟩ := hState.short_values i hi
    exact ⟨B i, Finset.subset_insert _ _, hi,
      HeteroBrackets.of_short_values hLower hUpper⟩
  · have hEq : Function.update B i (insert e (B i)) j = B j :=
      Function.update_of_ne hji _ _
    rw [hEq] at hFull hNoDummy ⊢
    exact hShorten j hFull hNoDummy

end FairDivision.BF
