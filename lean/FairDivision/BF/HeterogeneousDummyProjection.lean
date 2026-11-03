import FairDivision.BF.HeterogeneousBrackets

/-!
# BF Section 5: projecting heterogeneous brackets to real items

The manuscript removes dummy items only after its augmented comparisons have
been established. If valuations ignore dummies, each optional-deletion
witness projects to an optional-deletion witness on the real bundle.
-/

set_option autoImplicit false

namespace FairDivision.BF

/-- Removing dummies commutes with an optional deletion after the deletion
witness itself is restricted to real items. -/
theorem realTrace_sdiff {m : ℕ} (B E D : Finset (Fin m))
    (hE : E ⊆ B) :
    (B \ D) \ (E \ D) = (B \ E) \ D := by
  ext x
  simp only [Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨hxB, hxD⟩, hxED⟩
    refine ⟨⟨hxB, ?_⟩, hxD⟩
    intro hxE
    exact hxED ⟨hxE, hxD⟩
  · rintro ⟨⟨hxB, hxE⟩, hxD⟩
    refine ⟨⟨hxB, hxD⟩, ?_⟩
    intro hxED
    exact hxE hxED.1

/-- A deletion of at most one item remains a deletion of at most one real
item after discarding dummies. -/
theorem CanDeleteOne.realTrace
    {m : ℕ} {E B D : Finset (Fin m)}
    (h : CanDeleteOne E B) :
    CanDeleteOne (E \ D) (B \ D) := by
  rcases h with ⟨hSub, hCard⟩
  exact ⟨Finset.sdiff_subset_sdiff hSub (Finset.Subset.rfl),
    (Finset.card_le_card Finset.sdiff_subset).trans hCard⟩

/-- If all agents' values ignore dummy items, the manuscript's heterogeneous
lower and upper brackets survive dummy removal. -/
theorem HeteroBrackets.realTrace
    {n m : ℕ} {v : Fin n → Finset (Fin m) → ℝ}
    {τ : Fin n → ℝ} {owner : Fin n}
    {B D : Finset (Fin m)}
    (h : HeteroBrackets v τ owner B)
    (hIgnore : ∀ j : Fin n, ∀ S : Finset (Fin m),
      v j (S \ D) = v j S) :
    HeteroBrackets v τ owner (B \ D) := by
  rcases h with ⟨hLower, hUpper⟩
  constructor
  · intro j
    obtain ⟨E, hDelete, hValue⟩ := hLower j
    refine ⟨E \ D, CanDeleteOne.realTrace hDelete, ?_⟩
    rw [realTrace_sdiff B E D hDelete.1, hIgnore j (B \ E)]
    exact hValue
  · obtain ⟨E, hDelete, hValue⟩ := hUpper
    refine ⟨E \ D, CanDeleteOne.realTrace hDelete, ?_⟩
    rw [realTrace_sdiff B E D hDelete.1, hIgnore owner (B \ E)]
    exact hValue

/-- Direct short-bundle comparisons also survive dummy removal. -/
theorem shortValues_realTrace
    {n m : ℕ} {v : Fin n → Finset (Fin m) → ℝ}
    {τ : Fin n → ℝ} {owner : Fin n}
    {B D : Finset (Fin m)}
    (hLower : ∀ j : Fin n, v j B ≤ τ j)
    (hUpper : τ owner ≤ v owner B)
    (hIgnore : ∀ j : Fin n, ∀ S : Finset (Fin m),
      v j (S \ D) = v j S) :
    (∀ j : Fin n, v j (B \ D) ≤ τ j) ∧
      τ owner ≤ v owner (B \ D) := by
  constructor
  · intro j
    rw [hIgnore j B]
    exact hLower j
  · rw [hIgnore owner B]
    exact hUpper

end FairDivision.BF
