import FairDivision.Finite.DummyFreePosition

/-!
# A full dummy-free donor bundle

In the manuscript's final completion phase an unallocated dummy remains,
while every short bundle without a dummy has already been filled. Counting
dummy items then supplies a full bundle containing only real items. This is
the donor for the replacement lemma.
-/

set_option autoImplicit false

namespace FairDivision.Finite

/-- If an unused dummy remains and no dummy-free bundle is short, a full
dummy-free bundle is available for the manuscript's replacement swap. -/
theorem exists_full_dummy_free_position {α : Type*} [DecidableEq α]
    (n r : ℕ) (D : Finset α) (B : Fin n → Finset α)
    (hD : D.card ≤ n)
    (hPair : ∀ i j : Fin n, i ≠ j → Disjoint (B i) (B j))
    (e : α) (heD : e ∈ D) (heUnused : ∀ i : Fin n, e ∉ B i)
    (hNoShortFree : ∀ i : Fin n, B i ∩ D = ∅ → (B i).card = r + 1) :
    ∃ j : Fin n, B j ∩ D = ∅ ∧ (B j).card = r + 1 := by
  classical
  have hDPos : 0 < D.card := Finset.card_pos.mpr ⟨e, heD⟩
  have hEraseCard : (D.erase e).card < n := by
    rw [Finset.card_erase_of_mem heD]
    omega
  obtain ⟨j, hj⟩ := exists_dummy_free_position n (D.erase e) B
    hEraseCard hPair
  have hEq : B j ∩ D.erase e = B j ∩ D := by
    ext x
    by_cases hxe : x = e
    · subst x
      simp [heUnused j]
    · simp [hxe]
  rw [hEq] at hj
  exact ⟨j, hj, hNoShortFree j hj⟩

end FairDivision.Finite
