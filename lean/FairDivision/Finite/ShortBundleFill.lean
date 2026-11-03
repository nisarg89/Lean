import FairDivision.Finite.ShortExtension

/-!
# Filling a short BF bundle

The lottery-to-allocation proof fills a short exact-value bundle with one
unused item. Deleting that item recovers the old value, so the new full
bundle brackets the equitable threshold. A real inserted item leaves the
dummy count unchanged.
-/

set_option autoImplicit false

namespace FairDivision.Finite

/-- Inserting any fresh item into a short exact-value bundle produces a
full bundle whose one-item deletions bracket the same value. -/
theorem short_bundle_fill {α : Type*} [DecidableEq α]
    (v : Finset α → ℝ) (B : Finset α) (r : ℕ) (t : ℝ)
    (hSize : B.card = r) (hVal : v B = t)
    (e : α) (he : e ∉ B) :
    (insert e B).card = r + 1 ∧
      FairDivision.BracketsOneDeletion v (insert e B) t := by
  constructor
  · simpa [he, hSize]
  · exact bracketsOneDeletion_insert_of_eq v B t hVal e he

/-- Inserting an unused real item does not increase the number of dummy
items in the bundle. -/
theorem short_bundle_fill_real_dummy_count {α : Type*} [DecidableEq α]
    (B D : Finset α) (e : α) (heD : e ∉ D) :
    (insert e B ∩ D).card = (B ∩ D).card := by
  have hEq : insert e B ∩ D = B ∩ D := by
    ext x
    by_cases hxe : x = e
    · subst x
      simp [heD]
    · simp [hxe]
  rw [hEq]

/-- Filling a dummy-free short bundle with a dummy gives exactly one dummy
item, as required by the manuscript's compatible-bundle cap. -/
theorem short_bundle_fill_dummy_count {α : Type*} [DecidableEq α]
    (B D : Finset α) (e : α) (heD : e ∈ D)
    (hNoDummy : B ∩ D = ∅) :
    (insert e B ∩ D).card = 1 := by
  have hEq : insert e B ∩ D = {e} := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxe | hxB, hxD⟩
      · exact hxe
      · have hxInter : x ∈ B ∩ D := Finset.mem_inter.mpr ⟨hxB, hxD⟩
        rw [hNoDummy] at hxInter
        have hFalse : False := by simpa [hNoDummy] using hxInter
        exact hFalse.elim
    · intro hxe
      subst x
      exact ⟨Or.inl rfl, heD⟩
  rw [hEq]
  simp

end FairDivision.Finite
