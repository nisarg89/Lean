import FairDivision.Finite.Replacement

/-!
# One-deletion comparison after removing dummy items

The full augmented bundles in the BF manuscript bracket a common threshold
using exact one-item deletions. A deleted item may be a dummy. On the real
bundle this becomes an optional deletion of at most one real item.
-/

set_option autoImplicit false

namespace FairDivision.Finite

/-- The exact one-deletion bracket on an augmented bundle becomes an optional
one-deletion threshold statement on its real trace. -/
theorem bracketsOneDeletion_removeDummies {α : Type*} [DecidableEq α]
    (v : Finset α → ℝ) (B D : Finset α) (t : ℝ)
    (h : FairDivision.BracketsOneDeletion (fun F => v (F \ D)) B t) :
    (∃ E : Finset α, E ⊆ B \ D ∧ E.card ≤ 1 ∧
      v ((B \ D) \ E) ≤ t) ∧
    (∃ E : Finset α, E ⊆ B \ D ∧ E.card ≤ 1 ∧
      t ≤ v ((B \ D) \ E)) := by
  obtain ⟨⟨x, hx, hlow⟩, ⟨y, hy, hhigh⟩⟩ := h
  have hsubset (z : α) (hz : z ∈ B) :
      ({z} : Finset α) \ D ⊆ B \ D := by
    intro w hw
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at hw ⊢
    refine ⟨?_,hw.2⟩
    rw [hw.1]
    exact hz
  have hsize (z : α) : (({z} : Finset α) \ D).card ≤ 1 := by
    calc
      (({z} : Finset α) \ D).card ≤ ({z} : Finset α).card :=
        Finset.card_le_card Finset.sdiff_subset
      _ = 1 := by simp
  have hcomm (z : α) :
      (B \ D) \ (({z} : Finset α) \ D) = (B.erase z) \ D := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_erase]
    tauto
  constructor
  · refine ⟨{x} \ D, hsubset x hx, hsize x, ?_⟩
    simpa only [hcomm] using hlow
  · refine ⟨{y} \ D, hsubset y hy, hsize y, ?_⟩
    simpa only [hcomm] using hhigh

end FairDivision.Finite
