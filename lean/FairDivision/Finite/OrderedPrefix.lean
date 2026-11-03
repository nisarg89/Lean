import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Card

/-!
# Initial segments of finite ordered sets

The BF manuscript fixes an order on each real stock or dummy reserve and
uses its first `k` members. This module packages that construction without
committing the combinatorial proofs to a particular enumeration syntax.
-/

set_option autoImplicit false

namespace FairDivision.Finite

/-- The first `k` members of a finite set in its ambient linear order. -/
noncomputable def orderedPrefix {α : Type*} [LinearOrder α]
    (S : Finset α) (k : ℕ) (hk : k ≤ S.card) : Finset α := by
  classical
  exact (Finset.univ : Finset (Fin k)).image (S.orderEmbOfCardLe hk)

/-- The initial segment has the prescribed size and lies in the source set. -/
theorem orderedPrefix_spec {α : Type*} [LinearOrder α]
    (S : Finset α) (k : ℕ) (hk : k ≤ S.card) :
    orderedPrefix S k hk ⊆ S ∧ (orderedPrefix S k hk).card = k := by
  classical
  constructor
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.orderEmbOfCardLe_mem S hk i
  · unfold orderedPrefix
    rw [Finset.card_image_of_injective]
    · simp
    · exact (S.orderEmbOfCardLe hk).injective

end FairDivision.Finite
