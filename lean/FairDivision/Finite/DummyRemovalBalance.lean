import Mathlib

/-!
# Bundle sizes after deleting one-dummy-capped padding

In the BF manuscript the augmented item stock has exactly `nq` items and
every completed bundle has size `q` with at most one dummy. Removing dummies
therefore leaves each real bundle with size `q` or `q-1`. The global count of
dummies then identifies these as the balanced real-bundle sizes.
-/

set_option autoImplicit false

namespace FairDivision.Finite

/-- Removing at most one dummy from a full bundle leaves either its full
size or exactly one fewer item. -/
theorem card_removeDummies_full_or_short {α : Type*} [DecidableEq α]
    (B D : Finset α) (q : ℕ)
    (hFull : B.card = q) (hCap : (B ∩ D).card ≤ 1) :
    (B \ D).card = q ∨ (B \ D).card + 1 = q := by
  have hCard := Finset.card_sdiff_add_card_inter B D
  omega

end FairDivision.Finite
