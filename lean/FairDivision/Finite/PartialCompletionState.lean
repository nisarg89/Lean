import FairDivision.Finite.ShortCount
import FairDivision.Finite.ShortBundleFill
import FairDivision.Finite.DummyFreeFullPosition

/-!
# State of the BF lottery-to-allocation completion

The manuscript's three filling phases maintain the same invariant: every
bundle is short with value exactly `t`, or full with one-deletion values
bracketing `t`; bundles are disjoint, lie in the item stock, and contain at
most one dummy. The remaining-item count equals the short-bundle count.
-/

set_option autoImplicit false

namespace FairDivision.Finite

/-- The local short/full alternative maintained while completing bundles. -/
def ShortOrFullAt {α : Type*} [DecidableEq α]
    (v : Finset α → ℝ) (r : ℕ) (t : ℝ) (B : Finset α) : Prop :=
  (B.card = r ∧ v B = t) ∨
    (B.card = r + 1 ∧ FairDivision.BracketsOneDeletion v B t)

/-- The simultaneous state invariant for the manuscript's completion. -/
def PartialCompletionState {α : Type*} [DecidableEq α]
    (n r : ℕ) (U D : Finset α) (v : Finset α → ℝ) (t : ℝ)
    (B : Fin n → Finset α) : Prop :=
  (∀ i, B i ⊆ U ∧ ShortOrFullAt v r t (B i)) ∧
  (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
  (∀ i, (B i ∩ D).card ≤ 1)

/-- Every bundle in a completion state is either short or full. -/
theorem PartialCompletionState.size {α : Type*} [DecidableEq α]
    {n r : ℕ} {U D : Finset α} {v : Finset α → ℝ} {t : ℝ}
    {B : Fin n → Finset α}
    (h : PartialCompletionState n r U D v t B) (i : Fin n) :
    (B i).card = r ∨ (B i).card = r + 1 := by
  exact (h.1 i).2.elim (fun hs => Or.inl hs.1) (fun hf => Or.inr hf.1)

/-- The manuscript's count invariant: exactly one item remains for each
short position. -/
theorem PartialCompletionState.unallocated_count {α : Type*} [DecidableEq α]
    {n r : ℕ} {U D : Finset α} {v : Finset α → ℝ} {t : ℝ}
    {B : Fin n → Finset α}
    (h : PartialCompletionState n r U D v t B)
    (hTotal : U.card = n * (r + 1)) :
    (U \ Finset.univ.biUnion B).card =
      (Finset.univ.filter (fun i : Fin n => (B i).card = r)).card := by
  exact card_unallocated_eq_short_count n r U B
    (fun i => (h.1 i).1) h.2.1 hTotal (fun i => h.size i)

/-- A short bundle in the completion state has value exactly the common
threshold. -/
theorem PartialCompletionState.short_value {α : Type*} [DecidableEq α]
    {n r : ℕ} {U D : Finset α} {v : Finset α → ℝ} {t : ℝ}
    {B : Fin n → Finset α}
    (h : PartialCompletionState n r U D v t B)
    (i : Fin n) (hi : (B i).card = r) : v (B i) = t := by
  rcases (h.1 i).2 with hs | hf
  · exact hs.2
  · omega

/-- A full bundle in the completion state retains its one-deletion
threshold bracket. -/
theorem PartialCompletionState.full_bracket {α : Type*} [DecidableEq α]
    {n r : ℕ} {U D : Finset α} {v : Finset α → ℝ} {t : ℝ}
    {B : Fin n → Finset α}
    (h : PartialCompletionState n r U D v t B)
    (i : Fin n) (hi : (B i).card = r + 1) :
    FairDivision.BracketsOneDeletion v (B i) t := by
  rcases (h.1 i).2 with hs | hf
  · omega
  · exact hf.2

end FairDivision.Finite
