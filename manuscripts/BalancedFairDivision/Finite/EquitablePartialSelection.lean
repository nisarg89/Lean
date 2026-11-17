import FairDivision.Finite.EquitableBundleChoice

/-!
# Simultaneous bundle choices from an equitable compatible lottery

Each position chooses a short exact-value bundle or a full bracketed bundle.
Compatibility of the lottery pools makes these choices pairwise disjoint and
keeps the dummy cap. The remaining conversion step completes the allocation.
-/

set_option autoImplicit false

open scoped BigOperators

namespace FairDivision.Finite

open FairDivision.Topology

/-- Simultaneous disjoint short/full choices from an equitable compatible
lottery, before the manuscript's item-completion procedure. -/
theorem equitable_partial_selection {k m r c : ℕ}
    {D : Finset (Fin m)}
    (lot : stdSimplex ℝ (PartialVertex k D r c))
    (hComp : lot ∈ compatibleLotterySpace k m r c D)
    (v : Finset (Fin m) → ℝ) (t : ℝ)
    (hMean : ∀ i : Fin k,
      (∑ X : PartialVertex k D r c,
        lot.1 X * v (partialBundle X.1 i \ D)) = t) :
    ∃ B : Fin k → Finset (Fin m),
      (∀ i, B i ⊆ pool (lotterySupport lot) i ∧
        ((B i).card = r ∧ v (B i \ D) = t ∨
          (B i).card = r + 1 ∧
            FairDivision.BracketsOneDeletion
              (fun F => v (F \ D)) (B i) t)) ∧
      (∀ i j : Fin k, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ i : Fin k, (B i ∩ D).card ≤ c) := by
  classical
  have hChoice (i : Fin k) :
      ∃ B : Finset (Fin m),
        B ⊆ pool (lotterySupport lot) i ∧
        ((B.card = r ∧ v (B \ D) = t) ∨
          (B.card = r + 1 ∧
            FairDivision.BracketsOneDeletion
              (fun F => v (F \ D)) B t)) :=
    equitable_position_bundle lot v i t (hMean i)
  let B : Fin k → Finset (Fin m) :=
    fun i => Classical.choose (hChoice i)
  have hB (i : Fin k) :
      B i ⊆ pool (lotterySupport lot) i ∧
        ((B i).card = r ∧ v (B i \ D) = t ∨
          (B i).card = r + 1 ∧
            FairDivision.BracketsOneDeletion
              (fun F => v (F \ D)) (B i) t) :=
    Classical.choose_spec (hChoice i)
  refine ⟨B, hB, ?_, ?_⟩
  · intro i j hij
    exact choices_disjoint_of_compatible hComp B
      (fun i => (hB i).1) hij
  · intro i
    exact choice_dummy_bound_of_compatible hComp B
      (fun i => (hB i).1) i

end FairDivision.Finite
