import FairDivision.BF.SwapThresholdPositive
import FairDivision.BF.SwapThresholdNegative

/-!
# Reader-facing sharp swap threshold from BF Section 7

Review `SwapDefinitions` and the two theorem statements below against
`thm:swap`. The proof uses exactly the manuscript's complementary-swap
argument and continuous random q-layer perturbation/first-moment argument.
Its external probability ingredients are the existing Mathlib finite
product measure and PFR's extracted disjoint-block independence theorem.
-/

set_option autoImplicit false

namespace FairDivision.BF

/-- `thm:swap`, both clauses with the manuscript's quantifiers. The q=0
case in the first clause has no envy; the second clause uses the SAME
common valuation for EFX and the t-swap impossibility. -/
theorem sharp_swap_threshold (t q : ℕ) (ht : 1≤t) :
    (q≤2*t→∀n : ℕ,∀v : Fin n→Finset (Fin (n*q))→ℝ,
      ∀A : Allocation n (n*q),HasEqualBundleSize A q→IsTSwapEF t v A) ∧
    (2*t+1≤q→∃N : ℕ,∀n≥N,∃v : Finset (Fin (n*q))→ℝ,
      IsNormalized v ∧StrictMono v ∧IsBundleSubmodular v ∧
      ∀A : Allocation n (n*q),HasEqualBundleSize A q→
        IsBundleEFX (fun _=>v) A ∧¬IsTSwapEF t (fun _=>v) A) := by
  constructor
  · intro hq n v A hSize
    exact every_equal_bundle_allocation_is_tSwapEF ht hq v A hSize
  · intro hq
    exact SwapThresholdNegative.exists_threshold_submodular_no_tSwapEF t q ht hq

end FairDivision.BF
