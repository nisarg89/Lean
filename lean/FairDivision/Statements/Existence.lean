import FairDivision.Definitions

/-!
# Existence statements to be compared with the two manuscripts

The four propositions below are the reader-facing certificate boundary. This
file contains no proof. `Challenge/Existence.lean` states the corresponding
named theorems with isolated placeholders; proof modules must never import it.
-/

set_option autoImplicit false

namespace FairDivision.Statements

/-- Balanced Fair Division manuscript, Theorem `thm:identical-prime-power` (Section 3).
For arbitrary, not necessarily monotone or normalized common valuations, a
prime-power number of agents has a balanced EF[1,1] allocation. The proof
may establish the stronger common-threshold property internally. -/
def identicalPrimePower : Prop :=
  ∀ (n m : ℕ), 0 < n → IsPrimePowerAgentCount n →
    ∀ v : Finset (Fin m) → ℝ,
      ∃ A : Allocation n m, IsBalanced A ∧ IsEF11 (fun _ => v) A

/-- Balanced Fair Division manuscript, Theorem `thm:identical-all-n` (Section 4).
The balanced EF[1,1] conclusion holds for every positive agent count. -/
def identicalAllN : Prop :=
  ∀ (n m : ℕ), 0 < n →
    ∀ v : Finset (Fin m) → ℝ,
      ∃ A : Allocation n m, IsBalanced A ∧ IsEF11 (fun _ => v) A

/-- Balanced Fair Division manuscript, Theorem `thm:heterogeneous-all-m` (Section 5).
Each agent has an arbitrary, possibly nonmonotone and unnormalized valuation. -/
def heterogeneousPrimePower : Prop :=
  ∀ (n m : ℕ), 0 < n → IsPrimePowerAgentCount n →
    ∀ v : Fin n → Finset (Fin m) → ℝ,
      ∃ A : Allocation n m, IsBalanced A ∧ IsEF11 v A

/-- the fair and efficient allocation manuscript, Theorem `thm:balanced-main` (Section 3).
For arbitrary signed additive values, the integral allocation is balanced and
EF[1,1], and admits no Pareto improvement by a *balanced fractional*
allocation. If the item count is divisible by the agent count, it is also swap
EF in the paper's two-post-swap-bundle sense. -/
def balancedFairEfficient : Prop :=
  ∀ (n m : ℕ), 0 < n →
    ∀ v : Fin n → Fin m → ℝ,
      ∃ A : Allocation n m,
        IsBalanced A ∧
        IsEF11 (additiveAsBundleValue v) A ∧
        IsConstrainedFPO v A ∧
        (n ∣ m → IsSwapEF v A)

end FairDivision.Statements
