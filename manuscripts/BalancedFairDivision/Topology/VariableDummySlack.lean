import Mathlib.Data.Finset.Sum
import Mathlib

/-!
# Arithmetic of the BF auxiliary-complex connectivity slack

For real stock size `N`, dummy stock size `d`, requirements `r`, and caps
`c`, the manuscript's slack is `N - ∑ r + min(d, ∑ min(r,c))`. We use a natural
number expression only under its nonnegativity hypothesis.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- Total dummy capacity that can actually be used at the positions. -/
def variableUsefulDummyTotal {k : ℕ} (r c : Fin k → ℕ) : ℕ :=
  ∑ i : Fin k, min (r i) (c i)

/-- Sum of the position requirements. -/
def variableRequirementTotal {k : ℕ} (r : Fin k → ℕ) : ℕ :=
  ∑ i : Fin k, r i

/-- Nonnegativity condition for the manuscript's connectivity slack. -/
def VariableSlackAdmissible {k : ℕ}
    (N d : ℕ) (r c : Fin k → ℕ) : Prop :=
  variableRequirementTotal r ≤ N + min d (variableUsefulDummyTotal r c)

/-- The natural-number connectivity slack, used only with
`VariableSlackAdmissible`. -/
def variableSlack {k : ℕ}
    (N d : ℕ) (r c : Fin k → ℕ) : ℕ :=
  N + min d (variableUsefulDummyTotal r c) - variableRequirementTotal r

/-- Useful dummy demand never exceeds total required capacity. -/
theorem variableUsefulDummyTotal_le_requirements {k : ℕ}
    (r c : Fin k → ℕ) :
    variableUsefulDummyTotal r c ≤ variableRequirementTotal r := by
  unfold variableUsefulDummyTotal variableRequirementTotal
  exact Finset.sum_le_sum (fun i _ => Nat.min_le_left _ _)

/-- Reducing requirements by valid dummy targets removes precisely their
aggregate number from the requirement total. -/
theorem variableRequirementTotal_sub_add {k : ℕ}
    (r u : Fin k → ℕ) (hu : ∀ i, u i ≤ r i) :
    variableRequirementTotal (fun i => r i - u i) +
      variableRequirementTotal u = variableRequirementTotal r := by
  unfold variableRequirementTotal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := hu i
  omega

/-- In the saturated-dummy branch, the slack becomes the ordinary excess
of real stock over the reduced total requirement. -/
theorem variableSlack_saturation {k : ℕ}
    (N d : ℕ) (r c u : Fin k → ℕ)
    (hu : ∀ i, u i ≤ r i)
    (hUseful : variableUsefulDummyTotal r c = variableRequirementTotal u)
    (hd : variableRequirementTotal u ≤ d) :
    variableSlack N d r c =
      N - variableRequirementTotal (fun i => r i - u i) := by
  have hsum := variableRequirementTotal_sub_add r u hu
  unfold variableSlack
  rw [hUseful, Nat.min_eq_right hd]
  omega

end FairDivision.Topology
