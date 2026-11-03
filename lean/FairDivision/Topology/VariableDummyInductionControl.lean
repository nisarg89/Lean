import FairDivision.Topology.VariableDummyInductionArithmetic
import FairDivision.Topology.VariableDummyStock

/-!
# Arithmetic control of the BF connectivity induction

The induction measures real-stock size plus total required bundle size. Its
two reductions preserve the connectivity slack and decrease that measure.
Deleting one real item without decreasing a requirement lowers the slack by
one; this is the intersection case of the item cover.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- The useful dummy count is the requirement total of the pointwise useful
capacities. -/
theorem variableUseful_eq_requirement_min {k : ℕ}
    (r c : Fin k → ℕ) :
    variableUsefulDummyTotal r c =
      variableRequirementTotal (fun i => min (r i) (c i)) := rfl

/-- The saturation branch strictly decreases the induction measure. -/
theorem variableSaturation_measure_lt {k : ℕ}
    (N : ℕ) (r c : Fin k → ℕ)
    (hu : 0 < variableUsefulDummyTotal r c) :
    N + variableRequirementTotal
      (fun i => r i - min (r i) (c i)) <
    N + variableRequirementTotal r := by
  have hsum := variableRequirementTotal_sub_add r
    (fun i => min (r i) (c i))
    (fun i => Nat.min_le_left _ _)
  rw [← variableUseful_eq_requirement_min r c] at hsum
  omega

/-- The saturation branch preserves admissibility and slack after all
usable dummies are taken. -/
theorem variableSaturation_admissible_slack {k : ℕ}
    (N d : ℕ) (r c : Fin k → ℕ)
    (hAd : VariableSlackAdmissible N d r c)
    (hd : variableUsefulDummyTotal r c ≤ d) :
    VariableSlackAdmissible N 0
      (fun i => r i - min (r i) (c i)) (fun _ => 0) ∧
    variableSlack N 0
      (fun i => r i - min (r i) (c i)) (fun _ => 0) =
      variableSlack N d r c := by
  have hsum := variableRequirementTotal_sub_add r
    (fun i => min (r i) (c i))
    (fun i => Nat.min_le_left _ _)
  rw [← variableUseful_eq_requirement_min r c] at hsum
  have hreq : variableRequirementTotal
      (fun i => r i - min (r i) (c i)) ≤ N := by
    unfold VariableSlackAdmissible at hAd
    rw [Nat.min_eq_right hd] at hAd
    omega
  constructor
  · unfold VariableSlackAdmissible variableUsefulDummyTotal
    simpa using hreq
  · have hSat := variableSlack_saturation N d r c
      (fun i => min (r i) (c i))
      (fun i => Nat.min_le_left _ _) rfl hd
    rw [hSat]
    unfold variableSlack variableUsefulDummyTotal
    simp

/-- Deleting a forced real item and decreasing one positive requirement
strictly decreases the induction measure. -/
theorem variableForced_measure_lt {k : ℕ}
    (N : ℕ) (r : Fin k → ℕ) (a : Fin k)
    (hN : 0 < N) (hra : 0 < r a) :
    (N - 1) + variableRequirementTotal
      (variableDecreasedRequirement r a) <
    N + variableRequirementTotal r := by
  have hreq := variableRequirementTotal_decrease_add_one r a hra
  omega

/-- Removing an item from a finite real stock removes exactly one label. -/
theorem variableStock_erase_card_add_one {m : ℕ}
    (E : Finset (Fin m)) (e : Fin m) (he : e ∈ E) :
    (E.erase e).card + 1 = E.card := by
  simpa using Finset.card_erase_add_one he

/-- The forced-item branch preserves admissibility and connectivity slack. -/
theorem variableForced_admissible_slack {k m : ℕ}
    (D E : Finset (Fin m)) (r c : Fin k → ℕ)
    (e : Fin m) (he : e ∈ E) (a : Fin k)
    (hra : 0 < r a)
    (hAd : VariableSlackAdmissible E.card D.card r c)
    (hBranch : D.card < variableUsefulDummyTotal r c ∨
      variableUsefulDummyTotal r c = 0) :
    VariableSlackAdmissible (E.erase e).card D.card
      (variableDecreasedRequirement r a) c ∧
    variableSlack (E.erase e).card D.card
      (variableDecreasedRequirement r a) c =
      variableSlack E.card D.card r c := by
  have hCard := variableStock_erase_card_add_one E e he
  have hMin := variableMinDummy_decrease_eq D.card r c a hra hBranch
  have hReq := variableRequirementTotal_decrease_add_one r a hra
  constructor
  · unfold VariableSlackAdmissible at hAd ⊢
    rw [hMin]
    omega
  · have hN : 0 < E.card := by omega
    have h := variableSlack_decrease_eq E.card D.card r c a
      hN hra hBranch
    have hEq : (E.erase e).card = E.card - 1 := by omega
    rw [hEq]
    exact h

/-- A nonempty item-cover intersection has slack one lower after deleting
its forbidden item, provided the original slack is positive. -/
theorem variableIntersection_admissible_slack {k m : ℕ}
    (D E : Finset (Fin m)) (r c : Fin k → ℕ)
    (e : Fin m) (he : e ∈ E)
    (hAd : VariableSlackAdmissible E.card D.card r c)
    (hPositive : 0 < variableSlack E.card D.card r c) :
    VariableSlackAdmissible (E.erase e).card D.card r c ∧
    variableSlack (E.erase e).card D.card r c + 1 =
      variableSlack E.card D.card r c := by
  have hCard := variableStock_erase_card_add_one E e he
  constructor
  · unfold VariableSlackAdmissible at hAd ⊢
    unfold variableSlack at hPositive
    omega
  · unfold VariableSlackAdmissible at hAd
    unfold variableSlack at hPositive ⊢
    omega

end FairDivision.Topology
