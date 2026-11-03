import FairDivision.Topology.VariableDummyInductionControl

/-!
# Slack in the uniform BF configuration complex

The manuscript specializes the variable-size connectivity induction to
`k = n/a` positions, requirement `aq-1`, dummy cap `a`, and total item count
`nq`. Its useful dummy count is exactly `n`, and its slack is `n/a`.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- At each uniform position the useful dummy capacity is exactly `a`. -/
theorem variableUniform_useful_at (a q : ℕ)
    (ha : 0 < a) (hq : 2 ≤ q) :
    min (a * q - 1) a = a := by
  have hmul : a * 2 ≤ a * q := Nat.mul_le_mul_left a hq
  apply Nat.min_eq_right
  omega

/-- The total useful dummy capacity of the uniform complex is `n`. -/
theorem variableUniform_useful_total (n q a : ℕ)
    (ha : 0 < a) (hq : 2 ≤ q) (hdiv : a ∣ n) :
    variableUsefulDummyTotal
      (fun _ : Fin (n / a) => a * q - 1) (fun _ => a) = n := by
  simp [variableUsefulDummyTotal, variableUniform_useful_at a q ha hq,
    Nat.div_mul_cancel hdiv]

/-- The uniform requirement total has the expected product form. -/
theorem variableUniform_requirement_total (n q a : ℕ) :
    variableRequirementTotal (fun _ : Fin (n / a) => a * q - 1) =
      (n / a) * (a * q - 1) := by
  simp [variableRequirementTotal]

/-- The uniform requirement count plus the number of positions is `nq`. -/
theorem variableUniform_requirement_add_positions (n q a : ℕ)
    (ha : 0 < a) (hq : 2 ≤ q) (hdiv : a ∣ n) :
    (n / a) * (a * q - 1) + n / a = n * q := by
  have hAq : 1 ≤ a * q := by
    have hOne : 1 ≤ a := ha
    have hmul := Nat.mul_le_mul_right q hOne
    omega
  calc
    (n / a) * (a * q - 1) + n / a =
        (n / a) * ((a * q - 1) + 1) := by ring
    _ = (n / a) * (a * q) := by rw [Nat.sub_add_cancel hAq]
    _ = ((n / a) * a) * q := by ring
    _ = n * q := by rw [Nat.div_mul_cancel hdiv]

/-- The uniform full-stock instance satisfies the induction's admissibility
hypothesis. -/
theorem variableUniform_admissible {m : ℕ}
    (n q a : ℕ) (D E : Finset (Fin m))
    (ha : 0 < a) (hq : 2 ≤ q) (hdiv : a ∣ n)
    (hTotal : E.card + D.card = n * q) (hD : D.card ≤ n) :
    VariableSlackAdmissible E.card D.card
      (fun _ : Fin (n / a) => a * q - 1) (fun _ => a) := by
  have hReq := variableUniform_requirement_add_positions n q a ha hq hdiv
  unfold VariableSlackAdmissible
  rw [variableUniform_useful_total n q a ha hq hdiv,
    variableUniform_requirement_total n q a, Nat.min_eq_left hD]
  have hK : 0 ≤ n / a := Nat.zero_le _
  omega

/-- The uniform connectivity slack is the number `n/a` of positions. -/
theorem variableUniform_slack {m : ℕ}
    (n q a : ℕ) (D E : Finset (Fin m))
    (ha : 0 < a) (hq : 2 ≤ q) (hdiv : a ∣ n)
    (hTotal : E.card + D.card = n * q) (hD : D.card ≤ n) :
    variableSlack E.card D.card
      (fun _ : Fin (n / a) => a * q - 1) (fun _ => a) = n / a := by
  have hReq := variableUniform_requirement_add_positions n q a ha hq hdiv
  unfold variableSlack
  rw [variableUniform_useful_total n q a ha hq hdiv,
    variableUniform_requirement_total n q a, Nat.min_eq_left hD]
  have hK : 0 ≤ n / a := Nat.zero_le _
  omega

end FairDivision.Topology
