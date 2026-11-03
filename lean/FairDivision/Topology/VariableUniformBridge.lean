import FairDivision.Topology.VariableDummyFaceCriterion
import FairDivision.Topology.UnlabeledDummyFaceCriterion

/-!
# Uniform Section 3 complex as a variable-size special case

The connectivity induction uses position-dependent requirements. Its uniform
specialization is definitionally the corrected Section 3 complex, so the
induction can be applied without a separate topological comparison proof.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- Constant requirement and cap functions recover the Section 3 vertices. -/
theorem variableVertex_const_eq (k m r c : ℕ) (D : Finset (Fin m)) :
    VariableUnlabeledVertex k m D (fun _ => r) (fun _ => c) =
      UnlabeledDummyVertex k m r c D := rfl

/-- The uniform auxiliary complex is the constant-parameter instance of the
variable-size complex. -/
theorem variableDummyComplex_const_eq (k m r c : ℕ)
    (D : Finset (Fin m)) :
    variableDummyComplex k m D (fun _ => r) (fun _ => c) =
      unlabeledDummyComplex k m r c D := rfl

end FairDivision.Topology
