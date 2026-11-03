import FairDivision.Topology.Volovikov.ReducedSphere

/-!
# Continuous coordinate relabeling on the reduced sphere

Each position permutation acts by a continuous map on the concrete centered
unit sphere. Group action laws can be packaged after the prime-power subgroup
interface is fixed.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

/-- Coordinate relabeling is continuous in the sphere point. -/
theorem relabelReducedSphere_continuous {n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    Continuous (relabelReducedSphere σ : ReducedSphere n → ReducedSphere n) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (continuous_apply (σ.symm i)).comp continuous_subtype_val

end FairDivision.Topology.Volovikov
