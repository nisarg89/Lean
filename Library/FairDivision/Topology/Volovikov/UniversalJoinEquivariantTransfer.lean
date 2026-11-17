import FairDivision.Topology.Volovikov.UniversalJoinEquivariantExtension
import FairDivision.Topology.Volovikov.JoinVertexSkeleton

/-!
# Geometric transfer to a finite universal join

A nonempty sufficiently null-connected target admits an equivariant map
from the finite universal join. The map starts on the discrete vertex
skeleton and extends over free orbits of simplex cells.

Combined with a separately proved no-map theorem for the join and the
reduced regular representation sphere, this yields the desired obstruction
for any such target. No no-map theorem is asserted in this file.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity

/-- Geometric equivariant transfer from a finite universal join into a
sufficiently connected target. -/
theorem exists_equivariant_universalJoinMap
    {m k : ℕ} {G X : Type*}
    [AddGroup G] [Fintype G] [TopologicalSpace X]
    (hm : m ≤ k + 2)
    (hX : NullConnectedSpace k X)
    (targetAction : G → X ≃ₜ X)
    (hAction : IsContinuousAddAction targetAction) :
    ∃ f : C(simplicialRealization (universalJoinComplex m G), X),
      IsEquivariantJoinMap (universalJoinComplex m G)
        universalJoinComplex_invariant targetAction f := by
  let x0 : X := Classical.choice hX.1
  obtain ⟨f, _, hf⟩ :=
    exists_equivariant_universalJoinExtension hm hX targetAction
      hAction (equivariantVertexSkeletonMap targetAction x0)
      (equivariantVertexSkeletonMap_equivariant
        targetAction hAction x0)
  exact ⟨f, hf⟩

end FairDivision.Topology.Volovikov
