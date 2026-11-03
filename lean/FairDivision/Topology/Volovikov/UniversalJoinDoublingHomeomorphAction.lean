import FairDivision.Topology.Volovikov.UniversalJoinDoublingHomeomorph
import FairDivision.Topology.Volovikov.UniversalJoinDoublingEquivariance

/-!
# Equivariance of the doubled-join homeomorphism

The color-block homeomorphism intertwines diagonal translation on the
join quotient with coordinate translation on the doubled finite join.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity

/-- The doubled-join homeomorphism respects simultaneous label translation. -/
theorem doubledJoinHomeomorph_equivariant
    {m : ℕ} {G : Type*} [AddGroup G] [Fintype G]
    (a : G)
    (z : TopologicalJoin
      (simplicialRealization (universalJoinComplex m G))
      (simplicialRealization (universalJoinComplex m G))) :
    doubledJoinHomeomorph m G
        (topologicalJoinMap
          (translateJoinMap a) (translateJoinMap a) z) =
      translateJoinRealization a (doubledJoinHomeomorph m G z) := by
  exact doubledJoinMap_equivariant a z

/-- The inverse color-block homeomorphism respects translation too. -/
theorem doubledJoinHomeomorph_symm_equivariant
    {m : ℕ} {G : Type*} [AddGroup G] [Fintype G]
    (a : G)
    (w : simplicialRealization (universalJoinComplex (m + m) G)) :
    (doubledJoinHomeomorph m G).symm (translateJoinRealization a w) =
      topologicalJoinMap
        (translateJoinMap a) (translateJoinMap a)
        ((doubledJoinHomeomorph m G).symm w) := by
  apply (doubledJoinHomeomorph m G).injective
  rw [doubledJoinHomeomorph_equivariant]
  simp

end FairDivision.Topology.Volovikov
