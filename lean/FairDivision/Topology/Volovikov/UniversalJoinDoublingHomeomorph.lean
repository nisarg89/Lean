import FairDivision.Topology.Volovikov.UniversalJoinDoublingSurjective
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# A doubled finite universal join is a topological join

The weighted coordinate map is a continuous bijection from a compact join
quotient to the Hausdorff finite simplicial realization, hence a homeomorphism.
This geometric identification is independent of the later no-map obstruction.
-/

set_option autoImplicit false

open scoped unitInterval Topology Classical

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity

/-- Splitting the color set into two equal blocks identifies the doubled
finite universal join with a topological join of two smaller ones. -/
noncomputable def doubledJoinHomeomorph
    (m : ℕ) (G : Type*) [Fintype G] :
    TopologicalJoin
      (simplicialRealization (universalJoinComplex m G))
      (simplicialRealization (universalJoinComplex m G)) ≃ₜ
      simplicialRealization (universalJoinComplex (m + m) G) := by
  letI : CompactSpace (simplicialRealization (universalJoinComplex m G)) :=
    isCompact_iff_compactSpace.mp
      (simplicialRealization_isCompact (universalJoinComplex m G))
  letI : CompactSpace
      (TopologicalJoin
        (simplicialRealization (universalJoinComplex m G))
        (simplicialRealization (universalJoinComplex m G))) :=
    Quotient.compactSpace
  have h : IsHomeomorph (doubledJoinMap m G) := by
    rw [isHomeomorph_iff_continuous_bijective]
    exact ⟨(doubledJoinMap m G).continuous,
      doubledJoinMap_injective m G, doubledJoinMap_surjective m G⟩
  exact IsHomeomorph.homeomorph (doubledJoinMap m G) h

end FairDivision.Topology.Volovikov
