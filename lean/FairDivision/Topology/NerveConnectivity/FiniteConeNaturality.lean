import FairDivision.Topology.NerveConnectivity.FiniteConeBaseRealization

/-!
# Naturality of finite-cone inclusions

The base embedding uses the same probability coordinates in a complex
and every larger complex. This exact equality is needed to show that
maps pasted on a chamber base and an overlap cone agree on their common
base.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe u

/-- Inclusion of a subcone in a larger finite cone. -/
def finiteConeInclusion {V : Type u} [Fintype V]
    {I K : PreAbstractSimplicialComplex V} (hIK : I ≤ K) :
    C(simplicialRealization (finiteConeComplex I),
      simplicialRealization (finiteConeComplex K)) :=
  ContinuousMap.inclusion (simplicialRealization_mono
    (finiteConeComplex_mono hIK))

/-- The base embedding commutes exactly with subcomplex inclusion. -/
theorem finiteConeBaseMap_natural {V : Type u} [Fintype V] [Nonempty V]
    {I K : PreAbstractSimplicialComplex V} (hIK : I ≤ K)
    (w : simplicialRealization I) :
    finiteConeInclusion hIK (finiteConeBaseMap I w) =
      finiteConeBaseMap K
        ⟨w.1, (simplicialRealization_mono hIK) w.2⟩ := by
  apply Subtype.ext
  rfl

end FairDivision.Topology.NerveConnectivity
