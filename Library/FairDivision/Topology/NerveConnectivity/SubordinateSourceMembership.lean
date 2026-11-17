import FairDivision.Topology.NerveConnectivity.SubordinateSourceCover

/-!
# Maps carried by subordinate source pieces

A point in a subordinate subcomplex lies in the chosen cover member
because its positive support is itself one of the subordinate faces.
This packages the target-subtype map needed for cone fillings.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- The realization of a subordinate source piece maps into its
chosen relatively open set. -/
theorem subordinateSourceComplex_image_mem
    {V : Type u} [Fintype V]
    (K : PreAbstractSimplicialComplex V) (n : ℕ)
    (U : Set (simplicialRealization K))
    (z : simplicialRealization (subordinateSourceComplex K n U)) :
    iteratedBarycentricRealizationHomeomorph K n
      ⟨z.1, (subordinateSourceComplex_le K n U) z.2⟩ ∈ U :=
  z.2.2 ⟨z.1, z.2.1⟩ (Finset.Subset.rfl)

/-- Restrict a source map to a subordinate piece and its selected
target open set. -/
noncomputable def subordinateSourceMapToOpen
    {V : Type u} [Fintype V]
    {X : Type v} [TopologicalSpace X]
    (K : PreAbstractSimplicialComplex V) (n : ℕ)
    (f : C(simplicialRealization K, X))
    (U : Set X) :
    C(simplicialRealization
      (subordinateSourceComplex K n (f ⁻¹' U)), U) := by
  let inc : C(simplicialRealization
      (subordinateSourceComplex K n (f ⁻¹' U)),
      simplicialRealization (iteratedBarycentricComplex K n)) :=
    ContinuousMap.inclusion (simplicialRealization_mono
      (subordinateSourceComplex_le K n (f ⁻¹' U)))
  let e : C(simplicialRealization (iteratedBarycentricComplex K n),
      simplicialRealization K) := iteratedBarycentricRealizationHomeomorph K n
  let g := f.comp (e.comp inc)
  refine ⟨fun z => ⟨g z, ?_⟩, ?_⟩
  · exact subordinateSourceComplex_image_mem K n (f ⁻¹' U) z
  · exact Continuous.subtype_mk g.continuous _

end FairDivision.Topology.NerveConnectivity
