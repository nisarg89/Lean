import FairDivision.Topology.Volovikov.UniversalJoinDoublingEquivariance
import FairDivision.Topology.Volovikov.RealComplexJoinEquivariance
import FairDivision.Topology.Volovikov.UniversalJoinRealization

/-!
# Reduction of the real obstruction to a complex join obstruction

A zero-free centered real equivariant map on a finite universal join would
produce a zero-free centered complex equivariant map on the topological join
of two copies. The complex no-map theorem remains an explicit premise.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity

/-- The unresolved complex obstruction, stated on the join source that the
analytic doubling construction naturally produces. -/
def ComplexJoinNoMap (m : ℕ) (G : Type*)
    [AddCommGroup G] [Fintype G] : Prop :=
  ∀ F : C(TopologicalJoin
      (simplicialRealization (universalJoinComplex m G))
      (simplicialRealization (universalJoinComplex m G)), G → ℂ),
    (∀ z, ∑ g : G, F z g = 0) →
    (∀ z, F z ≠ 0) →
    (∀ (a : G) (z : TopologicalJoin
      (simplicialRealization (universalJoinComplex m G))
      (simplicialRealization (universalJoinComplex m G))),
      F (topologicalJoinMap
        (translateJoinMap a)
        (translateJoinMap a) z) =
          complexRegularTranslate a (F z)) → False

/-- The complex finite-join obstruction implies its real counterpart by
placing two copies of the real map in the real and imaginary coordinates. -/
theorem realJoin_noMap_of_complexJoin_noMap
    {m : ℕ} {G : Type*} [AddCommGroup G] [Fintype G]
    (hcomplex : ComplexJoinNoMap m G)
    (f : C(simplicialRealization (universalJoinComplex m G), G → ℝ))
    (hcenter : ∀ x, ∑ g : G, f x g = 0)
    (hne : ∀ x, f x ≠ 0)
    (hequiv : ∀ (a : G)
      (x : simplicialRealization (universalJoinComplex m G))
      (g : G), f (translateJoinRealization a x) g = f x (g - a)) :
    False := by
  apply hcomplex (realComplexJoinMap f f)
  · intro z
    exact realComplexJoinMap_sum_zero f f hcenter hcenter z
  · intro z
    exact realComplexJoinMap_ne_zero f f hne hne z
  · intro a z
    exact realComplexJoinMap_equivariant
      (fun a => (translateJoinMap a))
      (fun a => (translateJoinMap a))
      f f hequiv hequiv a z

end FairDivision.Topology.Volovikov
