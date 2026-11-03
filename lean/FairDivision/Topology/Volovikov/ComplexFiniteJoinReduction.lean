import FairDivision.Topology.Volovikov.UniversalJoinDoublingHomeomorphAction
import FairDivision.Topology.Volovikov.RealComplexJoinReduction

/-!
# The complex obstruction on one finite universal join

The doubled-join homeomorphism transports the natural complex no-map
statement from a topological join quotient to the ordinary finite
universal join with twice as many colors. The resulting premise is the
precise finite-source theorem needed from equivariant topology.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity

/-- The unresolved complex no-map theorem on the doubled finite universal
join. This is an explicit proposition, not an axiom or a proved result. -/
def ComplexFiniteJoinNoMap (m : ℕ) (G : Type*)
    [AddCommGroup G] [Fintype G] : Prop :=
  ∀ F : C(simplicialRealization (universalJoinComplex (m + m) G), G → ℂ),
    (∀ w, ∑ g : G, F w g = 0) →
    (∀ w, F w ≠ 0) →
    (∀ (a : G)
      (w : simplicialRealization (universalJoinComplex (m + m) G)),
      F (translateJoinRealization a w) =
        complexRegularTranslate a (F w)) → False

/-- A no-map theorem on the finite doubled join yields the equivalent
obstruction on the topological join quotient. -/
theorem complexJoinNoMap_of_finiteJoinNoMap
    {m : ℕ} {G : Type*} [AddCommGroup G] [Fintype G]
    (hfinite : ComplexFiniteJoinNoMap m G) :
    ComplexJoinNoMap m G := by
  intro F hcenter hne hequiv
  let e := doubledJoinHomeomorph m G
  let f : C(simplicialRealization (universalJoinComplex (m + m) G), G → ℂ) :=
    F.comp ⟨e.symm, e.symm.continuous⟩
  apply hfinite f
  · intro w
    exact hcenter (e.symm w)
  · intro w
    exact hne (e.symm w)
  · intro a w
    change F (e.symm (translateJoinRealization a w)) =
      complexRegularTranslate a (F (e.symm w))
    rw [doubledJoinHomeomorph_symm_equivariant]
    exact hequiv a (e.symm w)


/-- The topological-join no-map theorem also transports back to the finite
doubled join. Thus the two exact obstruction interfaces are equivalent. -/
theorem finiteJoinNoMap_of_complexJoinNoMap
    {m : ℕ} {G : Type*} [AddCommGroup G] [Fintype G]
    (hjoin : ComplexJoinNoMap m G) :
    ComplexFiniteJoinNoMap m G := by
  intro f hcenter hne hequiv
  let e := doubledJoinHomeomorph m G
  let F : C(TopologicalJoin
      (simplicialRealization (universalJoinComplex m G))
      (simplicialRealization (universalJoinComplex m G)), G → ℂ) :=
    f.comp ⟨e, e.continuous⟩
  apply hjoin F
  · intro z
    exact hcenter (e z)
  · intro z
    exact hne (e z)
  · intro a z
    change f (e (topologicalJoinMap
      (translateJoinMap a) (translateJoinMap a) z)) =
        complexRegularTranslate a (f (e z))
    rw [doubledJoinHomeomorph_equivariant]
    exact hequiv a (e z)

/-- The geometric identification equates the two forms of the unresolved
complex no-map theorem. -/
theorem complexFiniteJoinNoMap_iff_complexJoinNoMap
    {m : ℕ} {G : Type*} [AddCommGroup G] [Fintype G] :
    ComplexFiniteJoinNoMap m G ↔ ComplexJoinNoMap m G :=
  ⟨complexJoinNoMap_of_finiteJoinNoMap,
    finiteJoinNoMap_of_complexJoinNoMap⟩

end FairDivision.Topology.Volovikov
