import FairDivision.Topology.Volovikov.RealComplexJoinReduction
import FairDivision.Topology.Volovikov.ReducedSphere
import FairDivision.Topology.RegularTranslation

/-!
# From the complex join obstruction to the reduced-sphere obstruction

This converts a map into the concrete reduced sphere used by the BF score
statement into a centered real map on the finite universal join. The central
`ComplexJoinNoMap` premise remains explicit.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity
open FairDivision.Topology

theorem regularPositionPerm_symm_eq
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (e : Fin n ≃ G) (a : G) :
    (regularPositionPerm e a).symm = regularPositionPerm e (-a) := by
  apply Equiv.ext
  intro i
  apply (regularPositionPerm e a).injective
  simp [regularPositionPerm_apply]

theorem regularPositionPerm_symm_index
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (e : Fin n ≃ G) (a b : G) :
    (regularPositionPerm e a).symm (e.symm b) = e.symm (b - a) := by
  rw [regularPositionPerm_symm_eq]
  apply e.injective
  simp [regularPositionPerm_apply, sub_eq_add_neg, add_comm]

/-- A complex no-map theorem rules out any equivariant map from the finite
universal join into the concrete reduced regular sphere. -/
theorem no_reducedSphere_joinMap_of_complexJoinNoMap
    {n : ℕ} {G : Type*} [AddCommGroup G] [Fintype G]
    (e : Fin n ≃ G)
    (hcomplex : ComplexJoinNoMap n G)
    (F : C(simplicialRealization (universalJoinComplex n G), ReducedSphere n))
    (hF : ∀ (a : G)
      (x : simplicialRealization (universalJoinComplex n G)),
      F (translateJoinRealization a x) =
        relabelReducedSphere (regularPositionPerm e a) (F x)) :
    False := by
  let f : C(simplicialRealization (universalJoinComplex n G), G → ℝ) :=
    ⟨fun x g => (F x).1 (e.symm g), by
      apply continuous_pi
      intro g
      exact (continuous_apply (e.symm g)).comp
        (continuous_subtype_val.comp F.continuous)⟩
  have hcenter : ∀ x, ∑ g : G, f x g = 0 := by
    intro x
    change (∑ g : G, (F x).1 (e.symm g)) = 0
    exact (e.symm.sum_comp (F x).1).trans (F x).2.1
  have hne : ∀ x, f x ≠ 0 := by
    intro x hx
    have hzero : (F x).1 = 0 := by
      funext i
      have hi := congrFun hx (e i)
      simpa [f] using hi
    have hsq : (∑ i : Fin n, ((F x).1 i) ^ 2) = 0 := by
      simp [hzero]
    exact one_ne_zero ((F x).2.2.symm.trans hsq)
  have hequiv : ∀ (a : G)
      (x : simplicialRealization (universalJoinComplex n G))
      (g : G), f (translateJoinRealization a x) g = f x (g - a) := by
    intro a x g
    change (F (translateJoinRealization a x)).1 (e.symm g) =
      (F x).1 (e.symm (g - a))
    rw [hF a x]
    exact congrArg (F x).1 (regularPositionPerm_symm_index e a g)
  exact realJoin_noMap_of_complexJoin_noMap hcomplex f hcenter hne hequiv

end FairDivision.Topology.Volovikov
