import FairDivision.Topology.NerveConnectivity.NullHomotopy

/-!
# Transporting a nullhomotopy across a source homeomorphism

The finite sphere and its iterated subdivision are related to the
operational cube sphere by homeomorphisms. A nullhomotopy after either
change of source coordinates is a nullhomotopy of the original map.
-/

set_option autoImplicit false

open scoped Topology

namespace FairDivision.Topology.NerveConnectivity

universe u v w

/-- A source homeomorphism can be canceled from a nullhomotopy. -/
theorem homotopic_const_of_comp_homeomorph
    {A : Type u} {B : Type v} {X : Type w}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]
    (e : A ≃ₜ B) (f : C(B, X)) (x : X)
    (h : (f.comp (e : C(A, B))).Homotopic
      (ContinuousMap.const _ x)) :
    f.Homotopic (ContinuousMap.const _ x) := by
  have h' := ContinuousMap.Homotopic.comp h
    (ContinuousMap.Homotopic.refl (e.symm : C(B, A)))
  have heq : (f.comp (e : C(A, B))).comp (e.symm : C(B, A)) = f := by
    ext z
    simp
  simpa only [heq, ContinuousMap.const_comp] using h'

end FairDivision.Topology.NerveConnectivity
