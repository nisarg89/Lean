import FairDivision.Topology.Volovikov.RealComplexJoinMap
import FairDivision.Topology.Volovikov.CenteredCharacterDecomposition

/-!
# Equivariance of the real-to-complex join map

When both real vector maps transform by regular translation, their complex
join transforms by the complex regular representation. This is the action
bridge needed by the finite-join doubling reduction.
-/

set_option autoImplicit false

open scoped unitInterval Topology

namespace FairDivision.Topology.Volovikov

/-- The join formula commutes with regular translation coordinatewise. -/
theorem complexJoinVector_translate
    {G : Type*} [AddCommGroup G]
    (a : G) (t : I) (u v : G → ℝ) :
    complexJoinVector t (fun b => u (b - a)) (fun b => v (b - a)) =
      complexRegularTranslate a (complexJoinVector t u v) := by
  rfl

/-- A pair of equivariant real maps gives an equivariant complex map on
the topological join. -/
theorem realComplexJoinMap_equivariant
    {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [AddCommGroup G]
    (A : G → C(X, X)) (B : G → C(Y, Y))
    (f : C(X, G → ℝ)) (g : C(Y, G → ℝ))
    (hf : ∀ (a : G) (x : X) (b : G), f (A a x) b = f x (b - a))
    (hg : ∀ (a : G) (y : Y) (b : G), g (B a y) b = g y (b - a))
    (a : G) (z : TopologicalJoin X Y) :
    realComplexJoinMap f g (topologicalJoinMap (A a) (B a) z) =
      complexRegularTranslate a (realComplexJoinMap f g z) := by
  induction z using Quotient.inductionOn with
  | _ z =>
      change complexJoinVector z.1 (f (A a z.2.1)) (g (B a z.2.2)) =
        complexRegularTranslate a (complexJoinVector z.1 (f z.2.1) (g z.2.2))
      funext b
      simp [complexJoinVector, complexRegularTranslate, hf, hg]

end FairDivision.Topology.Volovikov
