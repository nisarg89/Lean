import FairDivision.Topology.Volovikov.TopologicalJoinLift
import FairDivision.Topology.Volovikov.RealComplexJoinAlgebra

/-!
# A zero-free complex map on a topological join

The real and imaginary copies of a nonvanishing real-valued vector map
combine into a nonvanishing complex-valued map on the join. This is the
analytic part of the real-to-complex doubling reduction.
-/

set_option autoImplicit false

open scoped unitInterval Topology

namespace FairDivision.Topology.Volovikov

/-- The cylinder formula before descent through the endpoint quotient. -/
def realComplexJoinCylinder
    {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, G → ℝ)) (g : C(Y, G → ℝ)) :
    C(I × (X × Y), G → ℂ) := by
  refine ⟨fun z => complexJoinVector z.1 (f z.2.1) (g z.2.2), ?_⟩
  apply continuous_pi
  intro a
  have ht : Continuous (fun z : I × (X × Y) => (z.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hf : Continuous (fun z : I × (X × Y) => f z.2.1 a) :=
    (continuous_apply a).comp (f.continuous.comp (continuous_fst.comp continuous_snd))
  have hg : Continuous (fun z : I × (X × Y) => g z.2.2 a) :=
    (continuous_apply a).comp (g.continuous.comp (continuous_snd.comp continuous_snd))
  have hleft : Continuous (fun z : I × (X × Y) =>
      (((1 - (z.1 : ℝ)) * f z.2.1 a : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_const.sub ht).mul hf)
  have hright : Continuous (fun z : I × (X × Y) =>
      (((z.1 : ℝ) * g z.2.2 a : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (ht.mul hg)
  convert hleft.add (continuous_const.mul hright) using 1
  funext z
  rfl

/-- The cylinder formula descends because each endpoint forgets the
appropriate factor. -/
noncomputable def realComplexJoinMap
    {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, G → ℝ)) (g : C(Y, G → ℝ)) :
    C(TopologicalJoin X Y, G → ℂ) :=
  topologicalJoinLift (realComplexJoinCylinder f g)
    (by intro x y y'; simp [realComplexJoinCylinder])
    (by intro x x' y; simp [realComplexJoinCylinder])

/-- A zero-free real map on each factor gives a zero-free complex map on
their join. -/
theorem realComplexJoinMap_ne_zero
    {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, G → ℝ)) (g : C(Y, G → ℝ))
    (hf : ∀ x, f x ≠ 0) (hg : ∀ y, g y ≠ 0)
    (z : TopologicalJoin X Y) :
    realComplexJoinMap f g z ≠ 0 := by
  induction z using Quotient.inductionOn with
  | _ z =>
      change complexJoinVector z.1 (f z.2.1) (g z.2.2) ≠ 0
      exact complexJoinVector_ne_zero z.1 (f z.2.1) (g z.2.2) (hf z.2.1) (hg z.2.2)

/-- The join map preserves the centered regular representation. -/
theorem realComplexJoinMap_sum_zero
    {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Fintype G]
    (f : C(X, G → ℝ)) (g : C(Y, G → ℝ))
    (hf : ∀ x, ∑ a, f x a = 0) (hg : ∀ y, ∑ a, g y a = 0)
    (z : TopologicalJoin X Y) :
    ∑ a, realComplexJoinMap f g z a = 0 := by
  induction z using Quotient.inductionOn with
  | _ z =>
      change ∑ a, complexJoinVector z.1 (f z.2.1) (g z.2.2) a = 0
      exact complexJoinVector_sum_zero z.1 (f z.2.1) (g z.2.2) (hf z.2.1) (hg z.2.2)

end FairDivision.Topology.Volovikov
