import Mathlib.Topology.Constructions
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.ContinuousMap.Basic

/-!
# A topological join quotient

At time zero the second factor is collapsed, and at time one the first
factor is collapsed. The quotient supports a continuous map induced by a
pair of continuous maps. This is the generic geometric input to doubling a
finite-join sphere map.
-/

set_option autoImplicit false

open scoped unitInterval Topology

namespace FairDivision.Topology.Volovikov

/-- Coordinates that record exactly the points not collapsed at the two
ends of the join parameter. -/
noncomputable def topologicalJoinKey {X Y : Type*} (z : I × (X × Y)) :
    I × (Option X × Option Y) :=
  (z.1, (if z.1 = 1 then none else some z.2.1,
    if z.1 = 0 then none else some z.2.2))

/-- The equivalence relation defining the topological join. -/
def topologicalJoinSetoid (X Y : Type*) : Setoid (I × (X × Y)) where
  r a b := topologicalJoinKey a = topologicalJoinKey b
  iseqv := by
    constructor
    · intro a; rfl
    · intro a b h; exact h.symm
    · intro a b c hab hbc; exact hab.trans hbc

/-- The quotient model of the topological join of two spaces. -/
abbrev TopologicalJoin (X Y : Type*) :=
  Quotient (topologicalJoinSetoid X Y)

/-- The canonical cylinder-to-join map. -/
def topologicalJoinProjection
    (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :
    C(I × (X × Y), TopologicalJoin X Y) :=
  ⟨@Quotient.mk' _ (topologicalJoinSetoid X Y),
    continuous_quotient_mk'⟩

/-- Continuous maps of both factors induce a continuous map of joins. -/
def topologicalJoinMap
    {X Y X' Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) :
    C(TopologicalJoin X Y, TopologicalJoin X' Y') := by
  let h : I × (X × Y) → I × (X' × Y') :=
    fun z => (z.1, (f z.2.1, g z.2.2))
  have hkey (z : I × (X × Y)) :
      topologicalJoinKey (h z) =
        ((topologicalJoinKey z).1,
          (Option.map f (topologicalJoinKey z).2.1,
            Option.map g (topologicalJoinKey z).2.2)) := by
    by_cases h1 : z.1 = 1 <;> by_cases h0 : z.1 = 0 <;>
      simp [topologicalJoinKey, h, h1, h0]
  have hrel : ∀ a b : I × (X × Y),
      (topologicalJoinSetoid X Y).r a b →
      (topologicalJoinSetoid X' Y').r (h a) (h b) := by
    intro a b hab
    change topologicalJoinKey (h a) = topologicalJoinKey (h b)
    rw [hkey, hkey]
    exact congrArg
      (fun z : I × (Option X × Option Y) =>
        (z.1, (Option.map f z.2.1, Option.map g z.2.2))) hab
  have hc : Continuous h := by
    dsimp [h]
    fun_prop
  exact ⟨Quot.map h hrel, continuous_quot_map hrel hc⟩

end FairDivision.Topology.Volovikov
