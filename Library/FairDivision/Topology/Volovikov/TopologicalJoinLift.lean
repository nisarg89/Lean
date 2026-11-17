import FairDivision.Topology.Volovikov.TopologicalJoin

/-!
# Descent from the cylinder to a topological join

A continuous cylinder map descends when its value at time zero ignores the
second factor and its value at time one ignores the first factor.
-/

set_option autoImplicit false

open scoped unitInterval Topology

namespace FairDivision.Topology.Volovikov

/-- The quotient universal property in the form used for join maps. -/
def topologicalJoinLift
    {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (h : C(I × (X × Y), Z))
    (h0 : ∀ (x : X) (y y' : Y), h ((0 : I), (x, y)) = h (0, (x, y')))
    (h1 : ∀ (x x' : X) (y : Y), h ((1 : I), (x, y)) = h (1, (x', y))) :
    C(TopologicalJoin X Y, Z) := by
  have hrel : ∀ a b : I × (X × Y),
      (topologicalJoinSetoid X Y).r a b → h a = h b := by
    rintro ⟨ta, xa, ya⟩ ⟨tb, xb, yb⟩ hab
    change topologicalJoinKey (ta, (xa, ya)) =
      topologicalJoinKey (tb, (xb, yb)) at hab
    have ht : ta = tb := congrArg Prod.fst hab
    subst tb
    by_cases ht0 : ta = (0 : I)
    · have hx : xa = xb := by
        have hopt := congrArg
          (fun z : I × (Option X × Option Y) => z.2.1) hab
        simpa [topologicalJoinKey, ht0] using hopt
      subst xb
      simpa [ht0] using h0 xa ya yb
    by_cases ht1 : ta = (1 : I)
    · have hy : ya = yb := by
        have hopt := congrArg
          (fun z : I × (Option X × Option Y) => z.2.2) hab
        simpa [topologicalJoinKey, ht1] using hopt
      subst yb
      simpa [ht1] using h1 xa xb ya
    have hx : xa = xb := by
      have hopt := congrArg
        (fun z : I × (Option X × Option Y) => z.2.1) hab
      simpa [topologicalJoinKey, ht1] using hopt
    have hy : ya = yb := by
      have hopt := congrArg
        (fun z : I × (Option X × Option Y) => z.2.2) hab
      simpa [topologicalJoinKey, ht0] using hopt
    subst xb
    subst yb
    rfl
  exact ⟨Quotient.lift h hrel, h.continuous.quotient_lift hrel⟩

@[simp] theorem topologicalJoinLift_projection
    {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (h : C(I × (X × Y), Z))
    (h0 : ∀ (x : X) (y y' : Y), h ((0 : I), (x, y)) = h (0, (x, y')))
    (h1 : ∀ (x x' : X) (y : Y), h ((1 : I), (x, y)) = h (1, (x', y)))
    (z : I × (X × Y)) :
    topologicalJoinLift h h0 h1 (topologicalJoinProjection X Y z) = h z := rfl

end FairDivision.Topology.Volovikov
