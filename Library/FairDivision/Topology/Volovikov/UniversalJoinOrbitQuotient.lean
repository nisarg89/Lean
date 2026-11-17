import FairDivision.Topology.Volovikov.UniversalJoinRealization
import Mathlib.Topology.Constructions

/-!
# The orbit space of the finite universal join

For the finite-skeleton Euler obstruction, the orbit space of `G^{*m}` is
the finite-stage model of `BG`. This file constructs only its quotient
space and the continuous orbit projection. The Euler class and the
no-equivariant-map theorem remain separate obligations.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity

/-- The orbit relation of diagonal group-label translation on the finite
universal join. -/
def universalJoinRealizationOrbitSetoid
    (m : ℕ) (G : Type*) [AddGroup G] [Fintype G] :
    Setoid (simplicialRealization (universalJoinComplex m G)) where
  r x y := ∃ a : G, translateJoinRealization a x = y
  iseqv := by
    constructor
    · intro x
      exact ⟨0, translateJoinRealization_zero x⟩
    · intro x y hxy
      obtain ⟨a, ha⟩ := hxy
      refine ⟨-a, ?_⟩
      rw [← ha, ← translateJoinRealization_add, neg_add_cancel]
      exact translateJoinRealization_zero x
    · intro x y z hxy hyz
      obtain ⟨a, ha⟩ := hxy
      obtain ⟨b, hb⟩ := hyz
      refine ⟨b + a, ?_⟩
      rw [translateJoinRealization_add, ha, hb]

/-- The topological orbit space of the finite join. -/
abbrev UniversalJoinOrbitSpace
    (m : ℕ) (G : Type*) [AddGroup G] [Fintype G] :=
  Quotient (universalJoinRealizationOrbitSetoid m G)

/-- The continuous quotient projection onto the finite join orbit space. -/
def universalJoinOrbitProjection
    (m : ℕ) (G : Type*) [AddGroup G] [Fintype G] :
    C(simplicialRealization (universalJoinComplex m G),
      UniversalJoinOrbitSpace m G) :=
  ⟨@Quotient.mk' _ (universalJoinRealizationOrbitSetoid m G),
    continuous_quotient_mk'⟩

/-- The orbit projection is unchanged by a group translation. -/
theorem universalJoinOrbitProjection_translate
    {m : ℕ} {G : Type*} [AddGroup G] [Fintype G]
    (a : G)
    (x : simplicialRealization (universalJoinComplex m G)) :
    universalJoinOrbitProjection m G (translateJoinRealization a x) =
      universalJoinOrbitProjection m G x := by
  change Quotient.mk (universalJoinRealizationOrbitSetoid m G)
      (translateJoinRealization a x) =
    Quotient.mk (universalJoinRealizationOrbitSetoid m G) x
  apply Quotient.sound
  refine ⟨-a, ?_⟩
  rw [← translateJoinRealization_add, neg_add_cancel]
  exact translateJoinRealization_zero x

end FairDivision.Topology.Volovikov
