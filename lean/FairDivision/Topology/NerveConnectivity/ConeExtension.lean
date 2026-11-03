import FairDivision.Topology.NerveConnectivity.NullHomotopy
import Mathlib.Topology.Constructions

/-!
# Cone extensions of sphere maps

A nullhomotopy of a map from a nonempty space `S` is equivalent to a
continuous extension to the topological cone on `S`. This chooses the cone
as the operational disk, so no homeomorphism from a cube to a cone is needed
for relative cell-filling arguments.
-/

set_option autoImplicit false

open scoped unitInterval Topology

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- Identify all points at time one in the cylinder `I × S`. -/
def coneSetoid (S : Type u) : Setoid (I × S) where
  r a b := a = b ∨ (a.1 = 1 ∧ b.1 = 1)
  iseqv := by
    constructor
    · intro a
      exact Or.inl rfl
    · intro a b h
      rcases h with h | ⟨ha, hb⟩
      · exact Or.inl h.symm
      · exact Or.inr ⟨hb, ha⟩
    · intro a b c hab hbc
      rcases hab with hab | ⟨ha, hb⟩
      · subst b
        exact hbc
      rcases hbc with hbc | ⟨hb', hc⟩
      · subst c
        exact Or.inr ⟨ha, hb⟩
      · exact Or.inr ⟨ha, hc⟩

/-- The quotient cylinder with its time-one end collapsed to an apex. -/
abbrev TopologicalCone (S : Type u) := Quot (coneSetoid S)

/-- Embed `S` as the time-zero base of its cone. -/
def coneBase (S : Type u) [TopologicalSpace S] :
    C(S, TopologicalCone S) :=
  ⟨fun s => Quot.mk (coneSetoid S) ((0 : I), s),
    continuous_quot_mk.comp (continuous_const.prodMk continuous_id)⟩

/-- A map is nullhomotopic exactly when it extends to the cone on its domain. -/
theorem homotopic_const_iff_coneExtension
    {S : Type u} {X : Type v} [TopologicalSpace S] [TopologicalSpace X]
    [Nonempty S] (f : C(S, X)) :
    (∃ x : X, f.Homotopic (ContinuousMap.const _ x)) ↔
      ∃ F : C(TopologicalCone S, X), F.comp (coneBase S) = f := by
  constructor
  · rintro ⟨x, ⟨H⟩⟩
    have hrel : ∀ a b : I × S, coneSetoid S a b → H a = H b := by
      intro a b hab
      rcases hab with rfl | ⟨ha, hb⟩
      · rfl
      · have haa : a = ((1 : I), a.2) := Prod.ext ha rfl
        have hbb : b = ((1 : I), b.2) := Prod.ext hb rfl
        rw [haa, hbb]
        exact (H.map_one_left a.2).trans (H.map_one_left b.2).symm
    let F : C(TopologicalCone S, X) :=
      ⟨Quot.lift H hrel, continuous_quot_lift hrel H.toContinuousMap.continuous⟩
    refine ⟨F, ?_⟩
    ext s
    change H ((0 : I), s) = f s
    exact H.map_zero_left s
  · rintro ⟨F, hF⟩
    let s₀ : S := Classical.choice inferInstance
    let x : X := F (Quot.mk (coneSetoid S) ((1 : I), s₀))
    refine ⟨x, ⟨{
      toContinuousMap := F.comp ⟨Quot.mk (coneSetoid S), continuous_quot_mk⟩
      map_zero_left := ?_
      map_one_left := ?_
    }⟩⟩
    · intro s
      have hs := congrArg (fun g : C(S, X) => g s) hF
      simpa [coneBase] using hs
    · intro s
      have hs : Quot.mk (coneSetoid S) ((1 : I), s) =
          (Quot.mk (coneSetoid S) ((1 : I), s₀) : TopologicalCone S) :=
        Quot.sound (Or.inr ⟨rfl, rfl⟩)
      exact congrArg F hs

end FairDivision.Topology.NerveConnectivity
