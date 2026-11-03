import FairDivision.Topology.NerveConnectivity.FiniteClosedFamilyPasting
import FairDivision.Topology.NerveConnectivity.PrismBoundary

/-!
# Pasting data on a prism boundary

A map on the side of a prism and maps on its two time ends assemble into
one continuous boundary map when their endpoint values agree. This is a
pure closed-cover theorem; no connectivity assumption enters here.
-/

set_option autoImplicit false

open scoped unitInterval Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- The side and two end faces of the prism over `P`, relative to `A`. -/
abbrev RelativePrismBoundary {P : Type u} [TopologicalSpace P]
    (A : Set P) :=
  {z : P × I // z.1 ∈ A ∨ z.2 = 0 ∨ z.2 = 1}

/-- Closed-cover pasting on the side and two ends of an arbitrary prism. -/
theorem exists_relativePrismBoundary_paste
    {P : Type u} {X : Type v} [TopologicalSpace P] [TopologicalSpace X]
    (A : Set P) (hA : IsClosed A)
    (fSide : C(A × I, X)) (f0 f1 : C(P, X))
    (h0 : ∀ a : A, fSide (a, 0) = f0 a.1)
    (h1 : ∀ a : A, fSide (a, 1) = f1 a.1) :
    ∃ H : C(RelativePrismBoundary A, X),
      (∀ (a : A) (t : I),
        H ⟨(a.1, t), Or.inl a.2⟩ = fSide (a, t)) ∧
      (∀ p : P, H ⟨(p, 0), Or.inr (Or.inl rfl)⟩ = f0 p) ∧
      (∀ p : P, H ⟨(p, 1), Or.inr (Or.inr rfl)⟩ = f1 p) := by
  let S : Set (P × I) := {z | z.1 ∈ A}
  let E : Bool → Set (P × I) := fun b =>
    {z | z.2 = if b then (1 : I) else 0}
  have hS : IsClosed S := hA.preimage continuous_fst
  have hE : ∀ b, IsClosed (E b) := by
    intro b
    exact isClosed_singleton.preimage continuous_snd
  let s : C(S, X) := fSide.comp ⟨fun z => (⟨z.1.1, z.2⟩, z.1.2), by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact continuous_fst.comp continuous_subtype_val
    · exact continuous_snd.comp continuous_subtype_val⟩
  let e : ∀ b, C(E b, X) := fun b => by
    cases b
    · exact f0.comp ⟨fun z => z.1.1,
        continuous_fst.comp continuous_subtype_val⟩
    · exact f1.comp ⟨fun z => z.1.1,
        continuous_fst.comp continuous_subtype_val⟩
  have hcomp : ClosedFamilyCompatible S E Finset.univ s e := by
    constructor
    · intro b _ z hzS hzE
      cases b with
      | false =>
          have ht : z.2 = 0 := hzE
          change fSide (⟨z.1, hzS⟩, z.2) = f0 z.1
          rw [ht]
          exact h0 ⟨z.1, hzS⟩
      | true =>
          have ht : z.2 = 1 := hzE
          change fSide (⟨z.1, hzS⟩, z.2) = f1 z.1
          rw [ht]
          exact h1 ⟨z.1, hzS⟩
    · intro b _ c _ hbc z hzb hzc
      cases b <;> cases c
      · exact False.elim (hbc rfl)
      · have hz0 : z.2 = 0 := hzb
        have hz1 : z.2 = 1 := hzc
        exact False.elim (zero_ne_one (hz0.symm.trans hz1))
      · have hz1 : z.2 = 1 := hzb
        have hz0 : z.2 = 0 := hzc
        exact False.elim (zero_ne_one (hz0.symm.trans hz1))
      · exact False.elim (hbc rfl)
  obtain ⟨Hraw, hHside, hHend⟩ :=
    exists_closedFamilyPaste S E hS hE s e Finset.univ hcomp
  have hset : closedFamilyUnion S E Finset.univ =
      {z : P × I | z.1 ∈ A ∨ z.2 = 0 ∨ z.2 = 1} := by
    ext z
    simp only [mem_closedFamilyUnion_iff, Finset.mem_univ, true_and,
      Set.mem_setOf_eq]
    constructor
    · rintro (hzS | ⟨b, hzE⟩)
      · exact Or.inl hzS
      · cases b with
        | false => exact Or.inr (Or.inl hzE)
        | true => exact Or.inr (Or.inr hzE)
    · rintro (hzS | hz0 | hz1)
      · exact Or.inl hzS
      · exact Or.inr ⟨false, hz0⟩
      · exact Or.inr ⟨true, hz1⟩
  let H : C(RelativePrismBoundary A, X) :=
    Hraw.comp ⟨fun z => ⟨z.1, hset.symm ▸ z.2⟩, by
      apply Continuous.subtype_mk
      exact continuous_subtype_val⟩
  refine ⟨H, ?_, ?_, ?_⟩
  · intro a t
    exact hHside ⟨(a.1, t), a.2⟩
  · intro p
    exact hHend false (Finset.mem_univ false) ⟨(p, 0), rfl⟩
  · intro p
    exact hHend true (Finset.mem_univ true) ⟨(p, 1), rfl⟩

end FairDivision.Topology.NerveConnectivity
