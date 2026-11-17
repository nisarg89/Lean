import FairDivision.Topology.NerveConnectivity.FiniteClosedFamilyPasting

/-! # A finite closed cover as a continuous-map pasting problem

A thin use of the existing closed-family pasting proof, with an empty base.
This is useful for the literal equal subintervals and one-dimensional faces
in the manuscript's virtual-score construction.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology

open NerveConnectivity

/-- Paste continuous maps on a finite closed cover, preserving every literal
restriction. The existing finite-family proof supplies all continuity. -/
theorem exists_finiteClosedCoverMap
    {ι X Y : Type*} [Fintype ι] [TopologicalSpace X] [TopologicalSpace Y]
    (piece : ι → Set X) (closed : ∀ i, IsClosed (piece i))
    (cover : ∀ x, ∃ i, x ∈ piece i)
    (f : ∀ i, C(piece i, Y))
    (compatible : ∀ i j x (hi : x ∈ piece i) (hj : x ∈ piece j),
      f i ⟨x, hi⟩ = f j ⟨x, hj⟩) :
    ∃ F : C(X, Y), ∀ i x (hi : x ∈ piece i), F x = f i ⟨x, hi⟩ := by
  classical
  let emptyMap : C((∅ : Set X), Y) := {
    toFun := fun x => False.elim x.2
    continuous_toFun := by
      rw [continuous_iff_isClosed]
      intro s _
      have he : (fun x : (∅ : Set X) => (False.elim x.2 : Y)) ⁻¹' s = ∅ := by
        ext x
        exact False.elim x.2
      rw [he]
      exact isClosed_empty }
  have hcompat : ClosedFamilyCompatible ∅ piece Finset.univ emptyMap f := by
    constructor
    · intro i _ x hx _
      exact False.elim hx
    · intro i _ j _ _ x hi hj
      exact compatible i j x hi hj
  obtain ⟨F, hbase, hpiece⟩ :=
    exists_closedFamilyPaste ∅ piece isClosed_empty closed emptyMap f Finset.univ hcompat
  have hUnion : ∀ x : X, x ∈ closedFamilyUnion ∅ piece Finset.univ := by
    intro x
    obtain ⟨i, hi⟩ := cover x
    exact (mem_closedFamilyUnion_iff _ _ _ _).2
      (Or.inr ⟨i, Finset.mem_univ i, hi⟩)
  let inclusion : C(X, closedFamilyUnion ∅ piece Finset.univ) := {
    toFun := fun x => ⟨x, hUnion x⟩
    continuous_toFun := continuous_id.subtype_mk hUnion }
  refine ⟨F.comp inclusion, ?_⟩
  intro i x hi
  exact hpiece i (Finset.mem_univ i) ⟨x, hi⟩

end FairDivision.Topology
