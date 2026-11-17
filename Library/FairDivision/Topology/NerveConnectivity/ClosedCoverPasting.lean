import FairDivision.Topology.NerveConnectivity.ClosedRealization
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Pasting maps on a closed finite-polyhedron cover

The realization of a union of finite subcomplexes is a closed cover by its
two pieces. Compatible continuous maps on the pieces therefore glue to a
continuous map on the union. This is the elementary topological pushout
property needed before any homotopy-excision argument.
-/

set_option autoImplicit false

open scoped Topology

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- Continuous maps on two closed subsets that agree on their overlap paste
to a continuous map on their union. -/
noncomputable def closedCoverPaste
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (A B : Set X) (hA : IsClosed A) (hB : IsClosed B)
    (f : C(A, Y)) (g : C(B, Y))
    (hfg : ∀ (x : X) (hxA : x ∈ A) (hxB : x ∈ B),
      f ⟨x, hxA⟩ = g ⟨x, hxB⟩) : C((A ∪ B : Set X), Y) := by
  classical
  let U : Set X := A ∪ B
  let A' : Set U := {x | x.1 ∈ A}
  let B' : Set U := {x | x.1 ∈ B}
  let h : U → Y := fun x =>
    if hxA : x.1 ∈ A then f ⟨x.1, hxA⟩
    else g ⟨x.1, x.2.resolve_left hxA⟩
  have hA' : IsClosed A' := by
    change IsClosed ((Subtype.val : U → X) ⁻¹' A)
    exact hA.preimage continuous_subtype_val
  have hB' : IsClosed B' := by
    change IsClosed ((Subtype.val : U → X) ⁻¹' B)
    exact hB.preimage continuous_subtype_val
  have hAc : ContinuousOn h A' := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hq : Continuous (fun x : A' => (⟨x.1.1, x.2⟩ : A)) := by
      fun_prop
    have hf : Continuous (fun x : A' => f ⟨x.1.1, x.2⟩) :=
      f.continuous.comp hq
    convert hf using 1
    funext x
    have hxA : x.1.1 ∈ A := x.2
    simp [h, hxA]
  have hBc : ContinuousOn h B' := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hq : Continuous (fun x : B' => (⟨x.1.1, x.2⟩ : B)) := by
      fun_prop
    have hg : Continuous (fun x : B' => g ⟨x.1.1, x.2⟩) :=
      g.continuous.comp hq
    convert hg using 1
    funext x
    dsimp [h]
    split_ifs with hxA
    · exact hfg x.1.1 hxA x.2
    · rfl
  have hunion : A' ∪ B' = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact x.2
  have hc : Continuous h := by
    apply continuousOn_univ.mp
    rw [← hunion]
    exact hAc.union_of_isClosed hBc hA' hB'
  exact ⟨h, hc⟩

/-- The pasted map restricts to the first closed piece. -/
theorem closedCoverPaste_left
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (A B : Set X) (hA : IsClosed A) (hB : IsClosed B)
    (f : C(A, Y)) (g : C(B, Y))
    (hfg : ∀ (x : X) (hxA : x ∈ A) (hxB : x ∈ B),
      f ⟨x, hxA⟩ = g ⟨x, hxB⟩) (x : A) :
    closedCoverPaste A B hA hB f g hfg ⟨x.1, Or.inl x.2⟩ = f x := by
  simp [closedCoverPaste]

/-- The pasted map restricts to the second closed piece. -/
theorem closedCoverPaste_right
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (A B : Set X) (hA : IsClosed A) (hB : IsClosed B)
    (f : C(A, Y)) (g : C(B, Y))
    (hfg : ∀ (x : X) (hxA : x ∈ A) (hxB : x ∈ B),
      f ⟨x, hxA⟩ = g ⟨x, hxB⟩) (x : B) :
    closedCoverPaste A B hA hB f g hfg ⟨x.1, Or.inr x.2⟩ = g x := by
  by_cases hxA : x.1 ∈ A
  · simpa [closedCoverPaste, hxA] using hfg x.1 hxA x.2
  · simp [closedCoverPaste, hxA]

/-- The union of two realized finite subcomplexes has the closed-cover
pasting property. -/
noncomputable def simplicialCoverPaste
    {V : Type v} [Fintype V] {Y : Type u} [TopologicalSpace Y]
    (K L : PreAbstractSimplicialComplex V)
    (f : C(simplicialRealization K, Y))
    (g : C(simplicialRealization L, Y))
    (hfg : ∀ (w : stdSimplex ℝ V)
      (hwK : w ∈ simplicialRealization K)
      (hwL : w ∈ simplicialRealization L),
      f ⟨w, hwK⟩ = g ⟨w, hwL⟩) :
    C(simplicialRealization (K ⊔ L), Y) := by
  rw [simplicialRealization_sup]
  exact closedCoverPaste
    (simplicialRealization K) (simplicialRealization L)
    (simplicialRealization_isClosed K) (simplicialRealization_isClosed L)
    f g hfg

end FairDivision.Topology.NerveConnectivity
