import FairDivision.Topology.NerveConnectivity.ClosedCoverPasting

/-!
# Restriction equations for finite simplicial closed-cover pasting

The explicit map into the union avoids a dependent cast introduced by
rewriting the equality between the realization of a supremum and the
union of realizations. It retains exact restriction equations.
-/

set_option autoImplicit false

open scoped Topology

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- Binary simplicial pasting with an explicit inclusion into the union. -/
noncomputable def simplicialCoverPasteExact
    {V : Type v} [Fintype V] {Y : Type u} [TopologicalSpace Y]
    (K L : PreAbstractSimplicialComplex V)
    (f : C(simplicialRealization K, Y))
    (g : C(simplicialRealization L, Y))
    (hfg : ∀ (w : stdSimplex ℝ V)
      (hwK : w ∈ simplicialRealization K)
      (hwL : w ∈ simplicialRealization L),
      f ⟨w, hwK⟩ = g ⟨w, hwL⟩) :
    C(simplicialRealization (K ⊔ L), Y) := by
  have hsub : simplicialRealization (K ⊔ L) ⊆
      simplicialRealization K ∪ simplicialRealization L := by
    rw [simplicialRealization_sup]
  exact (closedCoverPaste
    (simplicialRealization K) (simplicialRealization L)
    (simplicialRealization_isClosed K) (simplicialRealization_isClosed L)
    f g hfg).comp (ContinuousMap.inclusion hsub)

/-- The explicit pasted map restricts to the left map. -/
theorem simplicialCoverPaste_left
    {V : Type v} [Fintype V] {Y : Type u} [TopologicalSpace Y]
    (K L : PreAbstractSimplicialComplex V)
    (f : C(simplicialRealization K, Y))
    (g : C(simplicialRealization L, Y))
    (hfg : ∀ (w : stdSimplex ℝ V)
      (hwK : w ∈ simplicialRealization K)
      (hwL : w ∈ simplicialRealization L),
      f ⟨w, hwK⟩ = g ⟨w, hwL⟩)
    (w : simplicialRealization K) :
    simplicialCoverPasteExact K L f g hfg
      ⟨w.1, (simplicialRealization_mono le_sup_left) w.2⟩ = f w := by
  unfold simplicialCoverPasteExact
  exact closedCoverPaste_left
    (simplicialRealization K) (simplicialRealization L)
    (simplicialRealization_isClosed K) (simplicialRealization_isClosed L)
    f g hfg w

/-- The explicit pasted map restricts to the right map. -/
theorem simplicialCoverPaste_right
    {V : Type v} [Fintype V] {Y : Type u} [TopologicalSpace Y]
    (K L : PreAbstractSimplicialComplex V)
    (f : C(simplicialRealization K, Y))
    (g : C(simplicialRealization L, Y))
    (hfg : ∀ (w : stdSimplex ℝ V)
      (hwK : w ∈ simplicialRealization K)
      (hwL : w ∈ simplicialRealization L),
      f ⟨w, hwK⟩ = g ⟨w, hwL⟩)
    (w : simplicialRealization L) :
    simplicialCoverPasteExact K L f g hfg
      ⟨w.1, (simplicialRealization_mono le_sup_right) w.2⟩ = g w := by
  unfold simplicialCoverPasteExact
  exact closedCoverPaste_right
    (simplicialRealization K) (simplicialRealization L)
    (simplicialRealization_isClosed K) (simplicialRealization_isClosed L)
    f g hfg w

end FairDivision.Topology.NerveConnectivity
