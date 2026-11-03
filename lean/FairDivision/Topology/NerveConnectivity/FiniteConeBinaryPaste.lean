import FairDivision.Topology.NerveConnectivity.FiniteConeIntersection
import FairDivision.Topology.NerveConnectivity.SimplicialCoverPasteRestrictions

/-!
# Pasting maps on two finite simplicial cones

Coning preserves binary unions. Thus compatible continuous maps on
two subcones paste to one map on the cone of their union, retaining
both exact restriction equations.
-/

set_option autoImplicit false

open scoped Topology

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- Paste compatible maps on the cones of two finite subcomplexes. -/
noncomputable def finiteConeBinaryPaste
    {V : Type u} [Fintype V]
    {X : Type v} [TopologicalSpace X]
    (A B : PreAbstractSimplicialComplex V)
    (f : C(simplicialRealization (finiteConeComplex A), X))
    (g : C(simplicialRealization (finiteConeComplex B), X))
    (hfg : ∀ (w : stdSimplex ℝ (Option V))
      (hwA : w ∈ simplicialRealization (finiteConeComplex A))
      (hwB : w ∈ simplicialRealization (finiteConeComplex B)),
      f ⟨w, hwA⟩ = g ⟨w, hwB⟩) :
    C(simplicialRealization (finiteConeComplex (A ⊔ B)), X) := by
  let q := simplicialCoverPasteExact (finiteConeComplex A)
    (finiteConeComplex B) f g hfg
  have hEq := finiteConeComplex_sup A B
  exact q.comp (ContinuousMap.inclusion
    (simplicialRealization_mono (le_of_eq hEq)))

/-- The pasted cone map restricts exactly to the first prescribed map. -/
theorem finiteConeBinaryPaste_left
    {V : Type u} [Fintype V]
    {X : Type v} [TopologicalSpace X]
    (A B : PreAbstractSimplicialComplex V)
    (f : C(simplicialRealization (finiteConeComplex A), X))
    (g : C(simplicialRealization (finiteConeComplex B), X))
    (hfg : ∀ (w : stdSimplex ℝ (Option V))
      (hwA : w ∈ simplicialRealization (finiteConeComplex A))
      (hwB : w ∈ simplicialRealization (finiteConeComplex B)),
      f ⟨w, hwA⟩ = g ⟨w, hwB⟩)
    (w : simplicialRealization (finiteConeComplex A)) :
    finiteConeBinaryPaste A B f g hfg
      ⟨w.1, (simplicialRealization_mono
        (finiteConeComplex_mono le_sup_left)) w.2⟩ = f w := by
  unfold finiteConeBinaryPaste
  exact simplicialCoverPaste_left
    (finiteConeComplex A) (finiteConeComplex B) f g hfg w

/-- The pasted cone map restricts exactly to the second prescribed map. -/
theorem finiteConeBinaryPaste_right
    {V : Type u} [Fintype V]
    {X : Type v} [TopologicalSpace X]
    (A B : PreAbstractSimplicialComplex V)
    (f : C(simplicialRealization (finiteConeComplex A), X))
    (g : C(simplicialRealization (finiteConeComplex B), X))
    (hfg : ∀ (w : stdSimplex ℝ (Option V))
      (hwA : w ∈ simplicialRealization (finiteConeComplex A))
      (hwB : w ∈ simplicialRealization (finiteConeComplex B)),
      f ⟨w, hwA⟩ = g ⟨w, hwB⟩)
    (w : simplicialRealization (finiteConeComplex B)) :
    finiteConeBinaryPaste A B f g hfg
      ⟨w.1, (simplicialRealization_mono
        (finiteConeComplex_mono le_sup_right)) w.2⟩ = g w := by
  unfold finiteConeBinaryPaste
  exact simplicialCoverPaste_right
    (finiteConeComplex A) (finiteConeComplex B) f g hfg w

end FairDivision.Topology.NerveConnectivity
