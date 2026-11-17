import FairDivision.Topology.NerveConnectivity.FiniteFacePrismFilling
import FairDivision.Topology.NerveConnectivity.ClosedCoverPasting

/-!
# Pasting homotopies on finite subcomplex prisms

A finite simplicial realization is closed. Hence continuous maps on two
subcomplexes crossed with the unit interval paste to the prism over their
union, provided they agree on the overlap at every time.
-/

set_option autoImplicit false

open scoped unitInterval Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- Paste maps on two finite subcomplex prisms. -/
noncomputable def simplicialPrismPaste
    {V : Type v} [Fintype V] {Y : Type u} [TopologicalSpace Y]
    (K L : PreAbstractSimplicialComplex V)
    (f : C(simplicialRealization K × I, Y))
    (g : C(simplicialRealization L × I, Y))
    (hfg : ∀ (w : stdSimplex ℝ V) (t : I)
      (hwK : w ∈ simplicialRealization K)
      (hwL : w ∈ simplicialRealization L),
      f (⟨w, hwK⟩, t) = g (⟨w, hwL⟩, t)) :
    C(simplicialRealization (K ⊔ L) × I, Y) := by
  let A : Set (stdSimplex ℝ V × I) :=
    {z | z.1 ∈ simplicialRealization K}
  let B : Set (stdSimplex ℝ V × I) :=
    {z | z.1 ∈ simplicialRealization L}
  have hA : IsClosed A :=
    (simplicialRealization_isClosed K).preimage continuous_fst
  have hB : IsClosed B :=
    (simplicialRealization_isClosed L).preimage continuous_fst
  let f' : C(A, Y) := ⟨fun z => f (⟨z.1.1, z.2⟩, z.1.2), by
    apply f.continuous.comp
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact continuous_fst.comp continuous_subtype_val
    · exact continuous_snd.comp continuous_subtype_val⟩
  let g' : C(B, Y) := ⟨fun z => g (⟨z.1.1, z.2⟩, z.1.2), by
    apply g.continuous.comp
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact continuous_fst.comp continuous_subtype_val
    · exact continuous_snd.comp continuous_subtype_val⟩
  have hfg' : ∀ (z : stdSimplex ℝ V × I) (hzA : z ∈ A) (hzB : z ∈ B),
      f' ⟨z, hzA⟩ = g' ⟨z, hzB⟩ := by
    intro z hzA hzB
    exact hfg z.1 z.2 hzA hzB
  let e : C(simplicialRealization (K ⊔ L) × I, (A ∪ B : Set _)) :=
    ⟨fun z => ⟨(z.1.1, z.2), by
      have hz : z.1.1 ∈ simplicialRealization K ∪ simplicialRealization L := by
        simpa only [simplicialRealization_sup] using z.1.2
      exact hz⟩, by
      apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd⟩
  exact (closedCoverPaste A B hA hB f' g' hfg').comp e

/-- The prism paste agrees with its first input at every time. -/
theorem simplicialPrismPaste_left
    {V : Type v} [Fintype V] {Y : Type u} [TopologicalSpace Y]
    (K L : PreAbstractSimplicialComplex V)
    (f : C(simplicialRealization K × I, Y))
    (g : C(simplicialRealization L × I, Y))
    (hfg : ∀ (w : stdSimplex ℝ V) (t : I)
      (hwK : w ∈ simplicialRealization K)
      (hwL : w ∈ simplicialRealization L),
      f (⟨w, hwK⟩, t) = g (⟨w, hwL⟩, t))
    (w : simplicialRealization K) (t : I) :
    simplicialPrismPaste K L f g hfg
      (⟨w.1, simplicialRealization_mono le_sup_left w.2⟩, t) =
      f (w, t) := by
  simp [simplicialPrismPaste, closedCoverPaste]

/-- The prism paste agrees with its second input at every time. -/
theorem simplicialPrismPaste_right
    {V : Type v} [Fintype V] {Y : Type u} [TopologicalSpace Y]
    (K L : PreAbstractSimplicialComplex V)
    (f : C(simplicialRealization K × I, Y))
    (g : C(simplicialRealization L × I, Y))
    (hfg : ∀ (w : stdSimplex ℝ V) (t : I)
      (hwK : w ∈ simplicialRealization K)
      (hwL : w ∈ simplicialRealization L),
      f (⟨w, hwK⟩, t) = g (⟨w, hwL⟩, t))
    (w : simplicialRealization L) (t : I) :
    simplicialPrismPaste K L f g hfg
      (⟨w.1, simplicialRealization_mono le_sup_right w.2⟩, t) =
      g (w, t) := by
  by_cases hwK : w.1 ∈ simplicialRealization K
  · simpa [simplicialPrismPaste, closedCoverPaste, hwK] using
      hfg w.1 t hwK w.2
  · simp [simplicialPrismPaste, closedCoverPaste, hwK]

end FairDivision.Topology.NerveConnectivity
