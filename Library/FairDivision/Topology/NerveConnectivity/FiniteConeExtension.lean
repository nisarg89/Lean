import FairDivision.Topology.NerveConnectivity.FiniteConeContraction
import FairDivision.Topology.NerveConnectivity.FiniteCellExtension

/-!
# Extending a finite-complex map over its cone

When a target is null-connected through degree `k`, every map from a
finite complex with at most `k+1` vertices per face extends over its
simplicial cone. The resulting map gives a nullhomotopy on the base.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- A map from a sufficiently low-dimensional finite complex extends
across the simplicial cone. -/
theorem exists_finiteCone_mapExtension
    {V : Type u} [Fintype V] [Nonempty V]
    {X : Type v} [TopologicalSpace X]
    (K : PreAbstractSimplicialComplex V) (k : ℕ)
    (hKdim : ∀ F : Finset V, F ∈ K → F.card ≤ k + 1)
    (hX : NullConnectedSpace k X)
    (f : C(simplicialRealization K, X)) :
    ∃ g : C(simplicialRealization (finiteConeComplex K), X),
      ∀ w : simplicialRealization K,
        g (finiteConeBaseMap K w) = f w := by
  let e := finiteConeBaseRealizationHomeomorph K
  let fBase : C(simplicialRealization (finiteConeBaseComplex K), X) :=
    f.comp (e.symm : C(simplicialRealization (finiteConeBaseComplex K),
      simplicialRealization K))
  have hConeDim : ∀ S : Finset (Option V),
      S ∈ finiteConeComplex K → S.card ≤ k + 2 := by
    intro S hS
    have h := finiteConeComplex_card_le K (k + 1) hKdim S hS
    omega
  obtain ⟨g, hg⟩ := exists_finiteComplex_mapExtension
    (finiteConeComplex K) k hConeDim hX
    (finiteConeBaseComplex K) (finiteConeBaseComplex_le K) fBase
  refine ⟨g, ?_⟩
  intro w
  change g ((finiteConeBaseInclusion K) (e w)) = f w
  have h := hg (e w)
  change g ((finiteConeBaseInclusion K) (e w)) = fBase (e w) at h
  exact h.trans (by simp [fBase])

/-- Maps from a low-dimensional finite complex into a connected target
are nullhomotopic, via the explicit finite cone extension. -/
theorem finiteComplex_map_nullhomotopic_of_dimension
    {V : Type u} [Fintype V] [Nonempty V]
    {X : Type v} [TopologicalSpace X]
    (K : PreAbstractSimplicialComplex V) (k : ℕ)
    (hKdim : ∀ F : Finset V, F ∈ K → F.card ≤ k + 1)
    (hX : NullConnectedSpace k X)
    (f : C(simplicialRealization K, X)) :
    ∃ x : X, f.Homotopic (ContinuousMap.const _ x) := by
  obtain ⟨g, hg⟩ := exists_finiteCone_mapExtension K k hKdim hX f
  refine ⟨g (finiteConeApex K), ?_⟩
  have h := finiteConeMap_base_nullhomotopic K g
  have hfg : g.comp (finiteConeBaseMap K) = f := by
    ext w
    exact hg w
  simpa [hfg] using h

end FairDivision.Topology.NerveConnectivity
