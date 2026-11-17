import FairDivision.Topology.NerveConnectivity.FiniteSimplexRelativeOpenSubordination

/-!
# Subcomplex cover induced by a subordinate source subdivision

For an open cover of a finite realization, classify each face by the cover
members containing the image of every realized point supported on it.
This condition is inherited by nonempty subfaces. After a sufficiently
fine barycentric subdivision, the resulting subcomplexes cover every face.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- Faces whose entire realized simplex maps into a selected open set of
the original realization. -/
noncomputable def subordinateSourceComplex
    {V : Type u} [Fintype V]
    (K : PreAbstractSimplicialComplex V) (n : ℕ)
    (U : Set (simplicialRealization K)) :
    PreAbstractSimplicialComplex (iteratedBarycentricVertex V n) where
  faces := {F | F ∈ iteratedBarycentricComplex K n ∧
    ∀ z : simplicialRealization (iteratedBarycentricComplex K n),
      FairDivision.Topology.finiteSimplexSupport z.1 ⊆ F →
        iteratedBarycentricRealizationHomeomorph K n z ∈ U}
  isRelLowerSet_faces := by
    intro F hF
    constructor
    · exact ((iteratedBarycentricComplex K n).isRelLowerSet_faces hF.1).1
    · intro G hGF hGn
      refine ⟨((iteratedBarycentricComplex K n).isRelLowerSet_faces hF.1).2
        hGF hGn, ?_⟩
      intro z hz
      exact hF.2 z (hz.trans hGF)

/-- Each subordinate source complex lies inside the subdivision. -/
theorem subordinateSourceComplex_le
    {V : Type u} [Fintype V]
    (K : PreAbstractSimplicialComplex V) (n : ℕ)
    (U : Set (simplicialRealization K)) :
    subordinateSourceComplex K n U ≤ iteratedBarycentricComplex K n :=
  fun _ hF => hF.1

/-- A relatively open cover becomes a face-cover by subordinate
subcomplexes after one common subdivision depth. -/
theorem exists_subordinateSourceComplex_cover
    {V : Type u} {ι : Type v} [Fintype V]
    (K : PreAbstractSimplicialComplex V)
    (U : ι → Set (simplicialRealization K))
    (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ w : simplicialRealization K, ∃ i, w ∈ U i) :
    ∃ n : ℕ, ∀ F : Finset (iteratedBarycentricVertex V n),
      F ∈ iteratedBarycentricComplex K n →
      ∃ i, F ∈ subordinateSourceComplex K n (U i) := by
  obtain ⟨n, hn⟩ :=
    exists_finiteSimplexSubdivision_subordinate_relativeOpenCover K U hU hcover
  refine ⟨n, ?_⟩
  intro F hF
  obtain ⟨i, hi⟩ := hn F hF
  exact ⟨i, ⟨hF, hi⟩⟩

/-- Package the subordinate source pieces in the finite-subcomplex-cover
interface used by the connectivity induction. -/
theorem exists_subordinateFiniteSubcomplexCover
    {V : Type u} {ι : Type v} [Fintype V] [Fintype ι]
    (K : PreAbstractSimplicialComplex V)
    (U : ι → Set (simplicialRealization K))
    (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ w : simplicialRealization K, ∃ i, w ∈ U i) :
    ∃ n : ℕ, ∃ C : FiniteSubcomplexCover ι
      (iteratedBarycentricVertex V n),
      C.ambient = iteratedBarycentricComplex K n ∧
      ∀ i, C.pieces i = subordinateSourceComplex K n (U i) := by
  obtain ⟨n, hn⟩ := exists_subordinateSourceComplex_cover K U hU hcover
  refine ⟨n, {
    ambient := iteratedBarycentricComplex K n
    pieces := fun i => subordinateSourceComplex K n (U i)
    piece_le := fun i => subordinateSourceComplex_le K n (U i)
    covers := fun F hF => hn F hF
  }, rfl, ?_⟩
  intro i
  rfl

end FairDivision.Topology.NerveConnectivity
