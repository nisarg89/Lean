import FairDivision.Topology.Volovikov.InvariantComplexAction

/-!
# Intersections of translated top-dimensional join cells

Different translates of a nonempty join face have distinct vertex sets.
When their common cardinality is `d + 1`, every point in their full cells'
intersection lies in the old `d`-vertex skeleton. This is the overlap fact
needed to paste equivariant fillings over an entire free face orbit.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity
open scoped Classical

/-- Two distinct group elements give distinct translates of a nonempty join
face. -/
theorem translateJoinFace_ne_of_ne {m : ℕ} {G : Type*}
    [AddGroup G] (R : Finset (Fin m × G))
    (hR : IsUniversalJoinFace R) {a b : G} (hab : a ≠ b) :
    translateJoinFace a R ≠ translateJoinFace b R := by
  intro h
  exact hab (translateJoinFace_unique R hR a b h)

/-- A common point of two distinct translated `(d+1)`-vertex cells lies
already in the `d`-vertex skeleton. -/
theorem translatedFullCells_inter_oldSkeleton
    {m d : ℕ} {G : Type*} [AddGroup G] [Fintype G]
    (R : Finset (Fin m × G)) (hR : IsUniversalJoinFace R)
    (hcard : R.card = d + 1)
    (a b : G) (hab : a ≠ b)
    (w : stdSimplex ℝ (Fin m × G))
    (hwa : w ∈ simplicialRealization
      (fullFaceComplex (translateJoinFace a R)))
    (hwb : w ∈ simplicialRealization
      (fullFaceComplex (translateJoinFace b R))) :
    w ∈ simplicialRealization (universalJoinSkeleton m G d) := by
  let T := FairDivision.Topology.finiteSimplexSupport w
  have hTa : T ⊆ translateJoinFace a R := hwa.2
  have hTb : T ⊆ translateJoinFace b R := hwb.2
  have hproper : T ⊂ translateJoinFace a R := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hTa, ?_⟩
    intro hEq
    have hsub : translateJoinFace a R ⊆ translateJoinFace b R :=
      hEq ▸ hTb
    have hcards : (translateJoinFace b R).card ≤
        (translateJoinFace a R).card := by
      rw [translateJoinFace_card, translateJoinFace_card]
    have hfaces := Finset.eq_of_subset_of_card_le hsub hcards
    exact translateJoinFace_ne_of_ne R hR hab hfaces
  have hcell : translateJoinFace a R ∈
      universalJoinSkeleton m G (d + 1) := by
    refine ⟨universalJoinFace_translate hR a, ?_⟩
    rw [translateJoinFace_card, hcard]
  have hcarda : (translateJoinFace a R).card = d + 1 := by
    rw [translateJoinFace_card, hcard]
  exact universalJoinSkeleton_properFace_old hcell hcarda hwa.1 hproper

/-- The same intersection property holds inside any old complex that
contains the `d`-vertex skeleton. -/
theorem translatedFullCells_inter_old
    {m d : ℕ} {G : Type*} [AddGroup G] [Fintype G]
    (A : PreAbstractSimplicialComplex (Fin m × G))
    (hOld : universalJoinSkeleton m G d ≤ A)
    (R : Finset (Fin m × G)) (hR : IsUniversalJoinFace R)
    (hcard : R.card = d + 1)
    (a b : G) (hab : a ≠ b)
    (w : stdSimplex ℝ (Fin m × G))
    (hwa : w ∈ simplicialRealization
      (fullFaceComplex (translateJoinFace a R)))
    (hwb : w ∈ simplicialRealization
      (fullFaceComplex (translateJoinFace b R))) :
    w ∈ simplicialRealization A := by
  exact simplicialRealization_mono hOld
    (translatedFullCells_inter_oldSkeleton R hR hcard a b hab w hwa hwb)

/-- Outside the old skeleton, a point in the orbit complex belongs to
exactly one translated top cell. -/
theorem translatedFullCell_unique_outside_old
    {m d : ℕ} {G : Type*} [AddGroup G] [Fintype G]
    (A : PreAbstractSimplicialComplex (Fin m × G))
    (hOld : universalJoinSkeleton m G d ≤ A)
    (R : Finset (Fin m × G)) (hR : IsUniversalJoinFace R)
    (hcard : R.card = d + 1)
    (a b : G) (w : stdSimplex ℝ (Fin m × G))
    (hnA : w ∉ simplicialRealization A)
    (hwa : w ∈ simplicialRealization
      (fullFaceComplex (translateJoinFace a R)))
    (hwb : w ∈ simplicialRealization
      (fullFaceComplex (translateJoinFace b R))) :
    a = b := by
  by_contra hab
  exact hnA (translatedFullCells_inter_old A hOld R hR hcard
    a b hab w hwa hwb)

end FairDivision.Topology.Volovikov
