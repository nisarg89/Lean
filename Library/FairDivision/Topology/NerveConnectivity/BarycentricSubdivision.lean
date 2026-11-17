import FairDivision.Topology.NerveConnectivity.SimplicialCover
import Mathlib.Data.Finset.Max
import Mathlib.Order.Preorder.Chain

/-!
# Barycentric subdivision of a finite abstract simplicial complex

Vertices are the original nonempty faces; simplices are finite chains of
faces. This combinatorial construction is the first step toward regular
neighborhoods and the homotopy extension theorem for subcomplex inclusions.
Unlike a vertex type indexed by the complex, the common vertex type `Finset V`
makes intersections and unions of subdivisions directly comparable.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe v

/-- The order complex of the nonempty faces of `K`. -/
def barycentricSubdivision {V : Type v}
    (K : PreAbstractSimplicialComplex V) :
    PreAbstractSimplicialComplex (Finset V) where
  faces := {C | C.Nonempty ∧
    (∀ F ∈ C, F ∈ K) ∧ IsChain (· ⊆ ·) (C : Set (Finset V))}
  isRelLowerSet_faces := by
    intro C hC
    constructor
    · exact hC.1
    · intro D hDC hD
      refine ⟨hD, ?_, ?_⟩
      · intro F hF
        exact hC.2.1 F (hDC hF)
      · exact hC.2.2.mono (by
          intro F hF
          exact hDC hF)

/-- A finite chain of faces has a greatest member under inclusion. -/
theorem finiteChain_exists_greatest {V : Type v}
    (C : Finset (Finset V)) (hC : C.Nonempty)
    (hchain : IsChain (· ⊆ ·) (C : Set (Finset V))) :
    ∃ M ∈ C, ∀ F ∈ C, F ⊆ M := by
  classical
  obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image C Finset.card hC
  refine ⟨M, hM, ?_⟩
  intro F hF
  rcases hchain.total hF hM with h | h
  · exact h
  · have e : M = F := Finset.eq_of_subset_of_card_le h (hmax F hF)
    exact e.symm.subset

/-- A chain with one face in each of two subcomplexes has a face in
both. The smaller of the two faces supplies the common vertex. -/
theorem finiteChain_mixed_has_common_face {V : Type v}
    (K L : PreAbstractSimplicialComplex V)
    (C : Finset (Finset V))
    (hchain : IsChain (· ⊆ ·) (C : Set (Finset V)))
    (hK : ∃ F ∈ C, F ∈ K) (hL : ∃ F ∈ C, F ∈ L) :
    ∃ F ∈ C, F ∈ K ⊓ L := by
  obtain ⟨F, hF, hFK⟩ := hK
  obtain ⟨G, hG, hGL⟩ := hL
  rcases hchain.total hF hG with hFG | hGF
  · refine ⟨F, hF, ⟨hFK, ?_⟩⟩
    exact (L.isRelLowerSet_faces hGL).2 hFG
      (K.isRelLowerSet_faces hFK).1
  · refine ⟨G, hG, ⟨?_, hGL⟩⟩
    exact (K.isRelLowerSet_faces hFK).2 hGF
      (L.isRelLowerSet_faces hGL).1

/-- Subdivision respects subcomplex inclusions. -/
theorem barycentricSubdivision_mono {V : Type v}
    {K L : PreAbstractSimplicialComplex V} (hKL : K ≤ L) :
    barycentricSubdivision K ≤ barycentricSubdivision L := by
  intro C hC
  exact ⟨hC.1, fun F hF => hKL (hC.2.1 F hF), hC.2.2⟩

/-- The subdivision of an intersection is the intersection of subdivisions. -/
theorem barycentricSubdivision_inf {V : Type v}
    (K L : PreAbstractSimplicialComplex V) :
    barycentricSubdivision (K ⊓ L) =
      barycentricSubdivision K ⊓ barycentricSubdivision L := by
  ext C
  constructor
  · intro hC
    exact ⟨⟨hC.1, fun F hF => (hC.2.1 F hF).1, hC.2.2⟩,
      ⟨hC.1, fun F hF => (hC.2.1 F hF).2, hC.2.2⟩⟩
  · intro hC
    exact ⟨hC.1.1, fun F hF => ⟨hC.1.2.1 F hF, hC.2.2.1 F hF⟩,
      hC.1.2.2⟩

/-- A chain in a union belongs wholly to one side, since its greatest face
belongs to one side and all other faces are subfaces of it. -/
theorem barycentricSubdivision_sup {V : Type v}
    (K L : PreAbstractSimplicialComplex V) :
    barycentricSubdivision (K ⊔ L) =
      barycentricSubdivision K ⊔ barycentricSubdivision L := by
  ext C
  constructor
  · intro hC
    obtain ⟨M, hM, htop⟩ := finiteChain_exists_greatest C hC.1 hC.2.2
    have hm := hC.2.1 M hM
    change M ∈ K ∨ M ∈ L at hm
    rcases hm with hm | hm
    · left
      refine ⟨hC.1, ?_, hC.2.2⟩
      intro F hF
      exact (K.isRelLowerSet_faces hm).2 (htop F hF)
        ((K ⊔ L).isRelLowerSet_faces (hC.2.1 F hF)).1
    · right
      refine ⟨hC.1, ?_, hC.2.2⟩
      intro F hF
      exact (L.isRelLowerSet_faces hm).2 (htop F hF)
        ((K ⊔ L).isRelLowerSet_faces (hC.2.1 F hF)).1
  · intro hC
    rcases hC with hC | hC
    · exact ⟨hC.1, fun F hF => Or.inl (hC.2.1 F hF), hC.2.2⟩
    · exact ⟨hC.1, fun F hF => Or.inr (hC.2.1 F hF), hC.2.2⟩

/-- Points with positive mass on at least one barycentric vertex belonging
to `K`. This is an open neighborhood of the subdivided realization of `K`. -/
def barycentricOpenStar {V : Type v} [Fintype V]
    (K : PreAbstractSimplicialComplex V) :
    Set (stdSimplex ℝ (Finset V)) :=
  {w | ∃ F : Finset V, F ∈ K ∧ 0 < w.1 F}

/-- Positive barycentric mass is an open condition. -/
theorem barycentricOpenStar_isOpen {V : Type v} [Fintype V]
    (K : PreAbstractSimplicialComplex V) :
    IsOpen (barycentricOpenStar K) := by
  have hstar : barycentricOpenStar K =
      ⋃ F ∈ K.faces, {w : stdSimplex ℝ (Finset V) | 0 < w.1 F} := by
    ext w
    simp only [barycentricOpenStar, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨F, hF, hpos⟩
      exact ⟨F, hF, hpos⟩
    · rintro ⟨F, hF, hpos⟩
      exact ⟨F, hF, hpos⟩
  rw [hstar]
  apply isOpen_iUnion
  intro F
  apply isOpen_iUnion
  intro _
  exact isOpen_lt continuous_const
    ((continuous_apply F).comp continuous_subtype_val)

/-- The subdivided realization lies in its own open star. -/
theorem barycentricRealization_subset_openStar {V : Type v} [Fintype V]
    (K : PreAbstractSimplicialComplex V) :
    simplicialRealization (barycentricSubdivision K) ⊆
      barycentricOpenStar K := by
  intro w hw
  obtain ⟨F, hF⟩ := (FairDivision.Topology.finiteSimplexSupport_nonempty w)
  exact ⟨F, hw.2.1 F hF,
    (FairDivision.Topology.mem_finiteSimplexSupport_iff w F).1 hF⟩

/-- The two open stars cover the subdivided realization of a union. -/
theorem barycentricOpenStar_cover_union {V : Type v} [Fintype V]
    (K L : PreAbstractSimplicialComplex V) :
    simplicialRealization (barycentricSubdivision (K ⊔ L)) ⊆
      barycentricOpenStar K ∪ barycentricOpenStar L := by
  intro w hw
  obtain ⟨F, hF⟩ := (FairDivision.Topology.finiteSimplexSupport_nonempty w)
  have hface := hw.2.1 F hF
  change F ∈ K ∨ F ∈ L at hface
  rcases hface with hK | hL
  · exact Or.inl ⟨F, hK,
      (FairDivision.Topology.mem_finiteSimplexSupport_iff w F).1 hF⟩
  · exact Or.inr ⟨F, hL,
      (FairDivision.Topology.mem_finiteSimplexSupport_iff w F).1 hF⟩

/-- Inside a subdivided union, the two open stars overlap exactly on the
open star of the intersection. -/
theorem barycentricOpenStar_inter_on_union {V : Type v} [Fintype V]
    (K L : PreAbstractSimplicialComplex V)
    (w : stdSimplex ℝ (Finset V))
    (hw : w ∈ simplicialRealization (barycentricSubdivision (K ⊔ L))) :
    (w ∈ barycentricOpenStar K ∧ w ∈ barycentricOpenStar L) ↔
      w ∈ barycentricOpenStar (K ⊓ L) := by
  constructor
  · rintro ⟨⟨F, hFK, hFw⟩, ⟨G, hGL, hGw⟩⟩
    have hchain : IsChain (· ⊆ ·)
        ((FairDivision.Topology.finiteSimplexSupport w : Finset (Finset V)) :
          Set (Finset V)) := hw.2.2
    obtain ⟨H, hH, hHI⟩ := finiteChain_mixed_has_common_face K L
      (FairDivision.Topology.finiteSimplexSupport w) hchain
      ⟨F, (FairDivision.Topology.mem_finiteSimplexSupport_iff w F).2 hFw, hFK⟩
      ⟨G, (FairDivision.Topology.mem_finiteSimplexSupport_iff w G).2 hGw, hGL⟩
    exact ⟨H, hHI, (FairDivision.Topology.mem_finiteSimplexSupport_iff w H).1 hH⟩
  · rintro ⟨F, hFI, hFw⟩
    exact ⟨⟨F, hFI.1, hFw⟩, ⟨F, hFI.2, hFw⟩⟩

end FairDivision.Topology.NerveConnectivity
