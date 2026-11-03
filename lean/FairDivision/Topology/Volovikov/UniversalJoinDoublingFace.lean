import FairDivision.Topology.Volovikov.UniversalJoinDoublingCoordinates
import FairDivision.Topology.Volovikov.TopologicalJoinLift

/-!
# The doubled cylinder lies in the finite universal join

The two embedded endpoint supports use disjoint sets of colors. Hence every
convex combination still has at most one label in each color.
-/

set_option autoImplicit false

open scoped unitInterval Topology Classical

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity

private theorem doubledJoinColor_disjoint
    {m : ℕ} {G : Type*} (v w : Fin m × G) :
    (leftDoubledJoinVertex v).1 ≠ (rightDoubledJoinVertex w).1 := by
  intro h
  have hval := congrArg Fin.val h
  simp only [leftDoubledJoinVertex, rightDoubledJoinVertex,
    Fin.val_castAdd, Fin.val_natAdd] at hval
  omega

/-- The union of two universal-join faces in disjoint color blocks is again a
universal-join face. -/
theorem doubledJoinFace_union
    {m : ℕ} {G : Type*}
    {S T : Finset (Fin m × G)}
    (hS : IsUniversalJoinFace S) (hT : IsUniversalJoinFace T) :
    IsUniversalJoinFace
      (S.image leftDoubledJoinVertex ∪ T.image rightDoubledJoinVertex) := by
  classical
  constructor
  · obtain ⟨v, hv⟩ := hS.1
    exact ⟨leftDoubledJoinVertex v,
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)⟩
  · intro i g h hgi hhi
    rcases Finset.mem_union.mp hgi with hgl | hgr
    · obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp hgl
      rcases Finset.mem_union.mp hhi with hhl | hhr
      · obtain ⟨w, hw, hweq⟩ := Finset.mem_image.mp hhl
        have hi : v.1 = w.1 :=
          Fin.castAdd_injective m m
            ((congrArg Prod.fst hveq).trans
              (congrArg Prod.fst hweq).symm)
        have hw' : (v.1, w.2) ∈ S := by simpa [hi] using hw
        calc
          g = v.2 := (congrArg Prod.snd hveq).symm
          _ = w.2 := hS.2 v.1 v.2 w.2 hv hw'
          _ = h := congrArg Prod.snd hweq
      · obtain ⟨w, _, hweq⟩ := Finset.mem_image.mp hhr
        exact False.elim ((doubledJoinColor_disjoint v w)
          ((congrArg Prod.fst hveq).trans
            (congrArg Prod.fst hweq).symm))
    · obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp hgr
      rcases Finset.mem_union.mp hhi with hhl | hhr
      · obtain ⟨w, _, hweq⟩ := Finset.mem_image.mp hhl
        exact False.elim ((doubledJoinColor_disjoint w v)
          ((congrArg Prod.fst hweq).trans
            (congrArg Prod.fst hveq).symm))
      · obtain ⟨w, hw, hweq⟩ := Finset.mem_image.mp hhr
        have hi : v.1 = w.1 :=
          Fin.natAdd_injective m m
            ((congrArg Prod.fst hveq).trans
              (congrArg Prod.fst hweq).symm)
        have hw' : (v.1, w.2) ∈ T := by simpa [hi] using hw
        calc
          g = v.2 := (congrArg Prod.snd hveq).symm
          _ = w.2 := hT.2 v.1 v.2 w.2 hv hw'
          _ = h := congrArg Prod.snd hweq

/-- The weighted coordinates satisfy the doubled universal-join face
condition. -/
theorem doubledJoinCylinderSimplex_mem
    (m : ℕ) (G : Type*) [Fintype G]
    (z : I ×
      (simplicialRealization (universalJoinComplex m G) ×
        simplicialRealization (universalJoinComplex m G))) :
    doubledJoinCylinderSimplex m G z ∈
      simplicialRealization (universalJoinComplex (m + m) G) := by
  classical
  let S := FairDivision.Topology.finiteSimplexSupport z.2.1.1
  let T := FairDivision.Topology.finiteSimplexSupport z.2.2.1
  have hface : IsUniversalJoinFace
      (S.image leftDoubledJoinVertex ∪ T.image rightDoubledJoinVertex) :=
    doubledJoinFace_union z.2.1.2 z.2.2.2
  have hsub : FairDivision.Topology.finiteSimplexSupport
      (doubledJoinCylinderSimplex m G z) ⊆
        S.image leftDoubledJoinVertex ∪ T.image rightDoubledJoinVertex := by
    intro v hv
    have hseg := FairDivision.Topology.finiteSimplexSegment_support_subset
      (stdSimplex.map leftDoubledJoinVertex z.2.1.1)
      (stdSimplex.map rightDoubledJoinVertex z.2.2.1) z.1
    have hvseg := hseg (show v ∈ FairDivision.Topology.finiteSimplexSupport
      (FairDivision.Topology.finiteSimplexSegment
        (stdSimplex.map leftDoubledJoinVertex z.2.1.1)
        (stdSimplex.map rightDoubledJoinVertex z.2.2.1) z.1) by
          simpa only [doubledJoinCylinderSimplex] using hv)
    have hsplit := hvseg
    simp only [Finset.mem_union] at hsplit
    rcases hsplit with hl | hr
    · exact Finset.mem_union_left _
        (finiteSimplexSupport_map_subset leftDoubledJoinVertex z.2.1.1 hl)
    · exact Finset.mem_union_right _
        (finiteSimplexSupport_map_subset rightDoubledJoinVertex z.2.2.1 hr)
  exact ((universalJoinComplex (m + m) G).isRelLowerSet_faces hface).2
    hsub (FairDivision.Topology.finiteSimplexSupport_nonempty _)

/-- The weighted coordinates as a point in the doubled universal join. -/
noncomputable def doubledJoinCylinderPoint
    (m : ℕ) (G : Type*) [Fintype G] :
    C(I ×
      (simplicialRealization (universalJoinComplex m G) ×
        simplicialRealization (universalJoinComplex m G)),
      simplicialRealization (universalJoinComplex (m + m) G)) :=
  ⟨fun z => ⟨doubledJoinCylinderSimplex m G z,
      doubledJoinCylinderSimplex_mem m G z⟩,
    (doubledJoinCylinderSimplex_continuous m G).subtype_mk _⟩

/-- The two endpoint identifications make the cylinder map descend to the
topological join. -/
noncomputable def doubledJoinMap
    (m : ℕ) (G : Type*) [Fintype G] :
    C(TopologicalJoin
      (simplicialRealization (universalJoinComplex m G))
      (simplicialRealization (universalJoinComplex m G)),
      simplicialRealization (universalJoinComplex (m + m) G)) :=
  topologicalJoinLift (doubledJoinCylinderPoint m G)
    (by
      intro x y y'
      apply Subtype.ext
      simp [doubledJoinCylinderPoint, doubledJoinCylinderSimplex])
    (by
      intro x x' y
      apply Subtype.ext
      simp [doubledJoinCylinderPoint, doubledJoinCylinderSimplex])

end FairDivision.Topology.Volovikov
