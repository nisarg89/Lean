import FairDivision.Topology.NerveConnectivity.FiniteOpenCoverGluing
import FairDivision.Topology.NerveConnectivity.BarycentricOpenCover
import FairDivision.Topology.NerveConnectivity.OperationalReduction

/-!
# Binary simplicial gluing from open-cover gluing

The open stars of two subcomplexes cover the barycentric subdivision of
their union. Their overlap is the open star of the intersection. The
star deformation retractions transfer the connectivity hypotheses, and
the generic positive-dimensional open-cover theorem finishes the glue.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe v

/-- Positive-dimensional binary simplicial gluing in the operational
cube-sphere nullhomotopy predicate. -/
theorem operationalBinaryGluing_of_openCover
    {V : Type v} [Fintype V] :
    OperationalBinarySimplicialGluing V := by
  intro k hk K L hK hL hI
  let S := K ⊔ L
  let X := simplicialRealization (barycentricSubdivision S)
  let U : Set X := barycentricStarWithin K S
  let W : Set X := barycentricStarWithin L S
  have hUopen : IsOpen U := barycentricStarWithin_isOpen K S
  have hWopen : IsOpen W := barycentricStarWithin_isOpen L S
  have hcover : U ∪ W = Set.univ := by
    ext z
    constructor
    · intro _
      trivial
    · intro _
      have hz : z.1 ∈ barycentricStarDomain K S ∪
          barycentricStarDomain L S := by
        rw [barycentricStarDomain_cover_sup K L]
        exact z.2
      rcases hz with hz | hz
      · exact Or.inl hz.2
      · exact Or.inr hz.2
  have hinter : U ∩ W = barycentricStarWithin (K ⊓ L) S := by
    ext z
    change z.1 ∈ barycentricOpenStar K ∧
        z.1 ∈ barycentricOpenStar L ↔
      z.1 ∈ barycentricOpenStar (K ⊓ L)
    exact barycentricOpenStar_inter_on_union K L z.1 z.2
  obtain ⟨hStarK, hStarL, hStarI⟩ :=
    nullConnected_barycentric_binary_stars K L k hK hL hI
  have hUK : NullConnectedSet k U :=
    NullConnectedSpace.ofHomotopyEquiv
      (barycentricStarWithinHomeomorph K S).symm.toHomotopyEquiv hStarK
  have hWL : NullConnectedSet k W :=
    NullConnectedSpace.ofHomotopyEquiv
      (barycentricStarWithinHomeomorph L S).symm.toHomotopyEquiv hStarL
  have hUW : NullConnectedSet (k - 1) (U ∩ W) := by
    rw [hinter]
    exact NullConnectedSpace.ofHomotopyEquiv
      (barycentricStarWithinHomeomorph (K ⊓ L) S).symm.toHomotopyEquiv
      hStarI
  have hX : NullConnectedSpace k X :=
    nullConnectedSpace_binaryOpenCover U W hUopen hWopen hcover
      k hk hUK hWL hUW
  exact NullConnectedSpace.ofHomotopyEquiv
    (barycentricRealizationHomeomorph S).toHomotopyEquiv hX

end FairDivision.Topology.NerveConnectivity
