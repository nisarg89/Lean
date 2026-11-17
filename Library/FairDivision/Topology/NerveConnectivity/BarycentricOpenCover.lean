import FairDivision.Topology.NerveConnectivity.BarycentricHomeomorph
import FairDivision.Topology.NerveConnectivity.BarycentricStarRetraction
import FairDivision.Topology.NerveConnectivity.NullHomotopy

/-!
# The barycentric open cover and its deformation retracts

For two finite subcomplexes, the open stars in the subdivision cover the union
and intersect in the open star of the intersection. Each star retracts onto the
subdivision of its corresponding subcomplex. The barycentric homeomorphism
therefore transfers the original connectivity hypotheses to this open cover.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe v

/-- The open star viewed within a subdivided ambient realization. -/
def barycentricStarWithin {V : Type v} [Fintype V]
    (K L : PreAbstractSimplicialComplex V) :
    Set (simplicialRealization (barycentricSubdivision L)) :=
  {z | z.1 ∈ barycentricOpenStar K}

/-- A barycentric open star is genuinely open in the subdivided ambient
realization. -/
theorem barycentricStarWithin_isOpen {V : Type v} [Fintype V]
    (K L : PreAbstractSimplicialComplex V) :
    IsOpen (barycentricStarWithin K L) :=
  (barycentricOpenStar_isOpen K).preimage continuous_subtype_val

/-- The subtype topology on a star within the ambient realization agrees
with the ambient-simplex star-domain subtype. -/
def barycentricStarWithinHomeomorph {V : Type v} [Fintype V]
    (K L : PreAbstractSimplicialComplex V) :
    barycentricStarWithin K L ≃ₜ barycentricStarDomain K L where
  toFun z := ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
  invFun z := ⟨⟨z.1, z.2.1⟩, z.2.2⟩
  left_inv z := rfl
  right_inv z := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val

/-- Two stars cover the subdivision of a binary union. -/
theorem barycentricStarDomain_cover_sup {V : Type v} [Fintype V]
    (K L : PreAbstractSimplicialComplex V) :
    barycentricStarDomain K (K ⊔ L) ∪
      barycentricStarDomain L (K ⊔ L) =
        simplicialRealization (barycentricSubdivision (K ⊔ L)) := by
  ext w
  constructor
  · rintro (⟨hw, _⟩ | ⟨hw, _⟩) <;> exact hw
  · intro hw
    rcases barycentricOpenStar_cover_union K L hw with hK | hL
    · exact Or.inl ⟨hw, hK⟩
    · exact Or.inr ⟨hw, hL⟩

/-- The overlap of two stars is exactly the star of the intersection,
inside the subdivided union. -/
theorem barycentricStarDomain_inter_sup {V : Type v} [Fintype V]
    (K L : PreAbstractSimplicialComplex V) :
    barycentricStarDomain K (K ⊔ L) ∩
      barycentricStarDomain L (K ⊔ L) =
        barycentricStarDomain (K ⊓ L) (K ⊔ L) := by
  ext w
  constructor
  · rintro ⟨⟨hw, hK⟩, ⟨_, hL⟩⟩
    exact ⟨hw, (barycentricOpenStar_inter_on_union K L w hw).1 ⟨hK, hL⟩⟩
  · rintro ⟨hw, hI⟩
    obtain ⟨hK, hL⟩ :=
      (barycentricOpenStar_inter_on_union K L w hw).2 hI
    exact ⟨⟨hw, hK⟩, ⟨hw, hL⟩⟩

/-- Each barycentric open star is homotopy equivalent to the subdivided
subcomplex onto which it deformation retracts. -/
noncomputable def barycentricStarHomotopyEquiv {V : Type v} [Fintype V]
    {K L : PreAbstractSimplicialComplex V} (hKL : K ≤ L) :
    ContinuousMap.HomotopyEquiv
      (barycentricStarDomain K L)
      (simplicialRealization (barycentricSubdivision K)) :=
  homotopyEquivOfRetraction
    (barycentricStarProject K L)
    (barycentricStarInclusion hKL)
    (barycentricStarProject_comp_inclusion hKL)
    ⟨(barycentricStarHomotopy hKL).symm⟩

/-- Connectivity of a finite realization transfers to its subdivision. -/
theorem nullConnected_subdivision_of_original {V : Type v} [Fintype V]
    (K : PreAbstractSimplicialComplex V) (k : ℕ)
    (hK : NullConnectedSet k (simplicialRealization K)) :
    NullConnectedSet k (simplicialRealization (barycentricSubdivision K)) :=
  NullConnectedSpace.ofHomotopyEquiv
    (barycentricRealizationHomeomorph K).symm.toHomotopyEquiv hK

/-- Connectivity of a finite realization transfers to its barycentric
open star in any containing finite realization. -/
theorem nullConnected_barycentricStar_of_original {V : Type v} [Fintype V]
    {K L : PreAbstractSimplicialComplex V} (hKL : K ≤ L) (k : ℕ)
    (hK : NullConnectedSet k (simplicialRealization K)) :
    NullConnectedSet k (barycentricStarDomain K L) :=
  NullConnectedSpace.ofHomotopyEquiv
    (barycentricStarHomotopyEquiv hKL).symm
    (nullConnected_subdivision_of_original K k hK)


/-- The original binary gluing hypotheses imply the corresponding
connectivity bounds on the two open stars and their overlap. -/
theorem nullConnected_barycentric_binary_stars {V : Type v} [Fintype V]
    (K L : PreAbstractSimplicialComplex V) (k : ℕ)
    (hK : NullConnectedSet k (simplicialRealization K))
    (hL : NullConnectedSet k (simplicialRealization L))
    (hI : NullConnectedSet (k - 1) (simplicialRealization (K ⊓ L))) :
    NullConnectedSet k (barycentricStarDomain K (K ⊔ L)) ∧
    NullConnectedSet k (barycentricStarDomain L (K ⊔ L)) ∧
    NullConnectedSet (k - 1)
      (barycentricStarDomain (K ⊓ L) (K ⊔ L)) := by
  refine ⟨nullConnected_barycentricStar_of_original le_sup_left k hK,
    nullConnected_barycentricStar_of_original le_sup_right k hL, ?_⟩
  exact nullConnected_barycentricStar_of_original
    (inf_le_left.trans le_sup_left) (k - 1) hI

end FairDivision.Topology.NerveConnectivity
