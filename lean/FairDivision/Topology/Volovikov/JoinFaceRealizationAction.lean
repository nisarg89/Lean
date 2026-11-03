import FairDivision.Topology.Volovikov.JoinFaceOrbits

/-!
# Support transport on the universal-join realization

Translation of a realized join point translates precisely its positive
support face. This identifies the open simplex cells permuted by the group
action, needed to transport a chosen filling over a whole free face orbit.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

/-- Translation carries the positive support face to its translated face. -/
theorem translateJoinRealization_support {m : ℕ} {G : Type*}
    [AddGroup G] [Fintype G]
    (a : G)
    (x : FairDivision.Topology.NerveConnectivity.simplicialRealization
      (universalJoinComplex m G)) :
    FairDivision.Topology.finiteSimplexSupport
      (translateJoinRealization a x).1 =
    translateJoinFace a
      (FairDivision.Topology.finiteSimplexSupport x.1) := by
  classical
  change FairDivision.Topology.finiteSimplexSupport
      (stdSimplex.map (translateJoinVertexEquiv a) x.1) =
    (FairDivision.Topology.finiteSimplexSupport x.1).image
      (translateJoinVertexEquiv a)
  exact finiteSimplexSupport_map_equiv (translateJoinVertexEquiv a) x.1

/-- A realized point supported on one face remains supported on the
translated face after applying the group action. -/
theorem translateJoinRealization_support_subset {m : ℕ} {G : Type*}
    [AddGroup G] [Fintype G]
    (a : G) (S : Finset (Fin m × G))
    (x : FairDivision.Topology.NerveConnectivity.simplicialRealization
      (universalJoinComplex m G))
    (hx : FairDivision.Topology.finiteSimplexSupport x.1 ⊆ S) :
    FairDivision.Topology.finiteSimplexSupport
      (translateJoinRealization a x).1 ⊆ translateJoinFace a S := by
  classical
  rw [translateJoinRealization_support]
  exact Finset.image_subset_image hx

end FairDivision.Topology.Volovikov
