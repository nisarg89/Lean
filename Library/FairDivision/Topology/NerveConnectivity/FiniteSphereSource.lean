import FairDivision.Topology.NerveConnectivity.FiniteFaceFiniteBoundary
import FairDivision.Topology.NerveConnectivity.BarycentricMeshIteration

/-!
# A finite simplicial source for every cube-boundary sphere

The operational sphere model is homeomorphic to the boundary of a
finite standard simplex. Its faces, and every iterated barycentric
subdivision of them, have at most `j+1` vertices. This gives the exact
source dimension used by the direct finite-cone gluing argument.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.NerveConnectivity

/-- The boundary complex of a `(j+1)`-simplex. -/
def finiteSphereComplex (j : ℕ) :
    PreAbstractSimplicialComplex (Fin (j + 2)) :=
  boundaryFaceComplex (Finset.univ : Finset (Fin (j + 2)))

/-- The finite boundary complex realizes the operational cube sphere. -/
noncomputable def finiteSphereRealizationHomeomorph (j : ℕ) :
    simplicialRealization (finiteSphereComplex j) ≃ₜ CubeSphere j := by
  let F : Finset (Fin (j + 2)) := Finset.univ
  have hF : F.Nonempty := by
    exact Finset.univ_nonempty
  have hcard : F.card = j + 2 := by
    simp [F]
  exact (boundaryFaceRealizationHomeomorph F hF).trans
    ((finiteFaceBoundaryFinHomeomorph F j hcard).trans
      (FairDivision.Topology.finiteSimplexBoundaryCubeSphereHomeomorph j))

/-- A face of the source `j`-sphere has at most `j+1` vertices. -/
theorem finiteSphereComplex_card_le (j : ℕ) :
    ∀ F : Finset (Fin (j + 2)), F ∈ finiteSphereComplex j →
      F.card ≤ j + 1 := by
  intro F hF
  have hlt : F.card < (Finset.univ : Finset (Fin (j + 2))).card :=
    Finset.card_lt_card hF.2
  simp at hlt
  omega

/-- The source dimension does not grow under barycentric subdivision. -/
theorem iteratedFiniteSphereComplex_card_le (j n : ℕ) :
    ∀ F : Finset (iteratedBarycentricVertex (Fin (j + 2)) n),
      F ∈ iteratedBarycentricComplex (finiteSphereComplex j) n →
      F.card ≤ j + 1 :=
  iteratedBarycentric_faceCard_le
    (finiteSphereComplex j) (j + 1)
      (finiteSphereComplex_card_le j) n

end FairDivision.Topology.NerveConnectivity
