import FairDivision.Topology.Volovikov.JoinFaceRealizationAction
import FairDivision.Topology.NerveConnectivity.FiniteCellAttachment

/-!
# Translation of individual universal-join simplex cells

The global group action restricts to a homeomorphism from the full simplex
on a face to the full simplex on its translated face. This carries a chosen
continuous cell filling across a free face orbit.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity
open scoped Classical

private theorem translateJoinFace_image_symm {m : ℕ} {G : Type*}
    [AddGroup G] (a : G) (S : Finset (Fin m × G)) :
    (translateJoinFace a S).image (translateJoinVertexEquiv a).symm = S := by
  classical
  change (S.image (translateJoinVertexEquiv a)).image
    (translateJoinVertexEquiv a).symm = S
  rw [Finset.image_image]
  have hfun : (translateJoinVertexEquiv (m := m) a).symm ∘
      (translateJoinVertexEquiv (m := m) a) = id := by
    funext v
    exact (translateJoinVertexEquiv (m := m) a).symm_apply_apply v
  rw [hfun, Finset.image_id]

/-- Group translation restricts to a homeomorphism of full face cells. -/
noncomputable def translateJoinFaceCell {m : ℕ} {G : Type*}
    [AddGroup G] [Fintype G]
    (a : G) (S : Finset (Fin m × G)) :
    simplicialRealization (fullFaceComplex S) ≃ₜ
      simplicialRealization (fullFaceComplex (translateJoinFace a S)) := by
  classical
  apply realizationHomeomorphOfVertexEquiv
    (fullFaceComplex S) (fullFaceComplex (translateJoinFace a S))
    (translateJoinVertexEquiv a)
  · intro T hT
    exact ⟨hT.1.image _, Finset.image_subset_image hT.2⟩
  · intro T hT
    refine ⟨hT.1.image _, ?_⟩
    have hsub := Finset.image_subset_image
      (f := (translateJoinVertexEquiv a).symm) hT.2
    simpa only [translateJoinFace_image_symm (m := m) (G := G) a S] using hsub

/-- On weights, cell translation is exactly the global realization action. -/
theorem translateJoinFaceCell_apply {m : ℕ} {G : Type*}
    [AddGroup G] [Fintype G]
    (a : G) (S : Finset (Fin m × G))
    (x : simplicialRealization (fullFaceComplex S)) :
    (translateJoinFaceCell a S x).1 =
      stdSimplex.map (translateJoinVertexEquiv a) x.1 := rfl

end FairDivision.Topology.Volovikov
