import FairDivision.Topology.Volovikov.JoinOrbitTransport

/-!
# Composition laws for translation of universal-join simplex cells

The coordinate formulas make the cell homeomorphisms compatible with the
additive group action. These laws are used when a filling chosen on one face
is propagated over its entire free orbit.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity
open scoped Classical

/-- Zero translation fixes every point in a full simplex cell. -/
theorem translateJoinFaceCell_zero {m : ℕ} {G : Type*}
    [AddGroup G] [Fintype G]
    (S : Finset (Fin m × G))
    (x : simplicialRealization (fullFaceComplex S)) :
    (translateJoinFaceCell (0 : G) S x).1 = x.1 := by
  change stdSimplex.map (translateJoinVertex (0 : G)) x.1 = x.1
  have hvertex : translateJoinVertex (m := m) (0 : G) = id := by
    funext v
    rcases v with ⟨i, g⟩
    simp [translateJoinVertex]
  rw [hvertex, stdSimplex.map_id_apply]

/-- Translation of full simplex cells composes according to the group law.
The equality is stated in the ambient probability simplex, since the two
codomain subtypes are identified only after the face-action law. -/
theorem translateJoinFaceCell_add {m : ℕ} {G : Type*}
    [AddGroup G] [Fintype G]
    (a b : G) (S : Finset (Fin m × G))
    (x : simplicialRealization (fullFaceComplex S)) :
    (translateJoinFaceCell (a + b) S x).1 =
      (translateJoinFaceCell a (translateJoinFace b S)
        (translateJoinFaceCell b S x)).1 := by
  change stdSimplex.map (translateJoinVertex (a + b)) x.1 =
    stdSimplex.map (translateJoinVertex a)
      (stdSimplex.map (translateJoinVertex b) x.1)
  rw [stdSimplex.map_comp_apply]
  congr 1
  funext v
  rcases v with ⟨i, g⟩
  simp [translateJoinVertex, add_assoc]

/-- A full cell's inverse translation uses the inverse vertex permutation. -/
theorem translateJoinFaceCell_symm_apply {m : ℕ} {G : Type*}
    [AddGroup G] [Fintype G]
    (a : G) (S : Finset (Fin m × G))
    (x : simplicialRealization
      (fullFaceComplex (translateJoinFace a S))) :
    ((translateJoinFaceCell a S).symm x).1 =
      stdSimplex.map (translateJoinVertexEquiv a).symm x.1 := rfl

end FairDivision.Topology.Volovikov
