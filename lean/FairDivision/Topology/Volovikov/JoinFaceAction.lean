import FairDivision.Topology.Volovikov.UniversalJoinRealization

/-!
# Translation action on faces of a finite universal join

For the equivariant cellular extension, one fills a representative of each
free face orbit and translates the filling. This module records the algebraic
action and the uniqueness of the translating group element.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

/-- Translating a join face by zero does nothing. -/
theorem translateJoinFace_zero {m : ℕ} {G : Type*}
    [AddGroup G]
    (S : Finset (Fin m × G)) : translateJoinFace (0 : G) S = S := by
  classical
  change S.image (translateJoinVertex (0 : G)) = S
  have hfun : translateJoinVertex (m := m) (0 : G) = id := by
    funext v
    rcases v with ⟨i, g⟩
    simp [translateJoinVertex]
  rw [hfun, Finset.image_id]

/-- Translating a join face by a sum is successive translation. -/
theorem translateJoinFace_add {m : ℕ} {G : Type*}
    [AddGroup G]
    (a b : G) (S : Finset (Fin m × G)) :
    translateJoinFace (a + b) S =
      translateJoinFace a (translateJoinFace b S) := by
  classical
  simp only [translateJoinFace, Finset.image_image]
  congr 1
  funext v
  rcases v with ⟨i, g⟩
  simp [translateJoinVertex, add_assoc]

/-- Translation preserves the cardinality of each face. -/
theorem translateJoinFace_card {m : ℕ} {G : Type*}
    [AddGroup G]
    (a : G) (S : Finset (Fin m × G)) :
    (translateJoinFace a S).card = S.card := by
  classical
  change (S.image (translateJoinVertex a)).card = S.card
  exact Finset.card_image_iff.mpr
    (fun x _ y _ h => translateJoinVertex_injective a h)

/-- If two group elements translate the same nonempty universal-join face
to the same face, they are equal. -/
theorem translateJoinFace_unique {m : ℕ} {G : Type*}
    [AddGroup G]
    (S : Finset (Fin m × G)) (hS : IsUniversalJoinFace S)
    (a b : G)
    (h : translateJoinFace a S = translateJoinFace b S) : a = b := by
  have h' : translateJoinFace (-b) (translateJoinFace a S) = S := by
    rw [h, ← translateJoinFace_add, neg_add_cancel, translateJoinFace_zero]
  rw [← translateJoinFace_add] at h'
  have hab : -b + a = 0 := universalJoinFace_free hS (-b + a) h'
  exact (neg_add_eq_zero.mp hab).symm

end FairDivision.Topology.Volovikov
