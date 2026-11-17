import FairDivision.Topology.Volovikov.UniversalJoinSkeleton

/-!
# Translation on an invariant finite join subcomplex

During orbitwise cell attachment, each intermediate subcomplex is invariant
under translation. The vertex permutation therefore gives a continuous group
action on every intermediate realization, not only on the full join.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity
open scoped Classical

/-- A finite complex of join vertices is invariant under all group
translations. -/
def IsJoinTranslationInvariant {m : ℕ} {G : Type*}
    [AddGroup G]
    (A : PreAbstractSimplicialComplex (Fin m × G)) : Prop :=
  ∀ (a : G) (S : Finset (Fin m × G)),
    S ∈ A → translateJoinFace a S ∈ A

/-- An invariant subcomplex inherits the continuous translation action. -/
noncomputable def translateInvariantRealization {m : ℕ} {G : Type*}
    [AddGroup G] [Fintype G]
    (A : PreAbstractSimplicialComplex (Fin m × G))
    (hA : IsJoinTranslationInvariant A) (a : G) :
    simplicialRealization A ≃ₜ simplicialRealization A := by
  classical
  apply realizationHomeomorphOfVertexEquiv A A
    (translateJoinVertexEquiv a)
  · intro S hS
    exact hA a S hS
  · intro T hT
    change translateJoinFace (-a) T ∈ A
    exact hA (-a) T hT

/-- The inherited action fixes every point under zero translation. -/
theorem translateInvariantRealization_zero {m : ℕ} {G : Type*}
    [AddGroup G] [Fintype G]
    (A : PreAbstractSimplicialComplex (Fin m × G))
    (hA : IsJoinTranslationInvariant A)
    (x : simplicialRealization A) :
    translateInvariantRealization A hA (0 : G) x = x := by
  apply Subtype.ext
  change stdSimplex.map (translateJoinVertex (0 : G)) x.1 = x.1
  have hvertex : translateJoinVertex (m := m) (0 : G) = id := by
    funext v
    rcases v with ⟨i, g⟩
    simp [translateJoinVertex]
  rw [hvertex, stdSimplex.map_id_apply]

/-- The inherited action satisfies the additive composition law. -/
theorem translateInvariantRealization_add {m : ℕ} {G : Type*}
    [AddGroup G] [Fintype G]
    (A : PreAbstractSimplicialComplex (Fin m × G))
    (hA : IsJoinTranslationInvariant A)
    (a b : G) (x : simplicialRealization A) :
    translateInvariantRealization A hA (a + b) x =
      translateInvariantRealization A hA a
        (translateInvariantRealization A hA b x) := by
  apply Subtype.ext
  change stdSimplex.map (translateJoinVertex (a + b)) x.1 =
    stdSimplex.map (translateJoinVertex a)
      (stdSimplex.map (translateJoinVertex b) x.1)
  rw [stdSimplex.map_comp_apply]
  congr 1
  funext v
  rcases v with ⟨i, g⟩
  simp [translateJoinVertex, add_assoc]

/-- Pointwise laws for a continuous additive group action on the target. -/
def IsContinuousAddAction {G X : Type*}
    [AddGroup G] [TopologicalSpace X]
    (targetAction : G → X ≃ₜ X) : Prop :=
  (∀ x : X, targetAction 0 x = x) ∧
    (∀ (a b : G) (x : X),
      targetAction (a + b) x = targetAction a (targetAction b x))

/-- Equivariance of a map on an invariant join subcomplex. -/
def IsEquivariantJoinMap {m : ℕ} {G X : Type*}
    [AddGroup G] [Fintype G] [TopologicalSpace X]
    (A : PreAbstractSimplicialComplex (Fin m × G))
    (hA : IsJoinTranslationInvariant A)
    (targetAction : G → X ≃ₜ X)
    (f : C(simplicialRealization A, X)) : Prop :=
  ∀ (a : G) (w : simplicialRealization A),
    f (translateInvariantRealization A hA a w) =
      targetAction a (f w)

/-- Every cardinality skeleton is invariant under translation. -/
theorem universalJoinSkeleton_invariant {m d : ℕ} {G : Type*}
    [AddGroup G] :
    IsJoinTranslationInvariant (universalJoinSkeleton m G d) := by
  intro a S hS
  exact universalJoinSkeleton_translate hS a

/-- The full finite universal join is invariant under translation. -/
theorem universalJoinComplex_invariant {m : ℕ} {G : Type*}
    [AddGroup G] :
    IsJoinTranslationInvariant (universalJoinComplex m G) := by
  intro a S hS
  exact universalJoinFace_translate hS a

end FairDivision.Topology.Volovikov
