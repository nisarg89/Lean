import FairDivision.Topology.Volovikov.RegularCharacterEigenvectors
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Group.Translate

/-!
# Character decomposition of the centered complex regular representation

The nontrivial complex characters of a finite abelian group form a basis of
its centered regular representation. This is the representation-theoretic
input to the Euler-class calculation; no characteristic-class theorem is
asserted here.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open scoped BigOperators

/-- Summation over a finite group, as a complex-linear map. -/
def complexCoordinateSum (G : Type*) [AddCommGroup G] [Fintype G] :
    (G → ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∑ g : G, f g
  map_add' f h := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum]

/-- The complexification of the centered regular representation. -/
def centeredComplexSubmodule (G : Type*) [AddCommGroup G] [Fintype G] :
    Submodule ℂ (G → ℂ) :=
  LinearMap.ker (complexCoordinateSum G)

/-- Every nontrivial character belongs to the centered subspace. -/
theorem nontrivialCharacter_mem_centered
    {G : Type*} [AddCommGroup G] [Fintype G]
    (ψ : AddChar G ℂ) (hψ : ψ ≠ 0) :
    (ψ : G → ℂ) ∈ centeredComplexSubmodule G := by
  change (∑ g : G, ψ g) = 0
  exact nontrivialCharacter_centered ψ hψ

/-- Nontrivial characters remain linearly independent as complex functions. -/
theorem nontrivialCharacters_linearIndependent
    (G : Type*) [AddCommGroup G] [Fintype G] :
    LinearIndependent ℂ
      (fun ψ : {ψ : AddChar G ℂ // ψ ≠ 0} => (ψ.1 : G → ℂ)) :=
  (AddChar.linearIndependent G ℂ).comp Subtype.val Subtype.val_injective

/-- The finite nontrivial-character family spans the entire centered
complex regular representation. -/
theorem nontrivialCharacters_span_centered
    (G : Type*) [AddCommGroup G] [Fintype G] :
    Submodule.span ℂ
      (Set.range (fun ψ : {ψ : AddChar G ℂ // ψ ≠ 0} => (ψ.1 : G → ℂ))) =
      centeredComplexSubmodule G := by
  classical
  let b : {ψ : AddChar G ℂ // ψ ≠ 0} → (G → ℂ) := fun ψ => ψ.1
  have hli : LinearIndependent ℂ b :=
    nontrivialCharacters_linearIndependent G
  have hle : Submodule.span ℂ (Set.range b) ≤ centeredComplexSubmodule G := by
    apply Submodule.span_le.mpr
    rintro f ⟨ψ, rfl⟩
    exact nontrivialCharacter_mem_centered ψ.1 ψ.2
  have hsurj : Function.Surjective (complexCoordinateSum G) := by
    intro z
    refine ⟨(fun g : G => if g = 0 then z else 0), ?_⟩
    simp [complexCoordinateSum]
  have hrange : LinearMap.range (complexCoordinateSum G) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hdim := (complexCoordinateSum G).finrank_range_add_finrank_ker
  rw [hrange] at hdim
  simp only [finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card] at hdim
  have hcard : Fintype.card {ψ : AddChar G ℂ // ψ ≠ 0} = Fintype.card G - 1 := by
    simpa [Fintype.card_subtype_compl, AddChar.card_eq] using
      (Fintype.card_subtype_compl (fun ψ : AddChar G ℂ => ψ = 0))
  have hdim' : Module.finrank ℂ (centeredComplexSubmodule G) =
      Fintype.card {ψ : AddChar G ℂ // ψ ≠ 0} := by
    change Module.finrank ℂ (LinearMap.ker (complexCoordinateSum G)) = _
    omega
  have hspan : Module.finrank ℂ (Submodule.span ℂ (Set.range b)) =
      Fintype.card {ψ : AddChar G ℂ // ψ ≠ 0} :=
    finrank_span_eq_card hli
  exact Submodule.eq_of_le_of_finrank_eq hle (hspan.trans hdim'.symm)

/-- The nontrivial complex characters give a basis of the centered regular
representation. -/
noncomputable def centeredCharacterBasis
    (G : Type*) [AddCommGroup G] [Fintype G] :
    Module.Basis {ψ : AddChar G ℂ // ψ ≠ 0} ℂ
      (centeredComplexSubmodule G) := by
  classical
  rw [← nontrivialCharacters_span_centered G]
  exact Module.Basis.span (nontrivialCharacters_linearIndependent G)

/-- Regular translation preserves the centered complex subspace. -/
theorem complexRegularTranslate_mem_centered
    {G : Type*} [AddCommGroup G] [Fintype G]
    (a : G) (f : centeredComplexSubmodule G) :
    complexRegularTranslate a (f : G → ℂ) ∈ centeredComplexSubmodule G := by
  change (∑ g : G, complexRegularTranslate a (f : G → ℂ) g) = 0
  rw [show (∑ g : G, complexRegularTranslate a (f : G → ℂ) g) =
      ∑ g : G, (f : G → ℂ) g from sum_translate a (f : G → ℂ)]
  exact f.2

/-- The centered regular translation, as a complex-linear operator. -/
def centeredRegularTranslate
    (G : Type*) [AddCommGroup G] [Fintype G]
    (a : G) : centeredComplexSubmodule G →ₗ[ℂ]
      centeredComplexSubmodule G where
  toFun f := ⟨complexRegularTranslate a f.1,
    complexRegularTranslate_mem_centered a f⟩
  map_add' f h := by
    apply Subtype.ext
    funext x
    rfl
  map_smul' c f := by
    apply Subtype.ext
    funext x
    rfl

/-- Translation by zero acts as the identity on centered functions. -/
theorem centeredRegularTranslate_zero
    (G : Type*) [AddCommGroup G] [Fintype G] :
    centeredRegularTranslate G 0 = LinearMap.id := by
  ext f x
  simp [centeredRegularTranslate, complexRegularTranslate]

/-- The centered translation operators form a representation of the
additive group. -/
theorem centeredRegularTranslate_add
    (G : Type*) [AddCommGroup G] [Fintype G]
    (a b : G) :
    centeredRegularTranslate G (a + b) =
      (centeredRegularTranslate G a).comp
        (centeredRegularTranslate G b) := by
  ext f x
  simp [centeredRegularTranslate, complexRegularTranslate, sub_sub]

/-- Each nontrivial character is an eigenvector of the centered regular
translation operator. -/
theorem centeredRegularTranslate_character
    {G : Type*} [AddCommGroup G] [Fintype G]
    (a : G) (ψ : AddChar G ℂ) (hψ : ψ ≠ 0) :
    centeredRegularTranslate G a
      ⟨(ψ : G → ℂ), nontrivialCharacter_mem_centered ψ hψ⟩ =
      ψ (-a) •
        (⟨(ψ : G → ℂ), nontrivialCharacter_mem_centered ψ hψ⟩ :
          centeredComplexSubmodule G) := by
  apply Subtype.ext
  exact complexRegularTranslate_character a ψ

end FairDivision.Topology.Volovikov
