import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Characters diagonalize the complex regular translation action

Mathlib provides a complex character basis for functions on a finite
abelian group. Here we state the action eigenvector calculation and the
centeredness of every nontrivial character. These are the algebraic inputs
to identifying the reduced regular representation's top Chern class with
the nonzero character product. The characteristic-class identification
itself is not proved here.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open scoped BigOperators

/-- Left regular translation of a complex-valued function. -/
def complexRegularTranslate {G : Type*} [AddCommGroup G]
    (a : G) (f : G → ℂ) : G → ℂ :=
  fun x => f (x - a)

/-- Translation acts diagonally on each complex character. -/
theorem complexRegularTranslate_character
    {G : Type*} [AddCommGroup G]
    (a : G) (ψ : AddChar G ℂ) :
    complexRegularTranslate a (ψ : G → ℂ) =
      ψ (-a) • (ψ : G → ℂ) := by
  funext x
  change ψ (x - a) = ψ (-a) * ψ x
  rw [sub_eq_add_neg, ψ.map_add_eq_mul]
  exact mul_comm _ _

/-- A nontrivial complex character lies in the centered regular
representation. -/
theorem nontrivialCharacter_centered
    {G : Type*} [AddCommGroup G] [Fintype G]
    (ψ : AddChar G ℂ) (hψ : ψ ≠ 0) :
    (∑ g : G, ψ g) = 0 :=
  AddChar.sum_eq_zero_iff_ne_zero.mpr hψ

/-- Mathlib's finite Fourier theorem supplies a basis of the full
complex regular representation indexed by all characters. -/
noncomputable def complexRegularCharacterBasis
    (G : Type*) [AddCommGroup G] [Finite G] :
    Module.Basis (AddChar G ℂ) ℂ (G → ℂ) :=
  AddChar.complexBasis G

end FairDivision.Topology.Volovikov
