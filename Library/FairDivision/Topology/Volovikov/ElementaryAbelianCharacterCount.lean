import FairDivision.Topology.Volovikov.ElementaryAbelianCharacterBasis
import Mathlib.Algebra.Field.ZMod

/-!
# Number of nontrivial elementary-abelian characters

The centered complex regular representation has one character line for
each nonzero coefficient vector, hence rank `p^r - 1`. Its top Chern class,
when constructed, must live in cohomological degree `2 * (p^r - 1)`.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

/-- The elementary abelian group has `p^r` elements. -/
theorem elementaryAbelian_card (p r : ℕ) [Fact p.Prime] :
    Fintype.card (Fin r → ZMod p) = p ^ r := by
  rw [Fintype.card_pi_const, ZMod.card]

/-- The set of nonzero coefficient vectors has `p^r - 1` elements. -/
theorem nonzeroCoefficient_card (p r : ℕ) [Fact p.Prime] :
    Fintype.card {a : Fin r → ZMod p // a ≠ 0} = p ^ r - 1 := by
  classical
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  exact congrArg (· - 1) (elementaryAbelian_card p r)

/-- The nontrivial complex characters have the same count. -/
theorem nontrivialElementaryAbelianCharacter_card (p r : ℕ) [Fact p.Prime] :
    Fintype.card {ψ : AddChar (Fin r → ZMod p) ℂ // ψ ≠ 0} = p ^ r - 1 := by
  rw [← Fintype.card_congr (nonzeroCoefficientCharacterEquiv p r)]
  exact nonzeroCoefficient_card p r

/-- The complex centered regular representation has dimension `p^r - 1`. -/
theorem elementaryAbelian_centered_finrank (p r : ℕ) [Fact p.Prime] :
    Module.finrank ℂ (centeredComplexSubmodule (Fin r → ZMod p)) = p ^ r - 1 := by
  rw [Module.finrank_eq_card_basis (centeredElementaryAbelianCharacterBasis p r)]
  exact nonzeroCoefficient_card p r

end FairDivision.Topology.Volovikov
