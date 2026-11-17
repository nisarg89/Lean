import FairDivision.Topology.Volovikov.ElementaryAbelianCharacters
import FairDivision.Topology.Volovikov.CenteredCharacterDecomposition

/-!
# Centered regular basis indexed by nonzero coefficient vectors

The coefficient-vector parametrization of elementary-abelian characters
reindexes the already proved centered regular character basis. This is the
representation side of the eventual top Chern-class calculation; the
cohomological identification remains a separate theorem.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

/-- Nonzero coefficient vectors correspond exactly to nontrivial complex
characters of the elementary abelian group. -/
noncomputable def nonzeroCoefficientCharacterEquiv
    (p r : ℕ) [NeZero p] :
    {a : Fin r → ZMod p // a ≠ 0} ≃
      {ψ : AddChar (Fin r → ZMod p) ℂ // ψ ≠ 0} := by
  let e := elementaryAbelianCharacterEquiv p r
  refine
    { toFun := fun a => ⟨e a.1, ?_⟩
      invFun := fun ψ => ⟨e.symm ψ.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro h
    apply a.2
    apply e.injective
    simpa only [map_zero] using h
  · intro h
    apply ψ.2
    calc
      ψ.1 = e (e.symm ψ.1) := (e.apply_symm_apply ψ.1).symm
      _ = e 0 := congrArg e h
      _ = 0 := map_zero e
  · intro a
    apply Subtype.ext
    exact e.symm_apply_apply a.1
  · intro ψ
    apply Subtype.ext
    exact e.apply_symm_apply ψ.1

/-- The centered complex regular representation of `(ZMod p)^r` has one
basis vector for each nonzero coefficient vector. -/
noncomputable def centeredElementaryAbelianCharacterBasis
    (p r : ℕ) [NeZero p] :
    Module.Basis {a : Fin r → ZMod p // a ≠ 0} ℂ
      (centeredComplexSubmodule (Fin r → ZMod p)) :=
  (centeredCharacterBasis (Fin r → ZMod p)).reindex
    (nonzeroCoefficientCharacterEquiv p r).symm

end FairDivision.Topology.Volovikov
