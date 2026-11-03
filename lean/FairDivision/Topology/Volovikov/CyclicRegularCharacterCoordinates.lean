import FairDivision.Topology.Volovikov.CenteredCharacterDecomposition
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Continuous Fourier coordinates for the cyclic reduced regular space

This uses mathlib's existing complex character basis. The coefficient of
the trivial character vanishes on centered vectors, and deleting that
one coefficient preserves nonzeroness. Translation is diagonal with the
exact scalar ψ(-a), including its sign for odd primes.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov.CyclicRegularCharacterCoordinates

open scoped BigOperators

section FiniteAbelian

variable (G : Type*) [AddCommGroup G] [Fintype G]

noncomputable def coefficient (f : G→ℂ) (ψ : AddChar G ℂ) : ℂ :=
  (AddChar.complexBasis G).equivFun f ψ

noncomputable def coefficientLinear (ψ : AddChar G ℂ) : (G→ℂ)→ₗ[ℂ]ℂ :=
  (LinearMap.proj ψ).comp (AddChar.complexBasis G).equivFun.toLinearMap

theorem coefficient_continuous (ψ : AddChar G ℂ) :
    Continuous (fun f : G→ℂ=>coefficient G f ψ) :=
  (coefficientLinear G ψ).continuous_of_finiteDimensional

private def translation (a : G) : (G→ℂ)→ₗ[ℂ](G→ℂ) where
  toFun:=complexRegularTranslate a
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

/-- Basis expansion and the already proved character eigenvector law
calculate the actual coordinate action. -/
theorem coefficient_translate (a : G) (f : G→ℂ) (ψ : AddChar G ℂ) :
    coefficient G (complexRegularTranslate a f) ψ=
      ψ (-a)*coefficient G f ψ := by
  classical
  let b:=AddChar.complexBasis G
  have hEigen (χ : AddChar G ℂ) :
      translation G a (b χ)=χ (-a)•b χ := by
    change complexRegularTranslate a (b χ)=χ (-a)•b χ
    simpa only [b,AddChar.complexBasis_apply] using
      complexRegularTranslate_character a χ
  have hExpand : translation G a f=
      ∑χ : AddChar G ℂ,(b.equivFun f χ)•(χ (-a)•b χ) := by
    conv_lhs=>rw [←b.sum_equivFun f]
    simp only [map_sum,map_smul,hEigen]
  change b.equivFun (translation G a f) ψ=ψ (-a)*b.equivFun f ψ
  rw [hExpand]
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,
    b.equivFun_self,smul_eq_mul]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  exact mul_comm _ _

/-- The trivial character coefficient is zero exactly where the finite
coordinate sum is zero. Only the forward direction is needed here. -/
theorem trivial_coefficient_zero {f : G→ℂ} (hf : ∑g : G,f g=0) :
    coefficient G f 0=0 := by
  classical
  let b:=AddChar.complexBasis G
  have hExpand : (∑χ : AddChar G ℂ,coefficient G f χ*(∑g : G,χ g))=
      ∑g : G,f g := by
    calc
      _ = ∑g : G,∑χ : AddChar G ℂ,(b.equivFun f χ)*χ g := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        rfl
      _ = ∑g : G,f g := by
        apply Finset.sum_congr rfl
        intro g hg
        have h:=congrFun (b.sum_equivFun f) g
        simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
          b,AddChar.complexBasis_apply] using h
  have hOnly : (∑χ : AddChar G ℂ,coefficient G f χ*(∑g : G,χ g))=
      coefficient G f 0*(Fintype.card G : ℂ) := by
    rw [Finset.sum_eq_single (0 : AddChar G ℂ)]
    · simp
    · intro χ hχ hNontrivial
      rw [nontrivialCharacter_centered χ hNontrivial,mul_zero]
    · simp
  rw [hOnly,hf] at hExpand
  exact (mul_eq_zero.mp hExpand).resolve_right (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- Removing the trivial Fourier coordinate cannot annihilate a nonzero
centered vector. -/
theorem nontrivial_coordinates_nonzero {f : G→ℂ}
    (hCenter : ∑g : G,f g=0) (hNonzero : f≠0) :
    (fun ψ : {ψ : AddChar G ℂ // ψ≠0}=>coefficient G f ψ.1)≠0 := by
  intro hZero
  apply hNonzero
  apply (AddChar.complexBasis G).equivFun.injective
  funext ψ
  change coefficient G f ψ=(AddChar.complexBasis G).equivFun (0 : G→ℂ) ψ
  simp only [map_zero,Pi.zero_apply]
  by_cases hψ : ψ=0
  · subst ψ
    exact trivial_coefficient_zero G hCenter
  · have h:=congrFun hZero ⟨ψ,hψ⟩
    simpa only [Pi.zero_apply] using h

end FiniteAbelian

/-- Exact count of nontrivial characters of Z/p. -/
theorem nontrivial_card (p : ℕ) [NeZero p] :
    Fintype.card {ψ : AddChar (ZMod p) ℂ // ψ≠0}=p-1 := by
  classical
  simpa only [Fintype.card_subtype_eq,AddChar.card_eq,ZMod.card] using
    Fintype.card_subtype_compl (fun ψ : AddChar (ZMod p) ℂ=>ψ=0)

noncomputable def characterEquiv (p : ℕ) [NeZero p] :
    Fin (p-1)≃{ψ : AddChar (ZMod p) ℂ // ψ≠0} :=
  (finCongr (nontrivial_card p).symm).trans
    (Fintype.equivFin {ψ : AddChar (ZMod p) ℂ // ψ≠0}).symm

noncomputable def characters (p : ℕ) [NeZero p] (i : Fin (p-1)) : AddChar (ZMod p) ℂ :=
  (characterEquiv p i).1

theorem characters_nontrivial (p : ℕ) [NeZero p] (i : Fin (p-1)) : characters p i≠0 :=
  (characterEquiv p i).2

noncomputable def coordinates (p : ℕ) [NeZero p] (f : ZMod p→ℂ) : Fin (p-1)→ℂ :=
  fun i=>coefficient (ZMod p) f (characters p i)

theorem coordinates_continuous (p : ℕ) [NeZero p] : Continuous (coordinates p) :=
  continuous_pi (fun i=>coefficient_continuous (ZMod p) (characters p i))

theorem coordinates_nonzero (p : ℕ) [NeZero p] {f : ZMod p→ℂ}
    (hCenter : ∑g : ZMod p,f g=0) (hNonzero : f≠0) : coordinates p f≠0 := by
  intro hZero
  apply nontrivial_coordinates_nonzero (ZMod p) hCenter hNonzero
  funext ψ
  have h:=congrFun hZero ((characterEquiv p).symm ψ)
  simpa only [coordinates,characters,Equiv.apply_symm_apply,Pi.zero_apply] using h

theorem coordinates_translate (p : ℕ) [NeZero p] (a : ZMod p) (f : ZMod p→ℂ) :
    coordinates p (complexRegularTranslate a f)=
      fun i=>characters p i (-a)*coordinates p f i := by
  funext i
  exact coefficient_translate (ZMod p) a f (characters p i)

end FairDivision.Topology.Volovikov.CyclicRegularCharacterCoordinates
