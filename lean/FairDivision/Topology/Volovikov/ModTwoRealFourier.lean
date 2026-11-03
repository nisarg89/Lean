import FairDivision.Topology.Volovikov.RegularCharacterEigenvectors
import Mathlib.Algebra.Group.Translate
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic

/-!
# Real Fourier coordinates for an elementary abelian two-group

Mathlib's full complex character basis supplies injectivity. Every character
of an exponent-two group is real and takes values in {1,-1}; consequently
its real Fourier coefficient transforms by that same sign. On the centered
subspace, the nontrivial coordinates alone detect zero. These concrete
coordinates feed the imported character-join obstruction.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov.ModTwoRealFourier

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Exponent two is the only group property needed in this Fourier bridge. -/
def HasExponentTwo (G : Type*) [AddCommGroup G] : Prop := ∀ a : G, a+a=0

theorem character_eq_one_or_neg_one (hTwo : HasExponentTwo G)
    (ψ : AddChar G ℂ) (a : G) : ψ a=1 ∨ ψ a= -1 := by
  apply mul_self_eq_one_iff.mp
  rw [←ψ.map_add_eq_mul,hTwo a,ψ.map_zero_eq_one]

theorem character_im_eq_zero (hTwo : HasExponentTwo G)
    (ψ : AddChar G ℂ) (a : G) : (ψ a).im=0 := by
  rcases character_eq_one_or_neg_one hTwo ψ a with h|h <;> simp [h]

theorem character_re_cast (hTwo : HasExponentTwo G)
    (ψ : AddChar G ℂ) (a : G) : ((ψ a).re : ℂ)=ψ a := by
  apply Complex.ext
  · simp
  · simp [character_im_eq_zero hTwo ψ a]

/-- The real sign representation attached to a complex character. -/
noncomputable def realCharacter (hTwo : HasExponentTwo G) (ψ : AddChar G ℂ) : AddChar G ℝ where
  toFun a := (ψ a).re
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    rw [ψ.map_add_eq_mul,Complex.mul_re]
    simp [character_im_eq_zero hTwo ψ a,character_im_eq_zero hTwo ψ b]

@[simp] theorem realCharacter_apply (hTwo : HasExponentTwo G)
    (ψ : AddChar G ℂ) (a : G) : realCharacter hTwo ψ a=(ψ a).re := rfl

theorem realCharacter_sign (hTwo : HasExponentTwo G) (ψ : AddChar G ℂ) (a : G) :
    realCharacter hTwo ψ a=1 ∨ realCharacter hTwo ψ a= -1 := by
  rcases character_eq_one_or_neg_one hTwo ψ a with h|h
  · left; simp [realCharacter,h]
  · right; simp [realCharacter,h]

/-- Unnormalized real Fourier coefficient. A positive common normalization
is unnecessary for detecting zero or identifying the character action. -/
noncomputable def coefficient (ψ : AddChar G ℂ) (f : G → ℝ) : ℝ :=
  ∑ a : G, (ψ a).re*f a

theorem continuous_coefficient (ψ : AddChar G ℂ) : Continuous (coefficient ψ) := by
  unfold coefficient
  exact continuous_finset_sum _ (fun a _ => continuous_const.mul (continuous_apply a))

theorem coefficient_cast (hTwo : HasExponentTwo G) (ψ : AddChar G ℂ) (f : G → ℝ) :
    (coefficient ψ f : ℂ)=∑ a : G, ψ a*(f a : ℂ) := by
  unfold coefficient
  push_cast
  simp only [character_re_cast hTwo ψ]

theorem coefficient_translate (hTwo : HasExponentTwo G) (ψ : AddChar G ℂ)
    (b : G) (f : G → ℝ) :
    coefficient ψ (fun a => f (a-b))=realCharacter hTwo ψ b*coefficient ψ f := by
  let h : G → ℝ := fun a => realCharacter hTwo ψ (a+b)*f a
  calc
    coefficient ψ (fun a => f (a-b)) = ∑ a : G, translate b h a := by
      simp [coefficient,translate,h,realCharacter]
    _ = ∑ a : G, h a := sum_translate b h
    _ = realCharacter hTwo ψ b*coefficient ψ f := by
      simp only [h,(realCharacter hTwo ψ).map_add_eq_mul,coefficient]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      simp only [realCharacter_apply]
      ring

/-- The common trivial Fourier coordinate is the ordinary coordinate sum. -/
@[simp] theorem coefficient_trivial (f : G → ℝ) : coefficient (0 : AddChar G ℂ) f=∑ a,f a := by
  simp [coefficient]

/-- Vanishing of all real Fourier coefficients forces every source entry
to vanish. The proof uses the existing complex character basis. -/
theorem eq_zero_of_coefficients_eq_zero (hTwo : HasExponentTwo G) (f : G → ℝ)
    (h : ∀ ψ : AddChar G ℂ, coefficient ψ f=0) : f=0 := by
  classical
  let L : (G → ℂ) →ₗ[ℂ] ℂ :=
    {toFun := fun u => ∑ a : G,u a*(f a : ℂ)
     map_add' := by intro u v; simp [add_mul,Finset.sum_add_distrib]
     map_smul' := by intro c u; simp [Finset.mul_sum,mul_assoc]}
  have hL : L=0 := by
    apply (AddChar.complexBasis G).ext
    intro ψ
    rw [AddChar.complexBasis_apply]
    change (∑ a : G,ψ a*(f a : ℂ))=0
    rw [←coefficient_cast hTwo ψ f,h ψ]
    simp
  funext a
  have hEval := congrArg (fun T : (G → ℂ) →ₗ[ℂ] ℂ => T (Pi.single a 1)) hL
  have hCast : (f a : ℂ)=0 := by simpa [L,Pi.single_apply] using hEval
  exact_mod_cast hCast

/-- The nontrivial characters suffice on the centered real representation. -/
theorem exists_nonzero_coefficient (hTwo : HasExponentTwo G) (f : G → ℝ)
    (hCenter : ∑ a : G,f a=0) (hNonzero : f≠0) :
    ∃ ψ : {ψ : AddChar G ℂ // ψ≠0}, coefficient ψ.1 f≠0 := by
  classical
  by_contra h
  push_neg at h
  apply hNonzero
  apply eq_zero_of_coefficients_eq_zero hTwo f
  intro ψ
  by_cases hψ : ψ=0
  · simpa [hψ] using hCenter
  · exact h ⟨ψ,hψ⟩

/-- Encode a sign character as an additive F₂-valued character. -/
noncomputable def characterBit (hTwo : HasExponentTwo G) (ψ : AddChar G ℂ) : G →+ ZMod 2 := by
  classical
  exact
    {toFun := fun a => if ψ a=1 then (0 : ZMod 2) else 1
     map_zero' := by simp
     map_add' := by
       intro a b
       rw [ψ.map_add_eq_mul]
       rcases character_eq_one_or_neg_one hTwo ψ a with ha|ha <;>
         rcases character_eq_one_or_neg_one hTwo ψ b with hb|hb <;>
         norm_num [ha,hb,show (2 : ZMod 2)=0 from rfl] <;> decide}

@[simp] theorem characterBit_eq_zero_iff (hTwo : HasExponentTwo G) (ψ : AddChar G ℂ) (a : G) :
    characterBit hTwo ψ a=0 ↔ ψ a=1 := by
  classical
  by_cases h : ψ a=1 <;> simp [characterBit,h]

theorem characterBit_ne_zero (hTwo : HasExponentTwo G) (ψ : AddChar G ℂ) (hψ : ψ≠0) :
    characterBit hTwo ψ≠0 := by
  intro h
  apply hψ
  apply DFunLike.ext
  intro a
  have hEval : characterBit hTwo ψ a=0 := by rw [h]; rfl
  simpa using (characterBit_eq_zero_iff hTwo ψ a).mp hEval

theorem realCharacter_eq_bit_sign (hTwo : HasExponentTwo G) (ψ : AddChar G ℂ) (a : G) :
    realCharacter hTwo ψ a = if characterBit hTwo ψ a=0 then 1 else -1 := by
  classical
  simp only [characterBit_eq_zero_iff]
  rcases character_eq_one_or_neg_one hTwo ψ a with h|h
  · simp [realCharacter_apply,h]
  · have hne : ψ a≠1 := by rw [h]; norm_num
    simp [realCharacter_apply,h,hne] <;> norm_num

/-- Every element of the p=2 position group has additive order at most two. -/
theorem elementaryAbelian_exponentTwo (r : ℕ) : HasExponentTwo (Fin r → ZMod 2) := by
  intro a
  funext i
  change a i+a i=0
  rw [←two_mul,show (2 : ZMod 2)=0 from rfl,zero_mul]

/-- Restricting a nonzero F₂ character to the standard generators still
produces a nonzero coefficient vector, as required by the upstream theorem. -/
theorem generator_values_ne_zero {r : ℕ}
    (χ : (Fin r → ZMod 2) →+ ZMod 2) (hχ : χ≠0) :
    (fun i : Fin r => χ (Pi.single i 1))≠0 := by
  classical
  intro h
  apply hχ
  apply AddMonoidHom.ext
  intro a
  rw [pi_eq_sum_univ' a,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  have hi : χ (Pi.single i 1)=0 := congrFun h i
  have ha : a i=0 ∨ a i=1 :=
    (show ∀ x : ZMod 2, x=0 ∨ x=1 from by decide) (a i)
  rcases ha with ha|ha <;> simp [ha,hi]

end FairDivision.Topology.Volovikov.ModTwoRealFourier
