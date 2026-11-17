import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# Characters of an elementary abelian group

Mathlib identifies `ZMod p` with its complex character group. We combine
those one-coordinate characters to obtain the usual coefficient-vector
parametrization of characters of `(ZMod p)^r`. This representation bridge
will identify the reduced regular representation's character summands with
the nonzero linear forms in the eventual Euler-class calculation.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov

open scoped BigOperators

/-- The complex character of `(ZMod p)^r` determined by a coefficient vector. -/
noncomputable def elementaryAbelianCharacter
    (p r : ℕ) [NeZero p] (a : Fin r → ZMod p) :
    AddChar (Fin r → ZMod p) ℂ :=
  ∑ i : Fin r,
    (AddChar.zmodAddEquiv (a i)).compAddMonoidHom
      (Pi.evalAddMonoidHom (fun _ : Fin r => ZMod p) i)

/-- Evaluation is the product of the one-coordinate character values. -/
theorem elementaryAbelianCharacter_apply
    (p r : ℕ) [NeZero p] (a x : Fin r → ZMod p) :
    elementaryAbelianCharacter p r a x =
      ∏ i : Fin r, (AddChar.zmodAddEquiv (a i)) (x i) := by
  simp [elementaryAbelianCharacter, AddChar.sum_apply]

/-- The zero coefficient vector gives the trivial character. -/
theorem elementaryAbelianCharacter_zero
    (p r : ℕ) [NeZero p] :
    elementaryAbelianCharacter p r (0 : Fin r → ZMod p) = 0 := by
  apply DFunLike.ext
  intro x
  rw [elementaryAbelianCharacter_apply]
  simp only [Pi.zero_apply, map_zero, AddChar.zero_apply, Finset.prod_const_one]

/-- Adding coefficient vectors multiplies their characters. -/
theorem elementaryAbelianCharacter_add
    (p r : ℕ) [NeZero p] (a b : Fin r → ZMod p) :
    elementaryAbelianCharacter p r (a + b) =
      elementaryAbelianCharacter p r a +
        elementaryAbelianCharacter p r b := by
  apply DFunLike.ext
  intro x
  simp only [elementaryAbelianCharacter_apply, Pi.add_apply]
  have hchar (i : Fin r) :
      AddChar.zmodAddEquiv (a i + b i) =
        AddChar.zmodAddEquiv (a i) + AddChar.zmodAddEquiv (b i) :=
    (AddChar.zmodAddEquiv : ZMod p ≃+ AddChar (ZMod p) ℂ).map_add (a i) (b i)
  simp_rw [hchar, AddChar.add_apply]
  rw [Finset.prod_mul_distrib]
  simp only [elementaryAbelianCharacter_apply]


/-- A character of `ZMod p` is determined by its value at the generator `1`. -/
theorem zmodCharacter_eval_one_injective
    (p : ℕ) [NeZero p] :
    Function.Injective
      (fun a : ZMod p => (AddChar.zmodAddEquiv a) (1 : ZMod p)) := by
  intro a b hab
  apply (AddChar.zmodAddEquiv : ZMod p ≃+ AddChar (ZMod p) ℂ).injective
  apply DFunLike.ext
  intro x
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  calc
    (AddChar.zmodAddEquiv a) (k : ZMod p) =
        (AddChar.zmodAddEquiv a) (k • (1 : ZMod p)) := by rw [zsmul_one]
    _ = ((AddChar.zmodAddEquiv a) (1 : ZMod p)) ^ k :=
      AddChar.map_zsmul_eq_zpow _ k _
    _ = ((AddChar.zmodAddEquiv b) (1 : ZMod p)) ^ k :=
      congrArg (fun z : ℂ => z ^ k) hab
    _ = (AddChar.zmodAddEquiv b) (k • (1 : ZMod p)) :=
      (AddChar.map_zsmul_eq_zpow _ k _).symm
    _ = (AddChar.zmodAddEquiv b) (k : ZMod p) := by rw [zsmul_one]

/-- A one-coordinate test point recovers that coordinate's character value. -/
theorem elementaryAbelianCharacter_apply_single
    (p r : ℕ) [NeZero p]
    (a : Fin r → ZMod p) (i : Fin r) :
    elementaryAbelianCharacter p r a (Pi.single i (1 : ZMod p)) =
      (AddChar.zmodAddEquiv (a i)) (1 : ZMod p) := by
  classical
  rw [elementaryAbelianCharacter_apply]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j hj hji
    simp [Pi.single_eq_of_ne hji]
  · simp

/-- Distinct coefficient vectors give distinct complex characters. -/
theorem elementaryAbelianCharacter_injective
    (p r : ℕ) [NeZero p] :
    Function.Injective (elementaryAbelianCharacter p r) := by
  intro a b hab
  funext i
  apply zmodCharacter_eval_one_injective p
  have hi := congrArg
    (fun ψ : AddChar (Fin r → ZMod p) ℂ =>
      ψ (Pi.single i (1 : ZMod p))) hab
  simpa only [elementaryAbelianCharacter_apply_single] using hi


/-- Coefficient vectors index all complex characters of the elementary
abelian group. Surjectivity follows from Mathlib's character-count theorem. -/
noncomputable def elementaryAbelianCharacterEquiv
    (p r : ℕ) [NeZero p] :
    (Fin r → ZMod p) ≃+ AddChar (Fin r → ZMod p) ℂ := by
  let f : (Fin r → ZMod p) →+ AddChar (Fin r → ZMod p) ℂ :=
    { toFun := elementaryAbelianCharacter p r
      map_zero' := elementaryAbelianCharacter_zero p r
      map_add' := elementaryAbelianCharacter_add p r }
  have hcard : Fintype.card (Fin r → ZMod p) =
      Fintype.card (AddChar (Fin r → ZMod p) ℂ) :=
    (AddChar.card_eq (α := Fin r → ZMod p)).symm
  have hf : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2
      ⟨elementaryAbelianCharacter_injective p r, hcard⟩
  exact AddEquiv.ofBijective f hf

@[simp] theorem elementaryAbelianCharacterEquiv_apply
    (p r : ℕ) [NeZero p] (a : Fin r → ZMod p) :
    elementaryAbelianCharacterEquiv p r a =
      elementaryAbelianCharacter p r a := rfl

end FairDivision.Topology.Volovikov
