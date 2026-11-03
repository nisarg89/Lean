import FairDivision.Topology.Volovikov.OddPrimeTensorDifferential
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Polynomial.Eval.Algebra
import Mathlib.Algebra.Ring.GeomSum

/-!
# Actual shifted cyclic operators in characteristic p

For commuting p-periodic endomorphisms T_q and arbitrary scalar weights
λ_q, u=Σ λ_q(T_q−1) satisfies u^p=0. Therefore S=1+u is p-periodic.
Its cyclic norm is exactly u^(p−1). These are the actual shifted-cyclic
operators used by the generic coefficient proof route, not an assumed
cyclic action or a characteristic-class statement.

Commuting Frobenius is imported from mathlib. The norm identity is first
proved as a polynomial identity, where cancellation is legitimate, and
then evaluated in the possibly noncommutative endomorphism ring. No
cancellation of a nilpotent endomorphism is used.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov.ShiftedCyclicAlgebra

open scoped BigOperators
open Dvoretzky.Dold

section Ring

variable (p : ℕ) [Fact p.Prime] {A : Type*} [Ring A] [CharP A p]

/-- Frobenius for a finite sum of pairwise commuting ring elements. -/
theorem sum_pow_zero {ι : Type*} (s : Finset ι) (f : ι→A)
    (hCommute : ∀i∈s,∀j∈s,Commute (f i) (f j))
    (hZero : ∀i∈s,(f i)^p=0) : (∑i∈s,f i)^p=0 := by
  classical
  revert hCommute hZero
  induction s using Finset.induction_on with
  | empty=>intro hCommute hZero;simp [(Fact.out : p.Prime).ne_zero]
  | @insert a s ha ih=>
      intro hCommute hZero
      have hC : Commute (f a) (∑i∈s,f i) :=
        Commute.sum_right _ _ _ (fun i hi=>hCommute a
          (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi))
      rw [Finset.sum_insert ha,add_pow_char_of_commute p hC,
        hZero a (Finset.mem_insert_self a s)]
      rw [ih (fun i hi j hj=>hCommute i (Finset.mem_insert_of_mem hi)
        j (Finset.mem_insert_of_mem hj))
        (fun i hi=>hZero i (Finset.mem_insert_of_mem hi))]
      simp

end Ring

section Endomorphisms

variable (p : ℕ) [Fact p.Prime] {K M : Type*} [Field K] [CharP K p]
    [AddCommGroup M] [Module K M] [Nontrivial M]

private theorem end_char : CharP (Module.End K M) p :=
  CharP.of_ringHom_of_ne_zero (algebraMap K (Module.End K M)) p
    (Fact.out : p.Prime).ne_zero

def displacement {ι : Type*} [Fintype ι] («λ» : ι→K)
    (T : ι→Module.End K M) : Module.End K M := ∑q : ι,«λ» q•(T q-1)

def shifted {ι : Type*} [Fintype ι] («λ» : ι→K)
    (T : ι→Module.End K M) : Module.End K M := 1+displacement «λ» T

/-- The actual generic displacement is p-nilpotent for arbitrary scalar
weights; no nonvanishing assumption on a chosen coefficient is required. -/
theorem displacement_pow {ι : Type*} [Fintype ι] («λ» : ι→K)
    (T : ι→Module.End K M) (hOrder : ∀q,(T q)^p=1)
    (hCommute : ∀q k,Commute (T q) (T k)) : (displacement «λ» T)^p=0 := by
  letI:=end_char p (K:=K) (M:=M)
  apply sum_pow_zero p
  · intro q hq k hk
    exact ((((hCommute q k).sub_right (Commute.one_right _)).sub_left
      (Commute.one_left _)).smul_left («λ» q)).smul_right («λ» k)
  · intro q hq
    rw [smul_pow,sub_pow_char_of_commute p (Commute.one_right _),hOrder q,one_pow,sub_self,smul_zero]

/-- The shifted endomorphism is an actual p-periodic operator. -/
theorem shifted_pow {ι : Type*} [Fintype ι] («λ» : ι→K)
    (T : ι→Module.End K M) (hOrder : ∀q,(T q)^p=1)
    (hCommute : ∀q k,Commute (T q) (T k)) : (shifted «λ» T)^p=1 := by
  letI:=end_char p (K:=K) (M:=M)
  rw [shifted,add_pow_char_of_commute p (Commute.one_left _),
    one_pow,displacement_pow p «λ» T hOrder hCommute,add_zero]

/-- Commutation with all generators passes to the actual shifted cyclic
operator and therefore to its norm and difference. -/
theorem commute_shifted {ι : Type*} [Fintype ι] («λ» : ι→K)
    (T : ι→Module.End K M) (d : Module.End K M)
    (hCommute : ∀q,Commute d (T q)) : Commute d (shifted «λ» T) := by
  apply (Commute.one_right _).add_right
  unfold displacement
  apply Commute.sum_right
  intro q hq
  exact ((hCommute q).sub_right (Commute.one_right _)).smul_right («λ» q)

end Endomorphisms

section NormPolynomial

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p]

/-- Cancellation is performed here only in K[X], where X is nonzero and
is not a zero divisor. -/
theorem norm_one_add_polynomial :
    (∑i∈Finset.range p,(1+Polynomial.X : Polynomial K)^i)=Polynomial.X^(p-1) := by
  have hGeom:=mul_neg_geom_sum (1+Polynomial.X : Polynomial K) p
  rw [add_pow_char,one_pow] at hGeom
  have hProduct : Polynomial.X*(∑i∈Finset.range p,(1+Polynomial.X : Polynomial K)^i)=
      Polynomial.X^p := by
    linear_combination -hGeom
  have hp : 1≤p:=(Fact.out : p.Prime).one_le
  have hPower : (Polynomial.X : Polynomial K)^p=Polynomial.X*Polynomial.X^(p-1) := by
    rw [←pow_succ']
    congr 1
    omega
  exact mul_left_cancel₀ Polynomial.X_ne_zero (hProduct.trans hPower)

/-- Evaluation of the polynomial identity is valid for a noncommutative
K-algebra because its coefficient scalars commute with the evaluation
point. In particular this applies to every actual endomorphism ring. -/
theorem norm_one_add {A : Type*} [Ring A] [Algebra K A] (u : A) :
    (∑i∈Finset.range p,(1+u)^i)=u^(p-1) := by
  let evaluate : Polynomial K→+*A:=Polynomial.eval₂RingHom' (algebraMap K A) u
    (fun a=>Algebra.commute_algebraMap_left a u)
  have hX : evaluate Polynomial.X=u := by
    simp only [evaluate,Polynomial.eval₂RingHom'_apply,Polynomial.eval₂_X]
  have h:=congrArg evaluate (norm_one_add_polynomial p K)
  simpa only [map_sum,map_pow,map_add,map_one,hX] using h

/-- The exact cyclic norm of the actual shifted operator is its
nilpotent displacement to power p−1. -/
theorem shifted_norm {M ι : Type*} [AddCommGroup M] [Module K M]
    [Fintype ι] («λ» : ι→K) (T : ι→Module.End K M) :
    normOp (shifted «λ» T) p=(displacement «λ» T)^(p-1) := by
  exact norm_one_add p K (displacement «λ» T)

end NormPolynomial

end FairDivision.Topology.Volovikov.ShiftedCyclicAlgebra
