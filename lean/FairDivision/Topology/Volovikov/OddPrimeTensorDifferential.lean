import RequestProject.Dvoretzky.Dold.Algebra
import RequestProject.Dvoretzky.Dold.JoinChains
import Mathlib.Data.Finsupp.Order
import Mathlib.Tactic

/-!
# Signed tensor differential of the cyclic periodic resolutions

For r commuting operators T_q with T_q^p=1, the q-th tensor differential
alternates between 1−T_q in odd coordinate degree and its cyclic norm in
even coordinate degree. The Koszul sign is (-1) to the sum of the earlier
coordinate degrees. This file proves the ACTUAL multi-index formula
squares to zero, including every odd-prime sign.

The cyclic norm/difference identities and signed double-sum cancellation
are reused from the pinned Dvoretzky Dold source. Nothing here asserts an
Euler-class identification or the unresolved general odd-rank no-map
conclusion. The algebra works over any commutative coefficient ring.
-/

set_option autoImplicit false

namespace FairDivision.Topology.Volovikov.OddPrimeTensorDifferential

open scoped BigOperators
open Dvoretzky.Dold

variable {r : ℕ}

/-- Tensor factors are ordered by their actual finite coordinate index. -/
def prefixDegree (q : Fin r) (I : Fin r→₀ℕ) : ℕ :=
  ∑j∈Finset.univ.filter (fun j : Fin r=>j<q),I j

@[simp] theorem prefixDegree_add (q : Fin r) (I J : Fin r→₀ℕ) :
    prefixDegree q (I+J)=prefixDegree q I+prefixDegree q J := by
  simp [prefixDegree,Finset.sum_add_distrib]

@[simp] theorem prefixDegree_single (q k : Fin r) :
    prefixDegree q (Finsupp.single k 1)=if k<q then 1 else 0 := by
  classical
  unfold prefixDegree
  by_cases hk : k<q
  · rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro j hj hne
      simp [hne]
    · intro h
      exact (h (by simp [hk])).elim
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro j hj
    have hne : j≠k := by
      intro h
      subst j
      exact hk (Finset.mem_filter.mp hj).2
    simp [hne]

/-- Removing an existing coordinate lowers exactly the later prefix
counts. This is an equality of natural degrees, before taking signs. -/
theorem prefixDegree_remove (q k : Fin r) (I : Fin r→₀ℕ) (hk : I k≠0) :
    prefixDegree q (I-Finsupp.single k 1)+(if k<q then 1 else 0)=prefixDegree q I := by
  have hle : Finsupp.single k 1≤I := by
    intro j
    by_cases h : j=k
    · subst j
      simp only [Finsupp.single_eq_same]
      omega
    · simp [h]
  calc
    _=prefixDegree q ((I-Finsupp.single k 1)+Finsupp.single k 1) := by simp
    _=prefixDegree q I := by rw [tsub_add_cancel_of_le hle]

section Coefficients

variable {R : Type*} [CommRing R]

def sign (q : Fin r) (I : Fin r→₀ℕ) : R := (-1)^prefixDegree q I

theorem sign_remove (q k : Fin r) (I : Fin r→₀ℕ) (hk : I k≠0) :
    sign (R:=R) q (I-Finsupp.single k 1)=
      if k<q then -sign q I else sign q I := by
  have hPrefix:=prefixDegree_remove q k I hk
  by_cases h : k<q
  · simp only [h,if_true] at hPrefix ⊢
    unfold sign
    rw [←hPrefix,pow_succ]
    ring
  · simp only [h,if_false,Nat.add_zero] at hPrefix ⊢
    exact congrArg (fun n=>(-1 : R)^n) hPrefix

/-- The two off-diagonal tensor paths have opposite actual signs. -/
theorem sign_cross (q k : Fin r) (hne : q≠k) (I : Fin r→₀ℕ)
    (hq : I q≠0) (hk : I k≠0) :
    sign (R:=R) q I*sign k (I-Finsupp.single q 1)=
      -(sign k I*sign q (I-Finsupp.single k 1)) := by
  rw [sign_remove k q I hq,sign_remove q k I hk]
  rcases lt_or_gt_of_ne hne with h|h
  · simp only [h,not_lt_of_ge h.le,if_true,if_false]
    ring
  · simp only [h,not_lt_of_ge h.le,if_true,if_false]
    ring

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- The coefficient differential uses the CURRENT coordinate degree, so
its odd case is 1−T and its positive even case is the cyclic norm. -/
def operator (p : ℕ) (T : Fin r→Module.End R M) (I : Fin r→₀ℕ) (q : Fin r) :
    Module.End R M :=
  if Even (I q) then normOp (T q) p else 1-T q

theorem operator_remove_other (p : ℕ) (T : Fin r→Module.End R M)
    (I : Fin r→₀ℕ) (q k : Fin r) (hne : q≠k) :
    operator p T (I-Finsupp.single k 1) q=operator p T I q := by
  simp [operator,Finsupp.tsub_apply,Finsupp.single_apply,hne,Ne.symm hne]

/-- The two consecutive differentials in one periodic factor compose to
zero, by the already imported telescoping cyclic-norm identities. -/
theorem operator_consecutive (p : ℕ) (T : Fin r→Module.End R M)
    (hOrder : ∀q,(T q)^p=1) (I : Fin r→₀ℕ) (q : Fin r) (hq : I q≠0) :
    operator p T I q*operator p T (I-Finsupp.single q 1) q=0 := by
  obtain ⟨n,hn⟩:=Nat.exists_eq_succ_of_ne_zero hq
  by_cases hEven : Even n
  · have hOdd : ¬Even (n+1) := by simpa only [Nat.even_add_one,not_not] using hEven
    simp only [operator,hn,Finsupp.tsub_apply,Finsupp.single_eq_same,
      Nat.succ_sub_one,hEven,hOdd,if_true,if_false]
    exact sub_mul_normOp (T q) p (hOrder q)
  · have hEvenSucc : Even (n+1) := by simpa only [Nat.even_add_one] using hEven
    simp only [operator,hn,Finsupp.tsub_apply,Finsupp.single_eq_same,
      Nat.succ_sub_one,hEven,hEvenSucc,if_true,if_false]
    exact normOp_mul_sub (T q) p (hOrder q)

/-- Any two factor operators commute; norms are finite sums of powers of
the same already-commuting group operators. -/
theorem operator_commute (p : ℕ) (T : Fin r→Module.End R M)
    (hCommute : ∀q k,Commute (T q) (T k))
    (I J : Fin r→₀ℕ) (q k : Fin r) :
    Commute (operator p T I q) (operator p T J k) := by
  have hNT : Commute (normOp (T q) p) (T k) := by
    unfold normOp
    exact Commute.sum_left _ _ _ (fun i hi=>(hCommute q k).pow_left i)
  have hTN : Commute (T q) (normOp (T k) p) := by
    unfold normOp
    exact Commute.sum_right _ _ _ (fun i hi=>(hCommute q k).pow_right i)
  have hNN : Commute (normOp (T q) p) (normOp (T k) p) := by
    unfold normOp
    exact Commute.sum_right _ _ _ (fun i hi=>hNT.pow_right i)
  unfold operator
  split_ifs
  · exact hNN
  · exact (Commute.one_right _).sub_right hNT
  · exact (Commute.one_left _).sub_left hTN
  · exact (Commute.one_left _).sub_left ((Commute.one_right _).sub_right (hCommute q k))

/-- One signed direction of the actual multi-index differential. -/
noncomputable def step (p : ℕ) (T : Fin r→Module.End R M)
    (q : Fin r) (f : (Fin r→₀ℕ)→M) (I : Fin r→₀ℕ) : M :=
  if I q=0 then 0 else
    sign (R:=R) q I•operator p T I q (f (I-Finsupp.single q 1))

noncomputable def differential (p : ℕ) (T : Fin r→Module.End R M)
    (f : (Fin r→₀ℕ)→M) (I : Fin r→₀ℕ) : M := ∑q : Fin r,step p T q f I

@[simp] theorem step_zero (p : ℕ) (T : Fin r→Module.End R M)
    (q : Fin r) (I : Fin r→₀ℕ) : step p T q (fun _=>0) I=0 := by
  simp [step]

theorem step_sum {ι : Type*} (s : Finset ι) (p : ℕ) (T : Fin r→Module.End R M)
    (q : Fin r) (f : ι→(Fin r→₀ℕ)→M) (I : Fin r→₀ℕ) :
    step p T q (fun J=>∑i∈s,f i J) I=∑i∈s,step p T q (f i) I := by
  unfold step
  split_ifs <;> simp [map_sum,Finset.smul_sum]

theorem step_add (p : ℕ) (T : Fin r→Module.End R M)
    (q : Fin r) (f g : (Fin r→₀ℕ)→M) (I : Fin r→₀ℕ) :
    step p T q (fun J=>f J+g J) I=step p T q f I+step p T q g I := by
  unfold step
  split_ifs <;> simp [map_add,smul_add]

theorem differential_add (p : ℕ) (T : Fin r→Module.End R M)
    (f g : (Fin r→₀ℕ)→M) (I : Fin r→₀ℕ) :
    differential p T (fun J=>f J+g J) I=
      differential p T f I+differential p T g I := by
  simp only [differential,step_add,Finset.sum_add_distrib]

theorem degree_remove (q : Fin r) (I : Fin r→₀ℕ) (hq : I q≠0) :
    Finsupp.degree (I-Finsupp.single q 1)+1=Finsupp.degree I := by
  have hle : Finsupp.single q 1≤I := by
    intro j
    by_cases h : j=q
    · subst j
      simp only [Finsupp.single_eq_same]
      omega
    · simp [h]
  conv_rhs=>rw [←tsub_add_cancel_of_le hle]
  rw [map_add,Finsupp.degree_single]

/-- A degree-n input only reads the immediately preceding degree. -/
theorem differential_congr_degree (p : ℕ) (T : Fin r→Module.End R M)
    {n : ℕ} {f g : (Fin r→₀ℕ)→M}
    (h : ∀J,Finsupp.degree J=n→f J=g J)
    {I : Fin r→₀ℕ} (hI : Finsupp.degree I=n+1) :
    differential p T f I=differential p T g I := by
  apply Finset.sum_congr rfl
  intro q hq
  unfold step
  split_ifs with hZero
  · rfl
  · rw [h _ (by have hDegree:=degree_remove q I hZero;omega)]

/-- A boundary commuting with each group generator commutes with every
periodic factor operator, including its norm case. -/
theorem commute_operator (p : ℕ) (T : Fin r→Module.End R M)
    (d : Module.End R M) (hCommute : ∀q,Commute d (T q))
    (I : Fin r→₀ℕ) (q : Fin r) : Commute d (operator p T I q) := by
  unfold operator
  split_ifs
  · unfold normOp
    exact Commute.sum_right _ _ _ (fun i hi=>(hCommute q).pow_right i)
  · exact (Commute.one_right _).sub_right (hCommute q)

theorem differential_map (p : ℕ) (T : Fin r→Module.End R M)
    (d : Module.End R M) (hCommute : ∀q,Commute d (T q))
    (f : (Fin r→₀ℕ)→M) (I : Fin r→₀ℕ) :
    d (differential p T f I)=differential p T (fun J=>d (f J)) I := by
  unfold differential
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q hq
  unfold step
  split_ifs
  · simp
  · rw [map_smul]
    congr 1
    exact LinearMap.congr_fun (commute_operator p T d hCommute I q).eq _

/-- Repeating one factor direction gives zero, including coordinate
sizes zero and one where an inner step is already absent. -/
theorem step_step_self (p : ℕ) (T : Fin r→Module.End R M)
    (hOrder : ∀q,(T q)^p=1) (q : Fin r)
    (f : (Fin r→₀ℕ)→M) (I : Fin r→₀ℕ) :
    step p T q (step p T q f) I=0 := by
  unfold step
  split_ifs with hq hq'
  · rfl
  · simp
  · rw [map_smul,smul_smul,←Module.End.mul_apply,operator_consecutive p T hOrder I q hq]
    simp

/-- Off-diagonal tensor directions anticommute, including the guards
which omit nonexistent negative coordinate degrees. -/
theorem step_step_antisymmetric (p : ℕ) (T : Fin r→Module.End R M)
    (hCommute : ∀q k,Commute (T q) (T k))
    (q k : Fin r) (hne : q≠k) (f : (Fin r→₀ℕ)→M) (I : Fin r→₀ℕ) :
    step p T q (step p T k f) I= -step p T k (step p T q f) I := by
  have hqk : (I-Finsupp.single q 1 : Fin r→₀ℕ) k=I k := by
    simp [Finsupp.tsub_apply,Finsupp.single_apply,hne.symm]
  have hkq : (I-Finsupp.single k 1 : Fin r→₀ℕ) q=I q := by
    simp [Finsupp.tsub_apply,Finsupp.single_apply,hne]
  by_cases hq : I q=0
  · simp [step,hq,hkq]
  by_cases hk : I k=0
  · simp [step,hk,hqk]
  simp only [step,hq,hk,hqk,hkq,if_false,map_smul,smul_smul,
    operator_remove_other p T I k q hne.symm,
    operator_remove_other p T I q k hne]
  rw [sign_cross q k hne I hq hk]
  rw [tsub_right_comm (a:=I) (b:=Finsupp.single q 1) (c:=Finsupp.single k 1)]
  rw [←Module.End.mul_apply,(operator_commute p T hCommute I I q k).eq,
    Module.End.mul_apply,neg_smul]

/-- The signed tensor-periodic differential squares to zero. This is the
actual odd-prime source-resolution algebra, not a presumed chain law. -/
theorem differential_square_zero (p : ℕ) (T : Fin r→Module.End R M)
    (hOrder : ∀q,(T q)^p=1) (hCommute : ∀q k,Commute (T q) (T k))
    (f : (Fin r→₀ℕ)→M) (I : Fin r→₀ℕ) :
    differential p T (differential p T f) I=0 := by
  unfold differential
  simp only [step_sum]
  apply Dvoretzky.Dold.sum_antisymm
  · intro q k
    by_cases h : q=k
    · subst k
      rw [step_step_self p T hOrder]
      simp
    · exact step_step_antisymmetric p T hCommute k q (Ne.symm h) f I
  · intro q
    exact step_step_self p T hOrder q f I

end Coefficients

end FairDivision.Topology.Volovikov.OddPrimeTensorDifferential
