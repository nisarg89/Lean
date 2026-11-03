import FairDivision.Topology.Volovikov.OddPrimeTensorDifferential
import RequestProject.Dvoretzky.Dold.Main

/-!
# Actual signed source family for elementary abelian p-groups

The source is the existing ordered-chain model of the N-fold group join.
For every tensor multi-index I we cone its signed periodic differential
to the next source color. The square-zero theorem proves the coned chain
is a cycle. This constructs, rather than assumes, the augmented family
with defect one for every prime and every rank.

Odd signs are retained throughout. This is the source half of the general
odd-prime obstruction; target character-circle peeling is still separate.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.Volovikov.OddPrimeTensorSource

open scoped BigOperators
open Dvoretzky Dvoretzky.Dold OddPrimeTensorDifferential

abbrev Group (p r : ℕ):=Multiplicative (Fin r→ZMod p)

def generator {p r : ℕ} (q : Fin r) : Group p r:=Multiplicative.ofAdd (Pi.single q 1)

theorem generator_pow (p r : ℕ) [Fact p.Prime] (q : Fin r) :
    (generator (p:=p) q)^p=1 := by
  apply Multiplicative.toAdd.injective
  simp only [generator,toAdd_pow,toAdd_ofAdd,toAdd_one]
  funext j
  by_cases h : j=q
  · subst j
    simp [Pi.single_apply,nsmul_eq_mul]
  · simp [Pi.single_apply,h]

variable (p r N : ℕ) [Fact p.Prime]

abbrev SourceChain:=Chain (ZMod p) (Fin N→Group p r→ℝ)

def T (q : Fin r) : Module.End (ZMod p) (SourceChain p r N):=
  actL (joinAct (generator (p:=p) q))

theorem T_pow (q : Fin r) : (T p r N q)^p=1 := by
  have hPow (n : ℕ) (c : SourceChain p r N) :
      ((T p r N q)^n) c=actL (joinAct ((generator (p:=p) q)^n)) c := by
    induction n with
    | zero => simp [joinAct_one',actL_id]
    | succ n ih =>
        rw [pow_succ',Module.End.mul_apply,ih,T,actL_comp]
        congr 2
        funext x
        simp [joinAct_mul',pow_succ']
  apply LinearMap.ext
  intro c
  rw [hPow,generator_pow,joinAct_one',actL_id]
  rfl

theorem T_commute (q k : Fin r) : Commute (T p r N q) (T p r N k) := by
  apply LinearMap.ext
  intro c
  simp only [Module.End.mul_apply,T,actL_comp]
  congr 2
  funext x
  simp [joinAct_mul',mul_comm]

theorem boundary_commute (q : Fin r) :
    Commute (bd : Module.End (ZMod p) (SourceChain p r N)) (T p r N q) :=
  LinearMap.ext (fun c=>(actL_bd _ c).symm)

def empty : SourceChain p r N:=Finsupp.single [] 1

@[simp] theorem T_empty (q : Fin r) : T p r N q (empty p r N)=empty p r N := by
  simp [T,empty]

/-- Every periodic operator kills the augmentation simplex. The norm
case uses p=0 in the actual Z/p coefficients, not a mod-two shortcut. -/
theorem operator_empty (I : Fin r→₀ℕ) (q : Fin r) :
    operator p (T p r N) I q (empty p r N)=0 := by
  have hPow (n : ℕ) : ((T p r N q)^n) (empty p r N)=empty p r N := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ',Module.End.mul_apply,ih,T_empty]
  unfold operator
  split_ifs
  · rw [normOp_apply]
    simp only [hPow,Finset.sum_const,Finset.card_range]
    rw [←Nat.cast_smul_eq_nsmul (ZMod p),ZMod.natCast_self,zero_smul]
  · simp only [LinearMap.sub_apply,Module.End.one_apply,T_empty,sub_self]

/-- The delta augmentation contributes zero to the tensor differential. -/
theorem differential_augmentation (I : Fin r→₀ℕ) :
    differential p (T p r N)
      (fun J=>if J=0 then empty p r N else 0) I=0 := by
  apply Finset.sum_eq_zero
  intro q hq
  by_cases hZero : I q=0
  · simp only [step,hZero,ite_true]
  · simp only [step,hZero,ite_false]
    by_cases hAug : I-Finsupp.single q 1=0
    · simp only [hAug,ite_true,operator_empty,smul_zero]
    · simp only [hAug,ite_false,map_zero,smul_zero]

/-- Literal cone recursion; the source color is the total tensor degree. -/
def auxiliary : ℕ→(Fin r→₀ℕ)→SourceChain p r N
  | 0,_=>Finsupp.single [vtxPt N 0 1] 1
  | n+1,I=>appL (vtxPt N (n+1) 1)
      (sgnL (differential p (T p r N) (auxiliary n) I))

def family (I : Fin r→₀ℕ) : SourceChain p r N:=auxiliary p r N (Finsupp.degree I) I

theorem family_succ {n : ℕ} {I : Fin r→₀ℕ} (hI : Finsupp.degree I=n+1) :
    family p r N I=appL (vtxPt N (n+1) 1)
      (sgnL (differential p (T p r N) (family p r N) I)) := by
  rw [family,hI,auxiliary]
  congr 2
  apply differential_congr_degree
    (p:=p) (T:=T p r N) (n:=n) (I:=I)
  · intro J hJ
    simp only [family,hJ]
  · exact hI

/-- Complete augmented boundary relation of the actual source family. -/
theorem boundary_family : ∀(n : ℕ)(I : Fin r→₀ℕ),Finsupp.degree I=n→
    bd (family p r N I)=
      (if I=0 then empty p r N else 0)+
        differential p (T p r N) (family p r N) I
  | 0,I,hI=>by
      have hZero : I=0 := (Finsupp.degree_eq_zero_iff I).mp hI
      subst I
      simp [family,auxiliary,empty,differential,step,bdList_cons]
  | n+1,I,hI=>by
      have hNonzero : I≠0 := by intro h;subst I;simp at hI
      rw [if_neg hNonzero,zero_add,family_succ p r N hI,bd_appL,bd_sgnL,sgnL_sgnL]
      have hCycle : bd (differential p (T p r N) (family p r N) I)=0 := by
        rw [differential_map p (T p r N) bd (boundary_commute p r N)]
        have hReplace : differential p (T p r N)
            (fun J=>bd (family p r N J)) I=
          differential p (T p r N)
            (fun J=>(if J=0 then empty p r N else 0)+
              differential p (T p r N) (family p r N) J) I := by
          apply differential_congr_degree (n:=n) (I:=I)
          · intro J hJ
            exact boundary_family n J hJ
          · exact hI
        rw [hReplace,differential_add,differential_augmentation,
          differential_square_zero p (T p r N) (T_pow p r N) (T_commute p r N)]
        simp
      rw [hCycle,map_zero,neg_zero,map_zero,zero_add]

end FairDivision.Topology.Volovikov.OddPrimeTensorSource
