import FairDivision.Topology.Volovikov.ShiftedCyclicAlgebra
import FairDivision.Topology.Volovikov.OddPrimeTensorSource

/-!
# Actual cyclic cone sequence for the generic shifted source action

The generators act by the already defined label translations on ordered
join chains. Their scalar-weighted displacement gives a genuine
p-periodic shifted operator. The classical Dold cone sequence is then
constructed from that actual operator, with its augmentation, boundary,
literal color support, and subdivision commutation all proved.

No pointwise action of a fictitious generic group element is claimed:
the shifted action is a LINEAR combination of genuine translations.
Support preservation is proved term by term. An equivariant chain map
commuting with all genuine generators therefore commutes with this shift.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.Volovikov.ShiftedCyclicSource

open scoped BigOperators
open Dvoretzky Dvoretzky.Dold
open OddPrimeTensorSource (Group generator generator_pow)

variable (p r N : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [CharP K p]

abbrev Point:=Fin N→Group p r→ℝ
abbrev SourceChain:=Chain K (Point p r N)

/-- Genuine label translations, as a representation on ordered chains. -/
def groupAction : Group p r→*Module.End K (SourceChain p r N K) where
  toFun g:=actL (joinAct g)
  map_one':=by
    apply LinearMap.ext
    intro c
    simp only [joinAct_one',actL_id,Module.End.one_apply]
  map_mul' g h:=by
    apply LinearMap.ext
    intro c
    simp only [Module.End.mul_apply,actL_comp]
    congr 2
    funext x
    exact (joinAct_mul' g h x).symm

def generatorAction (q : Fin r) : Module.End K (SourceChain p r N K):=
  groupAction p r N K (generator (p:=p) q)

theorem generatorAction_pow (q : Fin r) : (generatorAction p r N K q)^p=1 := by
  rw [generatorAction,←map_pow,generator_pow,map_one]

theorem generatorAction_commute (q k : Fin r) :
    Commute (generatorAction p r N K q) (generatorAction p r N K k) := by
  change groupAction p r N K _*groupAction p r N K _=
    groupAction p r N K _*groupAction p r N K _
  rw [←map_mul,←map_mul,mul_comm]

variable («λ» : Fin r→K)

/-- The actual shifted cyclic operator, not a group-labelled point map. -/
def shifted : Module.End K (SourceChain p r N K):=
  ShiftedCyclicAlgebra.shifted «λ» (generatorAction p r N K)

theorem shifted_pow : (shifted p r N K «λ»)^p=1 :=
  ShiftedCyclicAlgebra.shifted_pow p «λ» (generatorAction p r N K)
    (generatorAction_pow p r N K) (generatorAction_commute p r N K)

def empty : SourceChain p r N K:=Finsupp.single [] 1

@[simp] theorem generatorAction_empty (q : Fin r) :
    generatorAction p r N K q (empty p r N K)=empty p r N K := by
  simp [generatorAction,groupAction,empty]

@[simp] theorem shifted_empty : shifted p r N K «λ» (empty p r N K)=empty p r N K := by
  simp [shifted,ShiftedCyclicAlgebra.shifted,ShiftedCyclicAlgebra.displacement,
    Module.End.one_apply,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.sum_apply,
    generatorAction_empty]

theorem boundary_shifted :
    Commute (bd : Module.End K (SourceChain p r N K)) (shifted p r N K «λ») := by
  apply ShiftedCyclicAlgebra.commute_shifted
  intro q
  exact LinearMap.ext (fun c=>(actL_bd _ c).symm)

def rho (k : ℕ) : Module.End K (SourceChain p r N K):=
  altOp (normOp (shifted p r N K «λ») p) (1-shifted p r N K «λ») k

theorem boundary_rho (k : ℕ) :
    Commute (bd : Module.End K (SourceChain p r N K)) (rho p r N K «λ» k) := by
  unfold rho altOp
  split_ifs
  · unfold normOp
    exact Commute.sum_right _ _ _ (fun i hi=>(boundary_shifted p r N K «λ»).pow_right i)
  · apply LinearMap.ext
    intro c
    change bd ((1-shifted p r N K «λ») c)=
      (1-shifted p r N K «λ») (bd c)
    simp only [LinearMap.sub_apply,Module.End.one_apply,map_sub]
    have h:=LinearMap.congr_fun (boundary_shifted p r N K «λ»).eq c
    simpa only [Module.End.mul_apply] using congrArg (fun z=>bd c-z) h

theorem rho_consecutive (k : ℕ) : rho p r N K «λ» (k+1)*rho p r N K «λ» k=0 := by
  unfold rho altOp
  by_cases hk : Even k
  · have hSucc : ¬Even (k+1) := by simpa only [Nat.even_add_one,not_not] using hk
    rw [if_neg hSucc,if_pos hk]
    exact sub_mul_normOp _ p (shifted_pow p r N K «λ»)
  · have hSucc : Even (k+1) := by simpa only [Nat.even_add_one] using hk
    rw [if_pos hSucc,if_neg hk]
    exact normOp_mul_sub _ p (shifted_pow p r N K «λ»)

theorem rho_empty : rho p r N K «λ» 0 (empty p r N K)=0 := by
  have hPow (k : ℕ) : ((shifted p r N K «λ»)^k) (empty p r N K)=empty p r N K := by
    induction k with
    | zero=>rfl
    | succ k ih=>rw [pow_succ',Module.End.mul_apply,ih,shifted_empty]
  rw [rho,altOp,if_pos (by decide : Even (0 : ℕ)),normOp_apply]
  simp only [hPow,Finset.sum_const,Finset.card_range]
  rw [←Nat.cast_smul_eq_nsmul K,CharP.cast_eq_zero K p,zero_smul]

/-- The actual classical source cycle-building sequence for the shift. -/
def sequence : ℕ→SourceChain p r N K
  | 0=>Finsupp.single [vtxPt N 0 1] 1
  | k+1=>appL (vtxPt N (k+1) 1) (sgnL (rho p r N K «λ» k (sequence k)))

theorem sequence_succ (k : ℕ) :
    sequence p r N K «λ» (k+1)=
      appL (vtxPt N (k+1) 1)
        (sgnL (rho p r N K «λ» k (sequence p r N K «λ» k))) := rfl

@[simp] theorem boundary_sequence_zero : bd (sequence p r N K «λ» 0)=empty p r N K := by
  simp [sequence,empty,bdList_cons]

theorem boundary_sequence_succ (k : ℕ) :
    bd (sequence p r N K «λ» (k+1))=rho p r N K «λ» k (sequence p r N K «λ» k) := by
  induction k with
  | zero=>
      have hCycle : bd (rho p r N K «λ» 0 (sequence p r N K «λ» 0))=0 := by
        rw [←Module.End.mul_apply,(boundary_rho p r N K «λ» 0).eq,
          Module.End.mul_apply,boundary_sequence_zero,rho_empty]
      rw [sequence_succ,bd_appL,bd_sgnL,hCycle,map_zero,neg_zero,map_zero,zero_add,sgnL_sgnL]
  | succ k ih=>
      have hCycle : bd (rho p r N K «λ» (k+1) (sequence p r N K «λ» (k+1)))=0 := by
        rw [←Module.End.mul_apply,(boundary_rho p r N K «λ» (k+1)).eq,
          Module.End.mul_apply,ih,←Module.End.mul_apply,rho_consecutive,LinearMap.zero_apply]
      rw [sequence_succ,bd_appL,bd_sgnL,hCycle,map_zero,neg_zero,map_zero,zero_add,sgnL_sgnL]

/-- A shifted source step preserves every set of lists invariant under
all genuine generators. This proves support directly for a linear shift. -/
theorem shifted_mem_supported
    {s : Set (List (Point p r N))}
    (hs : ∀q : Fin r,∀l∈s,l.map (joinAct (generator (p:=p) q))∈s)
    {c : SourceChain p r N K} (hc : c∈Finsupp.supported K K s) :
    shifted p r N K «λ» c∈Finsupp.supported K K s := by
  change (1+∑q : Fin r,«λ» q•(generatorAction p r N K q-1)) c∈_
  simp only [LinearMap.add_apply,Module.End.one_apply,LinearMap.sum_apply,LinearMap.smul_apply,
    LinearMap.sub_apply]
  apply Submodule.add_mem _ hc
  apply Submodule.sum_mem
  intro q hq
  apply Submodule.smul_mem
  apply Submodule.sub_mem _ ?_ hc
  apply map_mem_supported (generatorAction p r N K q) _ (fun l hl=>?_) hc
  change actL (joinAct (generator (p:=p) q)) (Finsupp.single l 1)∈
    Finsupp.supported K K s
  rw [actL_single]
  exact Finsupp.single_mem_supported K (1 : K) (hs q l hl)

theorem rho_mem_supported (k : ℕ)
    {s : Set (List (Point p r N))}
    (hs : ∀q : Fin r,∀l∈s,l.map (joinAct (generator (p:=p) q))∈s)
    {c : SourceChain p r N K} (hc : c∈Finsupp.supported K K s) :
    rho p r N K «λ» k c∈Finsupp.supported K K s := by
  have hPow : ∀i : ℕ,((shifted p r N K «λ»)^i) c∈Finsupp.supported K K s := by
    intro i
    induction i with
    | zero=>simpa using hc
    | succ i ih=>rw [pow_succ',Module.End.mul_apply];exact shifted_mem_supported p r N K «λ» hs ih
  unfold rho altOp
  split_ifs
  · rw [normOp_apply]
    exact Submodule.sum_mem _ (fun i hi=>hPow i)
  · simp only [LinearMap.sub_apply,Module.End.one_apply]
    exact Submodule.sub_mem _ hc (shifted_mem_supported p r N K «λ» hs hc)

/-- The sequence in degree k lives on the first k+1 source colors. -/
theorem sequence_supported (k : ℕ) :
    sequence p r N K «λ» k∈Finsupp.supported K K
      {l : List (Point p r N) | VList N k l} := by
  induction k with
  | zero=>exact Finsupp.single_mem_supported _ _ ⟨fun _=>1,by simp [sequence]⟩
  | succ k ih=>
      have h:=rho_mem_supported p r N K «λ» k
        (s:={l : List (Point p r N) | VList N k l})
        (fun q l hl=>VList.map_joinAct hl _) ih
      apply map_mem_supported (appL (vtxPt N (k+1) 1)∘ₗsgnL) _ (fun l hl=>?_) h
      simp only [LinearMap.coe_comp,Function.comp_apply,sgnL_single,mul_one,
        map_smul,appL_single]
      exact Submodule.smul_mem _ _ (Finsupp.single_mem_supported _ _ (VList.append hl))

/-- Every actual generator commutes with barycentric subdivision, hence
so does the weighted shifted operator. -/
theorem subdivision_shifted :
    Commute (sd : Module.End K (SourceChain p r N K)) (shifted p r N K «λ») := by
  apply ShiftedCyclicAlgebra.commute_shifted
  intro q
  apply LinearMap.ext
  intro c
  change sd (actL (joinAct (generator (p:=p) q)) c)=
    actL (joinAct (generator (p:=p) q)) (sd c)
  exact sd_actL (R:=K) (joinActL (N:=N) (generator (p:=p) q)) c

theorem subdivision_rho (iterations k : ℕ) :
    Commute ((sd : Module.End K (SourceChain p r N K))^iterations) (rho p r N K «λ» k) := by
  apply Commute.pow_left
  unfold rho altOp
  split_ifs
  · unfold normOp
    exact Commute.sum_right _ _ _ (fun i hi=>(subdivision_shifted p r N K «λ»).pow_right i)
  · apply LinearMap.ext
    intro c
    change sd ((1-shifted p r N K «λ») c)=
      (1-shifted p r N K «λ») (sd c)
    simp only [LinearMap.sub_apply,Module.End.one_apply,map_sub]
    have h:=LinearMap.congr_fun (subdivision_shifted p r N K «λ»).eq c
    simpa only [Module.End.mul_apply] using congrArg (fun z=>sd c-z) h

end FairDivision.Topology.Volovikov.ShiftedCyclicSource
