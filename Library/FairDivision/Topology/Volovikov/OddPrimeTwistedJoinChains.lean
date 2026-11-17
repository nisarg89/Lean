import FairDivision.Topology.Volovikov.OddPrimeTensorDifferential
import RequestProject.Dvoretzky.Dold.JoinAction

/-!
# Twisted cyclic-label actions on oriented join chains

A character of an elementary abelian p-group acts on each circle's two
colors by its own cyclic label shift. Unlike the mod-two swap action, the
inverse shift and all oriented boundary signs must be retained. This file
constructs those actual chain actions, proves boundary equivariance, and
computes last-color projection equivariance. It does not assume the
remaining two-color Euler peeling identity.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.Volovikov.OddPrimeTwistedJoinChains

open scoped BigOperators
open Dvoretzky.Dold

abbrev Label (p : ℕ):=Multiplicative (ZMod p)

variable {p D : ℕ} [NeZero p]

/-- The vertex action uses minus the label pullback shift. Both signs
coincide at p=2, but are distinct for the present general-prime action. -/
def twistS (ε : Fin D→ZMod p) (s : Smp D (Label p)) : Smp D (Label p) :=
  fun j=>(s j).map (fun l=>l*Multiplicative.ofAdd (-ε j))

@[simp] theorem twistS_zero (s : Smp D (Label p)) : twistS 0 s=s := by
  funext j
  simp [twistS]

theorem twistS_add (ε η : Fin D→ZMod p) (s : Smp D (Label p)) :
    twistS ε (twistS η s)=twistS (ε+η) s := by
  funext j
  simp only [twistS,Option.map_map]
  congr 1
  funext l
  apply Multiplicative.toAdd.injective
  simp only [Function.comp_apply,toAdd_mul,toAdd_ofAdd,Pi.add_apply,neg_add]
  abel

@[simp] theorem twistS_inverse (ε : Fin D→ZMod p) (s : Smp D (Label p)) :
    twistS ε (twistS (-ε) s)=s := by
  rw [twistS_add,add_neg_cancel,twistS_zero]

theorem twistS_injective (ε : Fin D→ZMod p) : Function.Injective (twistS ε) :=
  Function.LeftInverse.injective (fun s=>by
    simpa only [neg_neg] using twistS_inverse (-ε) s)

@[simp] theorem isSome_twistS (ε : Fin D→ZMod p) (s : Smp D (Label p)) (j : Fin D) :
    (twistS ε s j).isSome=(s j).isSome := by simp [twistS]

@[simp] theorem pos_twistS (ε : Fin D→ZMod p) (s : Smp D (Label p)) (j : Fin D) :
    pos (twistS ε s) j=pos s j := by simp [pos]

@[simp] theorem sgnP_twistS {R : Type*} [CommRing R]
    (ε : Fin D→ZMod p) (s : Smp D (Label p)) (j : Fin D) :
    (sgnP (twistS ε s) j : R)=sgnP s j := by simp [sgnP]

/-- Changing or deleting one color commutes with all other color shifts. -/
theorem twistS_update (ε : Fin D→ZMod p) (s : Smp D (Label p))
    (j : Fin D) (v : Option (Label p)) :
    twistS ε (Function.update s j v)=
      Function.update (twistS ε s) j (v.map (fun l=>l*Multiplicative.ofAdd (-ε j))) := by
  funext k
  by_cases h : k=j
  · subst k
    simp [twistS]
  · simp [twistS,Function.update_of_ne h]

variable {R : Type*} [CommRing R]

def twistL (ε : Fin D→ZMod p) : TChain R D (Label p)→ₗ[R]TChain R D (Label p) :=
  Finsupp.lmapDomain R R (twistS ε)

@[simp] theorem twistL_single (ε : Fin D→ZMod p) (s : Smp D (Label p)) (c : R) :
    twistL ε (Finsupp.single s c)=Finsupp.single (twistS ε s) c := by simp [twistL]

/-- A coefficient is pulled back by the inverse vertex action. This is
where the general-prime formula differs from the self-inverse mod-two one. -/
theorem twistL_apply (ε : Fin D→ZMod p) (c : TChain R D (Label p))
    (s : Smp D (Label p)) : twistL ε c s=c (twistS (-ε) s) := by
  conv_lhs=>rw [←twistS_inverse ε s]
  exact Finsupp.mapDomain_apply_of_injective (twistS_injective ε) c _

@[simp] theorem twistL_zero (c : TChain R D (Label p)) : twistL 0 c=c := by
  apply Finsupp.ext
  intro s
  simp [twistL_apply]

theorem twistL_add (ε η : Fin D→ZMod p) (c : TChain R D (Label p)) :
    twistL ε (twistL η c)=twistL (ε+η) c := by
  have h : (twistL (R:=R) ε)∘ₗtwistL η=twistL (ε+η) := by
    apply tchain_hom_ext
    intro s
    simp only [LinearMap.coe_comp,Function.comp_apply,twistL_single,twistS_add]
  exact LinearMap.congr_fun h c

theorem twistL_commute (ε η : Fin D→ZMod p) :
    Commute (twistL (R:=R) ε) (twistL η) := by
  apply LinearMap.ext
  intro c
  simp only [Module.End.mul_apply,twistL_add,add_comm ε η]

@[simp] theorem twistL_empty (ε : Fin D→ZMod p) :
    twistL (R:=R) ε (Finsupp.single emptyS 1)=Finsupp.single emptyS 1 := by
  rw [twistL_single]
  congr 1

/-- The full oriented face formula is preserved, without identifying
minus one with plus one in the coefficients. -/
theorem faceT_twistS (ε : Fin D→ZMod p) (s : Smp D (Label p)) :
    (faceT (twistS ε s) : TChain R D (Label p))=twistL ε (faceT s) := by
  rw [faceT,faceT,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [isSome_twistS,sgnP_twistS]
  split_ifs
  · rw [map_smul,twistL_single]
    simp only [twistS_update,Option.map_none]
  · exact (map_zero _).symm

/-- Twisted label translation is a genuine chain map over every
commutative coefficient ring, including odd prime fields. -/
theorem boundary_twistL (ε : Fin D→ZMod p) (c : TChain R D (Label p)) :
    bdT (twistL ε c)=twistL ε (bdT c) := by
  have h : (bdT∘ₗtwistL ε : TChain R D (Label p)→ₗ[R]TChain R D (Label p))=
      twistL ε∘ₗbdT :=
    tchain_hom_ext (fun s=>by
      simp only [LinearMap.coe_comp,Function.comp_apply,twistL_single,
        bdT_single,one_smul]
      exact faceT_twistS ε s)
  exact LinearMap.congr_fun h c

/-- Literal coefficient projection at the last color. -/
def projection (v : Option (Label p)) :
    TChain R (D+1) (Label p)→ₗ[R]TChain R D (Label p) :=
  Finsupp.lcomapDomain (fun s : Smp D (Label p)=>Fin.snoc s v)
    (fun s t h=>(Fin.snoc_injective2 h).1)

@[simp] theorem projection_apply (v : Option (Label p))
    (c : TChain R (D+1) (Label p)) (s : Smp D (Label p)) :
    projection v c s=c (Fin.snoc s v) := rfl

theorem twistS_snoc (ε : Fin (D+1)→ZMod p) (s : Smp D (Label p))
    (v : Option (Label p)) :
    twistS ε (Fin.snoc s v)=
      Fin.snoc (twistS (Fin.init ε) s)
        (v.map (fun l=>l*Multiplicative.ofAdd (-ε (Fin.last D)))) := by
  funext j
  refine Fin.lastCases ?_ (fun k=>?_) j
  · simp [twistS]
  · simp [twistS,Fin.init]

/-- The exact last-color projection relation needed for an odd-prime
peeling calculation; its label is shifted by PLUS ε in the pullback. -/
theorem projection_twistL (ε : Fin (D+1)→ZMod p) (v : Option (Label p))
    (c : TChain R (D+1) (Label p)) :
    projection v (twistL ε c)=
      twistL (Fin.init ε)
        (projection (v.map (fun l=>l*Multiplicative.ofAdd (ε (Fin.last D)))) c) := by
  apply Finsupp.ext
  intro s
  simp only [projection_apply,twistL_apply,twistS_snoc,Pi.neg_apply,neg_neg]
  rfl

/-- Each actual elementary-abelian generator gives an operator of order
p, as required by the signed tensor differential. -/
theorem twistL_pow_prime (p : ℕ) [Fact p.Prime] (ε : Fin D→ZMod p) :
    (twistL (R:=R) ε)^p=1 := by
  have hPow : ∀n : ℕ,∀c : TChain R D (Label p),
      ((twistL (R:=R) ε)^n) c=twistL (n•ε) c := by
    intro n
    induction n with
    | zero=>intro c;simp
    | succ n ih=>
        intro c
        rw [pow_succ',Module.End.mul_apply,ih,twistL_add]
        simp only [succ_nsmul,add_comm]
  apply LinearMap.ext
  intro c
  rw [hPow]
  have hZero : p•ε=0 := by
    funext j
    simp [nsmul_eq_mul]
  rw [hZero,twistL_zero]
  rfl

end FairDivision.Topology.Volovikov.OddPrimeTwistedJoinChains
