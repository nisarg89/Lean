import FairDivision.Topology.Volovikov.ShiftedCyclicTargetBlocks

/-!
# The complete shifted-cyclic algebraic obstruction on the target

All hypotheses of DKGM's algebraic Dold theorem are supplied here by the
actual twisted join-chain operators. The generic support-block proof
establishes the two exactness directions, including the empty-simplex
augmentation. This module does not assume a free genuine cyclic action
on the whole target.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.Volovikov.ShiftedCyclicTarget

open scoped BigOperators
open Dvoretzky.Dold
open OddPrimeTwistedJoinChains
open ShiftedCyclicTargetBlocks
open ShiftedCyclicSupportMatrices (weights)

variable {p r D : ℕ} [Fact p.Prime]

/-- The same independent scalar weights as on the source. -/
def shifted (ε : Fin r→Fin D→ZMod p) : Module.End (K p r) (Target p r D) :=
  1+displacement ε

def empty : Target p r D:=Finsupp.single emptyS 1

def augmentation : Target p r D→ₗ[K p r]K p r:=Finsupp.lapply emptyS

theorem shifted_power (ε : Fin r→Fin D→ZMod p) : (shifted ε)^p=1 :=
  ShiftedCyclicAlgebra.shifted_pow p (weights (p:=p) (r:=r))
    (fun q=>twistL (ε q))
    (fun q=>twistL_pow_prime p (ε q)) (fun q k=>twistL_commute (ε q) (ε k))

theorem norm_eq_power (ε : Fin r→Fin D→ZMod p) :
    normOp (shifted ε) p=(displacement ε)^(p-1) :=
  ShiftedCyclicAlgebra.norm_one_add p (K p r) (displacement ε)

theorem difference_eq_neg (ε : Fin r→Fin D→ZMod p) :
    1-shifted ε= -displacement ε := by
  unfold shifted
  abel

/-- Boundary equivariance holds for the whole shifted linear combination. -/
theorem boundary_shifted (ε : Fin r→Fin D→ZMod p) :
    Commute (bdT : Module.End (K p r) (Target p r D)) (shifted ε) := by
  apply ShiftedCyclicAlgebra.commute_shifted
  intro q
  exact LinearMap.ext (fun c=>boundary_twistL (ε q) c)

theorem boundary_norm (ε : Fin r→Fin D→ZMod p) :
    Commute (bdT : Module.End (K p r) (Target p r D)) (normOp (shifted ε) p) := by
  unfold normOp
  exact Commute.sum_right _ _ _ (fun i hi=>(boundary_shifted ε).pow_right i)

theorem boundary_difference (ε : Fin r→Fin D→ZMod p) :
    Commute (bdT : Module.End (K p r) (Target p r D)) (1-shifted ε) := by
  apply LinearMap.ext
  intro c
  change bdT ((1-shifted ε) c)=(1-shifted ε) (bdT c)
  simp only [LinearMap.sub_apply,Module.End.one_apply,map_sub]
  have h:=LinearMap.congr_fun (boundary_shifted ε).eq c
  simpa only [Module.End.mul_apply] using congrArg (fun z=>bdT c-z) h

@[simp] theorem boundary_empty : bdT (empty : Target p r D)=0 := by
  classical
  simp [empty,faceT,emptyS]

@[simp] theorem augmentation_empty : augmentation (empty : Target p r D)=1 := by
  classical
  simp [augmentation,empty]

theorem augmentation_difference (ε : Fin r→Fin D→ZMod p) (z : Target p r D) :
    augmentation ((1-shifted ε) z)=0 := by
  rw [difference_eq_neg]
  change -(displacement ε z emptyS)=0
  rw [displacement_empty,neg_zero]

/-- A norm-kernel vector has an ACTUAL difference preimage modulo its
empty coefficient. The negative witness retains the odd-prime sign. -/
theorem norm_kernel_preimage (ε : Fin r→Fin D→ZMod p)
    (hCharacters : ∀j : Fin D,∃q : Fin r,ε q j≠0)
    (z : Target p r D) (hz : normOp (shifted ε) p z=0) :
    ∃e : Target p r D,∃c : K p r,z=(1-shifted ε) e+c•empty := by
  rw [norm_eq_power] at hz
  obtain ⟨e,he⟩:=displacement_power_kernel_preimage ε hCharacters z hz
  refine ⟨-e,z emptyS,?_⟩
  rw [difference_eq_neg]
  simpa only [LinearMap.neg_apply,map_neg,neg_neg,empty] using he

/-- A difference-kernel vector has an actual norm preimage modulo the
augmentation simplex, using the SAME generic target operator. -/
theorem difference_kernel_preimage (ε : Fin r→Fin D→ZMod p)
    (hCharacters : ∀j : Fin D,∃q : Fin r,ε q j≠0)
    (z : Target p r D) (hz : (1-shifted ε) z=0) :
    ∃e : Target p r D,∃c : K p r,z=normOp (shifted ε) p e+c•empty := by
  rw [difference_eq_neg,LinearMap.neg_apply,neg_eq_zero] at hz
  obtain ⟨e,he⟩:=displacement_kernel_preimage ε hCharacters z hz
  exact ⟨e,z emptyS,by simpa only [norm_eq_power,empty] using he⟩

/-- Completed target algebraic obstruction: every genuine character is
nontrivial, and hence no finite defect-one shifted cone sequence can end
in zero. The remaining geometric use must construct that sequence by
actual subdivision and an equivariant simplicial approximation. -/
theorem no_sequence (ε : Fin r→Fin D→ZMod p)
    (hCharacters : ∀j : Fin D,∃q : Fin r,ε q j≠0)
    (n : ℕ) (b : ℕ→Target p r D)
    (hFirst : bdT (b 0)=empty)
    (hBoundary : ∀k<n,bdT (b (k+1))=
      altOp (normOp (shifted ε) p) (1-shifted ε) k (b k))
    (hLast : b n=0) : False := by
  apply dold_algebra (bdT : Module.End (K p r) (Target p r D))
    (normOp (shifted ε) p) (1-shifted ε) empty augmentation
    (LinearMap.ext (fun c=>bdT_bdT c))
    (boundary_norm ε).eq (boundary_difference ε).eq
    boundary_empty (augmentation_difference ε)
    (by rw [augmentation_empty];exact one_ne_zero)
    (norm_kernel_preimage ε hCharacters)
    (difference_kernel_preimage ε hCharacters)
    n b hFirst hBoundary hLast

end FairDivision.Topology.Volovikov.ShiftedCyclicTarget
