import RequestProject.Dvoretzky.Dold.JoinAction
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Concrete relative chains for a suspension of a cyclic join

Write a suspension chain as a base chain, a north-cone chain, and a
south-cone chain. Relative to the north pole, the empty base simplex and the
north singleton are zero. Removing the empty coefficient gives an explicit
normal form for that quotient: the base and north components have zero
empty coefficient, while the south component keeps its empty simplex.

The retained south empty simplex is the south pole, and is a nonzero cycle.
The differential below is the literal cone boundary formula, with its signs.
All facts in this file are proved for actual imported oriented join chains;
no relative-chain, differential, or augmentation-exactness premise is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.AAK.SuspensionRelativeChains

open Dvoretzky.Dold
open scoped Classical

abbrev Base (R : Type*) [CommRing R] (D p : ℕ) :=
  TChain R D (Multiplicative (ZMod p))

variable {R : Type*} [CommRing R] {D p : ℕ}

/-- The empty augmentation simplex of the free cyclic join. -/
def empty : Base R D p := Finsupp.single emptyS 1

/-- Coefficient of the empty simplex. -/
def augmentation : Base R D p→ₗ[R]R := Finsupp.lapply emptyS

@[simp] theorem augmentation_empty : augmentation (empty : Base R D p)=1 := by
  simp [augmentation,empty]

/-- Nonempty oriented base chains, represented without their augmentation
coefficient. -/
def NonemptyBase (R : Type*) [CommRing R] (D p : ℕ) : Submodule R (Base R D p) :=
  LinearMap.ker augmentation

@[simp] theorem nonemptyBase_augmentation (c : NonemptyBase R D p) :
    augmentation c.1=0 := c.2

/-- Delete just the empty coefficient. This gives a canonical normal form,
so subsequent maps need no arbitrary representative choices. -/
def removeEmpty : Base R D p→ₗ[R]NonemptyBase R D p where
  toFun c:=⟨c-augmentation c •empty,by
    change augmentation (c-augmentation c •empty)=0
    simp⟩
  map_add' x y:=by
    apply Subtype.ext
    change x + y - augmentation (x + y) • empty =
      (x - augmentation x • empty) + (y - augmentation y • empty)
    rw [map_add, add_smul]
    abel
  map_smul' a x:=by
    apply Subtype.ext
    simp [smul_sub,smul_smul]

@[simp] theorem removeEmpty_coe (c : Base R D p) :
    (removeEmpty c : Base R D p)=c-augmentation c •empty := rfl

@[simp] theorem removeEmpty_of_nonempty (c : NonemptyBase R D p) :
    removeEmpty c.1=c := by
  apply Subtype.ext
  simp

@[simp] theorem removeEmpty_empty : removeEmpty (empty : Base R D p)=0 := by
  apply Subtype.ext
  simp

@[simp] theorem boundary_empty : bdT (empty : Base R D p)=0 := by
  simp [empty,bdT_single,faceT,emptyS]

/-- Removing augmentation does not affect the next ordinary boundary. -/
@[simp] theorem boundary_removeEmpty (c : Base R D p) :
    bdT (removeEmpty c : Base R D p)=bdT c := by
  rw [removeEmpty_coe,map_sub,map_smul,boundary_empty,smul_zero,sub_zero]

/-- Reduced boundary on the nonempty base chains. -/
def reducedBoundary : Module.End R (NonemptyBase R D p) :=
  removeEmpty ∘ₗ bdT ∘ₗ (NonemptyBase R D p).subtype

@[simp] theorem reducedBoundary_apply (c : NonemptyBase R D p) :
    reducedBoundary c=removeEmpty (bdT c.1) := rfl

@[simp] theorem reducedBoundary_removeEmpty (c : Base R D p) :
    reducedBoundary (removeEmpty c)=removeEmpty (bdT c) := by
  rw [reducedBoundary_apply,boundary_removeEmpty]

@[simp] theorem reducedBoundary_squared (c : NonemptyBase R D p) :
    reducedBoundary (reducedBoundary c)=0 := by
  change reducedBoundary (removeEmpty (bdT c.1))=0
  rw [reducedBoundary_removeEmpty,bdT_bdT,map_zero]

/-- Relative suspension chains in their actual three-component normal form.
The last component's empty simplex is retained as the south pole. -/
abbrev Relative (R : Type*) [CommRing R] (D p : ℕ) :=
  NonemptyBase R D p×NonemptyBase R D p×Base R D p

/-- Literal relative cone differential: d(c,a,b)=(dc+a+b,-da,-db),
with empty coefficients removed precisely in the two quotient components. -/
def boundary : Module.End R (Relative R D p) where
  toFun z:=(reducedBoundary z.1+z.2.1+removeEmpty z.2.2,
    -reducedBoundary z.2.1,-bdT z.2.2)
  map_add' x y:=by
    apply Prod.ext
    · simp only [map_add,Prod.fst_add,Prod.snd_add]
      abel
    · apply Prod.ext <;> simp only [map_add,Prod.fst_add,Prod.snd_add] <;> abel
  map_smul' a x:=by
    apply Prod.ext
    · simp only [map_smul,smul_add,Prod.smul_fst,Prod.smul_snd,RingHom.id_apply]
    · apply Prod.ext
      · change -reducedBoundary (a • x.2.1) = a • -reducedBoundary x.2.1
        rw [(reducedBoundary (R := R) (D := D) (p := p)).map_smul]
        exact (smul_neg a (reducedBoundary x.2.1)).symm
      · change -bdT (a • x.2.2) = a • -bdT x.2.2
        rw [map_smul]
        exact (smul_neg a (bdT x.2.2)).symm

@[simp] theorem boundary_apply (z : Relative R D p) :
    boundary z=(reducedBoundary z.1+z.2.1+removeEmpty z.2.2,
      -reducedBoundary z.2.1,-bdT z.2.2) := rfl

/-- The cone signs and augmentation deletion give an actual differential. -/
@[simp] theorem boundary_squared (z : Relative R D p) : boundary (boundary z)=0 := by
  apply Prod.ext
  · change reducedBoundary (reducedBoundary z.1+z.2.1+removeEmpty z.2.2)+
        -reducedBoundary z.2.1+removeEmpty (-bdT z.2.2)=0
    rw [map_add,map_add,reducedBoundary_squared,reducedBoundary_removeEmpty,map_neg]
    abel
  · apply Prod.ext
    · change -reducedBoundary (-reducedBoundary z.2.1)=0
      have hNeg := LinearMap.map_neg (R := R) (S := R) (σ := RingHom.id R)
        (M := NonemptyBase R D p) (M₂ := NonemptyBase R D p)
        (reducedBoundary (R := R) (D := D) (p := p)) (reducedBoundary z.2.1)
      calc
        -reducedBoundary (-reducedBoundary z.2.1) =
            -(-reducedBoundary (reducedBoundary z.2.1)) := congrArg Neg.neg hNeg
        _ = 0 := by
          apply Subtype.ext
          change -(-(reducedBoundary (reducedBoundary z.2.1) : Base R D p)) = 0
          rw [neg_neg]
          exact congrArg (fun c : NonemptyBase R D p => (c : Base R D p))
            (reducedBoundary_squared z.2.1)
    · change -bdT (-bdT z.2.2)=0
      simp [bdT_bdT]

/-- The north pole vanishes in this relative model; the south pole remains. -/
def southPole : Relative R D p := (0,0,empty)

/-- Extract the retained south-pole coefficient. -/
def southCoefficient : Relative R D p→ₗ[R]R :=
  augmentation ∘ₗ LinearMap.snd R (NonemptyBase R D p) (Base R D p) ∘ₗ
    LinearMap.snd R (NonemptyBase R D p) (NonemptyBase R D p×Base R D p)

@[simp] theorem southCoefficient_apply (z : Relative R D p) :
    southCoefficient z=augmentation z.2.2 := rfl

@[simp] theorem southCoefficient_southPole : southCoefficient (southPole : Relative R D p)=1 := by
  simp [southPole]

@[simp] theorem boundary_southPole : boundary (southPole : Relative R D p)=0 := by
  apply Prod.ext
  · change reducedBoundary (0 : NonemptyBase R D p) + 0 +
      removeEmpty (empty : Base R D p) = 0
    rw [map_zero, removeEmpty_empty, zero_add, add_zero]
  · apply Prod.ext
    · change -reducedBoundary (0 : NonemptyBase R D p) = 0
      rw [map_zero]
      apply Subtype.ext
      change -(0 : Base R D p) = 0
      exact neg_zero
    · change -bdT (empty : Base R D p) = 0
      rw [boundary_empty, neg_zero]

theorem southPole_ne_zero [Nontrivial R] : (southPole : Relative R D p)≠0 := by
  intro h
  have hCoeff:=congrArg (southCoefficient (R:=R) (D:=D) (p:=p)) h
  apply (one_ne_zero : (1:R)≠0)
  simpa only [southCoefficient_southPole,map_zero] using hCoeff

end FairDivision.Topology.AAK.SuspensionRelativeChains
