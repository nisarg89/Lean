import FairDivision.Topology.AAK.SuspensionRelativeCyclic

/-!
# Augmented suspension chains and their actual relative projection

The simplicial approximation first lands in ordinary augmented suspension
chains. Only afterwards do we quotient out the north pole. This distinction
is necessary: adding a vertex to the empty simplex does not descend to the
relative quotient. The raw three-component chain model below implements the
cone differential before applying the explicit relative normal form.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.AAK.SuspensionRelativeChains

open Dvoretzky.Dold
open scoped Classical

variable {R : Type*} [CommRing R] {D p : ℕ}

abbrev Raw (R : Type*) [CommRing R] (D p : ℕ) := Base R D p×Base R D p×Base R D p

/-- Ordinary augmented suspension differential, before taking a relative
quotient. The cone vertex is placed before its base orientation. -/
def rawBoundary : Module.End R (Raw R D p) where
  toFun z:=(bdT z.1+z.2.1+z.2.2,-bdT z.2.1,-bdT z.2.2)
  map_add' x y:=by
    apply Prod.ext
    · simp only [map_add,Prod.fst_add,Prod.snd_add]
      abel
    · apply Prod.ext <;> simp only [map_add,Prod.fst_add,Prod.snd_add] <;> abel
  map_smul' a x:=by
    apply Prod.ext
    · simp only [map_smul,smul_add,Prod.smul_fst,Prod.smul_snd,RingHom.id_apply]
    · apply Prod.ext
      · change -bdT (a • x.2.1) = a • -bdT x.2.1
        rw [map_smul]
        exact (smul_neg a (bdT x.2.1)).symm
      · change -bdT (a • x.2.2) = a • -bdT x.2.2
        rw [map_smul]
        exact (smul_neg a (bdT x.2.2)).symm

@[simp] theorem rawBoundary_apply (z : Raw R D p) :
    rawBoundary z=(bdT z.1+z.2.1+z.2.2,-bdT z.2.1,-bdT z.2.2) := rfl

@[simp] theorem rawBoundary_squared (z : Raw R D p) : rawBoundary (rawBoundary z)=0 := by
  apply Prod.ext
  · change bdT (bdT z.1+z.2.1+z.2.2)+ -bdT z.2.1+ -bdT z.2.2=0
    simp only [map_add,bdT_bdT]
    abel
  · apply Prod.ext
    · change -bdT (-bdT z.2.1)=0
      simp [bdT_bdT]
    · change -bdT (-bdT z.2.2)=0
      simp [bdT_bdT]

/-- The actual projection to the relative north-pole chain model. -/
def toRelative : Raw R D p→ₗ[R]Relative R D p :=
  removeEmpty.prodMap (removeEmpty.prodMap LinearMap.id)

@[simp] theorem toRelative_apply (z : Raw R D p) :
    toRelative z=(removeEmpty z.1,removeEmpty z.2.1,z.2.2) := rfl

/-- This projection really is a chain map, including augmented degree zero. -/
theorem toRelative_boundary (z : Raw R D p) :
    toRelative (rawBoundary z)=boundary (toRelative z) := by
  apply Prod.ext
  · change removeEmpty (bdT z.1+z.2.1+z.2.2)=
      reducedBoundary (removeEmpty z.1)+removeEmpty z.2.1+removeEmpty z.2.2
    rw [map_add,map_add,reducedBoundary_removeEmpty]
  · apply Prod.ext
    · change removeEmpty (-bdT z.2.1)= -reducedBoundary (removeEmpty z.2.1)
      rw [LinearMap.map_neg (R := R) (S := R) (σ := RingHom.id R)
        (M := Base R D p) (M₂ := NonemptyBase R D p)
        (removeEmpty (R := R) (D := D) (p := p)), reducedBoundary_removeEmpty]
    · rfl

/-- Every relative normal form has the indicated literal raw representative. -/
theorem toRelative_surjective : Function.Surjective (toRelative (R:=R) (D:=D) (p:=p)) := by
  intro z
  refine ⟨(z.1.1,z.2.1.1,z.2.2),?_⟩
  simp

/-- Raw augmented empty simplex, before quotienting. -/
def rawEmpty : Raw R D p := (empty,0,0)

def rawNorth : Raw R D p := (0,empty,0)

def rawSouth : Raw R D p := (0,0,empty)

@[simp] theorem rawBoundary_empty : rawBoundary (rawEmpty : Raw R D p)=0 := by
  simp [rawEmpty,rawBoundary_apply]

@[simp] theorem rawBoundary_north : rawBoundary (rawNorth : Raw R D p)=rawEmpty := by
  simp [rawNorth,rawEmpty,rawBoundary_apply]

@[simp] theorem rawBoundary_south : rawBoundary (rawSouth : Raw R D p)=rawEmpty := by
  simp [rawSouth,rawEmpty,rawBoundary_apply]

@[simp] theorem toRelative_empty : toRelative (rawEmpty : Raw R D p)=0 := by
  simp [rawEmpty]

@[simp] theorem toRelative_north : toRelative (rawNorth : Raw R D p)=0 := by
  simp [rawNorth]

@[simp] theorem toRelative_south : toRelative (rawSouth : Raw R D p)=southPole := by
  simp [rawSouth,southPole]

/-- The kernel removes exactly the empty base and north-singleton
coefficients, with no relation imposed on the south component. -/
theorem toRelative_eq_zero_iff (z : Raw R D p) :
    toRelative z=0 ↔ z=(augmentation z.1 •empty,augmentation z.2.1 •empty,0) := by
  constructor
  · intro hz
    have hc:=congrArg (fun w : Relative R D p=>(w.1 : Base R D p)) hz
    have ha:=congrArg (fun w : Relative R D p=>(w.2.1 : Base R D p)) hz
    have hb:=congrArg (fun w : Relative R D p=>w.2.2) hz
    apply Prod.ext
    · change z.1=augmentation z.1 •empty
      exact sub_eq_zero.mp hc
    · apply Prod.ext
      · change z.2.1=augmentation z.2.1 •empty
        exact sub_eq_zero.mp ha
      · exact hb
  · intro hz
    rw [hz]
    simp

/-- The cyclic action on the raw suspension fixes both cone vertices. -/
def rawGenerator [Fact p.Prime] : Module.End R (Raw R D p) :=
  baseGenerator.prodMap (baseGenerator.prodMap baseGenerator)

@[simp] theorem rawGenerator_apply [Fact p.Prime] (z : Raw R D p) :
    rawGenerator z=(baseGenerator z.1,baseGenerator z.2.1,baseGenerator z.2.2) := rfl

/-- Equivariance of the actual north-pole quotient. -/
theorem toRelative_generator [Fact p.Prime] (z : Raw R D p) :
    toRelative (rawGenerator z)=generator (toRelative z) := by
  apply Prod.ext
  · exact (nonemptyGenerator_removeEmpty z.1).symm
  · apply Prod.ext
    · exact (nonemptyGenerator_removeEmpty z.2.1).symm
    · rfl

end FairDivision.Topology.AAK.SuspensionRelativeChains
