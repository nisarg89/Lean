import FairDivision.Topology.AAK.SuspensionRelativeChains

/-!
# Actual cyclic exactness on the relative suspended-join target

The imported fundamental-domain projection on free oriented join chains is
restricted to the zero-augmentation components and used directly on the
south component. Its conjugates sum to the identity except for the retained
south-pole coefficient. Thus the exact hypotheses of the imported Dold
algebra theorem are proved for this concrete relative target.

These are actual relative target operators and exactness proofs. The
geometric source-time prism must still be mapped into this target before
its no-sequence theorem gives the external AAK sign-reversal obstruction.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.AAK.SuspensionRelativeChains

open Dvoretzky.Dold
open scoped BigOperators Classical

variable {R : Type*} [CommRing R] {D p : ℕ} [Fact p.Prime]

/-- The existing Mathlib group construction retains this kernel's fixed
additive monoid and module, so endomorphism subtraction synthesizes without
reconstructing a constrained ambient Finsupp group. -/
local instance nonemptyCanonicalAddCommGroup : AddCommGroup (NonemptyBase R D p) :=
  Module.addCommMonoidToAddCommGroup R

/-- The aligned group's actual negation agrees with the ambient chain
negation. The dictionary is explicit because bare `-c` still selects the
independently available subtype negation. -/
private theorem nonemptyCanonical_neg_coe (c : NonemptyBase R D p) :
    ((@Neg.neg (NonemptyBase R D p) nonemptyCanonicalAddCommGroup.toNeg c) :
      Base R D p) = -(c : Base R D p) := by
  change (-1 : R) • (c : Base R D p) = -(c : Base R D p)
  exact neg_one_smul R _

private theorem nonemptyCanonical_sub_coe (c d : NonemptyBase R D p) :
    ((@Sub.sub (NonemptyBase R D p) nonemptyCanonicalAddCommGroup.toSub c d) :
      Base R D p) = (c : Base R D p) - (d : Base R D p) := by
  change ((c + @Neg.neg (NonemptyBase R D p)
      nonemptyCanonicalAddCommGroup.toNeg d : NonemptyBase R D p) : Base R D p) = _
  simp only [Submodule.coe_add, nonemptyCanonical_neg_coe, sub_eq_add_neg]

/-- The product group's inherited subtraction and the direct product/subtype
subtraction agree on actual chains, although their instance terms differ. -/
private theorem relativeCanonical_sub_eq (x y : Relative R D p) :
    @Sub.sub (Relative R D p)
      (inferInstance : AddCommGroup (Relative R D p)).toSub x y = x-y := by
  apply Prod.ext
  · apply Subtype.ext
    change ((@Sub.sub (NonemptyBase R D p) nonemptyCanonicalAddCommGroup.toSub x.1 y.1) :
      Base R D p) = ((x.1-y.1 : NonemptyBase R D p) : Base R D p)
    rw [nonemptyCanonical_sub_coe, Submodule.coe_sub]
  · apply Prod.ext
    · apply Subtype.ext
      change ((@Sub.sub (NonemptyBase R D p) nonemptyCanonicalAddCommGroup.toSub
          x.2.1 y.2.1) : Base R D p) =
        ((x.2.1-y.2.1 : NonemptyBase R D p) : Base R D p)
      rw [nonemptyCanonical_sub_coe, Submodule.coe_sub]
    · rfl

/-- Cyclic translation on the literal oriented base chains. -/
def baseGenerator : Module.End R (Base R D p) := tact (gen p)

@[simp] theorem augmentation_baseGenerator (c : Base R D p) :
    augmentation (baseGenerator c)=augmentation c :=
  tact_apply_emptyS (gen p) c

@[simp] theorem baseGenerator_empty : baseGenerator (empty : Base R D p)=empty := by
  simp [baseGenerator,empty]

/-- Translation preserves zero augmentation. -/
def nonemptyGenerator : Module.End R (NonemptyBase R D p) where
  toFun c:=⟨baseGenerator c.1,by
    change augmentation (baseGenerator c.1)=0
    rw [augmentation_baseGenerator,nonemptyBase_augmentation]⟩
  map_add' x y:=by apply Subtype.ext; exact map_add baseGenerator x.1 y.1
  map_smul' a x:=by apply Subtype.ext; exact map_smul baseGenerator a x.1

@[simp] theorem nonemptyGenerator_coe (c : NonemptyBase R D p) :
    (nonemptyGenerator c : Base R D p)=baseGenerator c.1 := rfl

@[simp] theorem nonemptyGenerator_removeEmpty (c : Base R D p) :
    nonemptyGenerator (removeEmpty c)=removeEmpty (baseGenerator c) := by
  apply Subtype.ext
  simp only [nonemptyGenerator_coe,removeEmpty_coe,map_sub,map_smul,
    baseGenerator_empty,augmentation_baseGenerator]

/-- Reduced boundary commutes with this actual cyclic translation. -/
theorem reducedBoundary_nonemptyGenerator (c : NonemptyBase R D p) :
    reducedBoundary (nonemptyGenerator c)=nonemptyGenerator (reducedBoundary c) := by
  change removeEmpty (bdT (baseGenerator c.1))=
    nonemptyGenerator (removeEmpty (bdT c.1))
  rw [nonemptyGenerator_removeEmpty]
  exact congrArg removeEmpty (bdT_tact (gen p) c.1)

/-- The diagonal action on base, north cone, and south cone. -/
def generator : Module.End R (Relative R D p) :=
  nonemptyGenerator.prodMap (nonemptyGenerator.prodMap baseGenerator)

@[simp] theorem generator_apply (z : Relative R D p) :
    generator z=(nonemptyGenerator z.1,nonemptyGenerator z.2.1,baseGenerator z.2.2) := rfl

theorem nonemptyGenerator_pow_coe (i : ℕ) (c : NonemptyBase R D p) :
    ((nonemptyGenerator^i) c : Base R D p)=(baseGenerator^i) c.1 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [pow_succ',Module.End.mul_apply,nonemptyGenerator_coe,ih]

theorem generator_pow_apply (i : ℕ) (z : Relative R D p) :
    (generator^i) z=((nonemptyGenerator^i) z.1,
      (nonemptyGenerator^i) z.2.1,(baseGenerator^i) z.2.2) := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [pow_succ',Module.End.mul_apply,ih,generator_apply]

theorem baseGenerator_pow_p : (baseGenerator : Module.End R (Base R D p))^p=1 := by
  apply LinearMap.ext
  intro c
  rw [baseGenerator,tact_pow,gen_pow_p,tact_one]
  rfl

theorem nonemptyGenerator_pow_p :
    (nonemptyGenerator : Module.End R (NonemptyBase R D p))^p=1 := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  rw [nonemptyGenerator_pow_coe,baseGenerator_pow_p]
  rfl

theorem generator_pow_p : (generator : Module.End R (Relative R D p))^p=1 := by
  apply LinearMap.ext
  intro z
  rw [generator_pow_apply,nonemptyGenerator_pow_p,baseGenerator_pow_p]
  rfl

/-- The relative differential is equivariant, with both cone signs retained. -/
theorem boundary_generator : Commute (boundary : Module.End R (Relative R D p)) generator := by
  apply LinearMap.ext
  intro z
  apply Prod.ext
  · change reducedBoundary (nonemptyGenerator z.1)+nonemptyGenerator z.2.1+
        removeEmpty (baseGenerator z.2.2)=
      nonemptyGenerator (reducedBoundary z.1+z.2.1+removeEmpty z.2.2)
    rw [reducedBoundary_nonemptyGenerator,←nonemptyGenerator_removeEmpty,map_add,map_add]
  · apply Prod.ext
    · apply Subtype.ext
      change -(reducedBoundary (nonemptyGenerator z.2.1) : Base R D p) =
        baseGenerator (-(reducedBoundary z.2.1 : Base R D p))
      have hComm := congrArg (fun c : NonemptyBase R D p => (c : Base R D p))
        (reducedBoundary_nonemptyGenerator z.2.1)
      rw [hComm]
      exact (LinearMap.map_neg (R := R) (S := R) (σ := RingHom.id R)
        (M := Base R D p) (M₂ := Base R D p)
        (baseGenerator (R := R) (D := D) (p := p))
        (reducedBoundary z.2.1 : Base R D p)).symm
    · change -bdT (baseGenerator z.2.2)=baseGenerator (-bdT z.2.2)
      rw [map_neg]
      exact congrArg Neg.neg (bdT_tact (gen p) z.2.2)

@[simp] theorem southCoefficient_generator (z : Relative R D p) :
    southCoefficient (generator z)=southCoefficient z :=
  augmentation_baseGenerator z.2.2

@[simp] theorem generator_southPole : generator (southPole : Relative R D p)=southPole := by
  simp [generator_apply,southPole]

/-- The imported projection has no empty coefficient in its image. -/
theorem augmentation_projQ (c : Base R D p) : augmentation (projQ p c)=0 := by
  have h : augmentation ∘ₗ (projQ p : Module.End R (Base R D p))=0 := by
    -- The codomain is R, so use Finsupp's general linear extensionality;
    -- DKGM's tchain_hom_ext is restricted to chain-valued endomorphisms.
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    have hEmpty : ¬FundDom p (emptyS : Smp D (Multiplicative (ZMod p))) := by
      rintro ⟨j,_hj,hj⟩
      simp [emptyS] at hj
    by_cases hs : s=emptyS
    · subst s
      simp [projQ,hEmpty,augmentation]
    · by_cases hFund : FundDom p s
      · simp [projQ,hFund,augmentation,hs,Ne.symm hs]
      · simp [projQ,hFund,augmentation]
  exact LinearMap.congr_fun h c

/-- Restrict the SAME fundamental-domain projection to nonempty chains. -/
def nonemptyProjection : Module.End R (NonemptyBase R D p) where
  toFun c:=⟨projQ p c.1,augmentation_projQ c.1⟩
  map_add' x y:=by apply Subtype.ext; exact map_add (projQ p) x.1 y.1
  map_smul' a x:=by apply Subtype.ext; exact map_smul (projQ p) a x.1

@[simp] theorem nonemptyProjection_coe (c : NonemptyBase R D p) :
    (nonemptyProjection c : Base R D p)=projQ p c.1 := rfl

theorem nonemptyProjection_identity (c : NonemptyBase R D p) :
    (∑i∈Finset.range p,(nonemptyGenerator^i)
      (nonemptyProjection ((nonemptyGenerator^(p-i)) c)))=c := by
  apply Subtype.ext
  simp only [Submodule.coe_sum,nonemptyGenerator_pow_coe,nonemptyProjection_coe]
  have h := projQ_identity (R:=R) (D:=D) p c.1
  have hAug : c.1 emptyS=0 := c.2
  simpa only [baseGenerator,hAug,zero_smul,sub_zero] using h

/-- Diagonal transversal projection on the concrete relative target. -/
def projection : Module.End R (Relative R D p) :=
  nonemptyProjection.prodMap (nonemptyProjection.prodMap (projQ p))

@[simp] theorem projection_apply (z : Relative R D p) :
    projection z=(nonemptyProjection z.1,nonemptyProjection z.2.1,projQ p z.2.2) := rfl

/-- Every nonfixed simplex has exactly one representative in the chosen
transversal. The only remaining fixed coefficient is the south pole. -/
theorem projection_identity (z : Relative R D p) :
    (∑i∈Finset.range p,(generator^i) (projection ((generator^(p-i)) z)))=
      z-southCoefficient z •southPole := by
  apply Prod.ext
  · apply Subtype.ext
    simpa [Prod.fst_sum,generator_pow_apply,projection_apply,southPole,
      southCoefficient_apply,Submodule.coe_sum,Submodule.coe_sub] using
      congrArg (fun c : NonemptyBase R D p => (c : Base R D p))
        (nonemptyProjection_identity z.1)
  · apply Prod.ext
    · apply Subtype.ext
      simpa [Prod.fst_sum,Prod.snd_sum,generator_pow_apply,projection_apply,southPole,
        southCoefficient_apply,Submodule.coe_sum,Submodule.coe_sub] using
        congrArg (fun c : NonemptyBase R D p => (c : Base R D p))
          (nonemptyProjection_identity z.2.1)
    · simpa [Prod.snd_sum,generator_pow_apply,projection_apply,southPole,
        southCoefficient_apply,baseGenerator,augmentation,empty] using
        projQ_identity (R:=R) (D:=D) p z.2.2

set_option backward.isDefEq.respectTransparency false in
/-- Actual norm/difference exactness modulo the one retained pole cycle. -/
theorem exactness :
    (∀z : Relative R D p,
      (((1 : Module.End R (Relative R D p)) - generator (R := R) (D := D) (p := p)) : Module.End R (Relative R D p)) z=0→
      ∃e : Relative R D p,∃c : R,
        z=normOp (R := R) (M := Relative R D p)
          (generator (R := R) (D := D) (p := p)) p e+c•southPole) ∧
    (∀z : Relative R D p,
      normOp (R := R) (M := Relative R D p)
        (generator (R := R) (D := D) (p := p)) p z=0→
      ∃e : Relative R D p,∃c : R,
        z=(((1 : Module.End R (Relative R D p)) -
          generator (R := R) (D := D) (p := p)) : Module.End R (Relative R D p)) e+c•southPole) :=
  exact_of_proj (R := R) (M := Relative R D p)
    (generator (R := R) (D := D) (p := p))
    (projection (R := R) (D := D) (p := p)) p (Fact.out : p.Prime).pos
    (generator_pow_p (R := R) (D := D) (p := p))
    (southPole (R := R) (D := D) (p := p))
    (southCoefficient (R := R) (D := D) (p := p))
    (fun z => (projection_identity (R := R) (D := D) (p := p) z).trans
      (relativeCanonical_sub_eq z (southCoefficient z • southPole)).symm)

theorem boundary_norm :
    Commute (boundary : Module.End R (Relative R D p))
      (normOp (R := R) (M := Relative R D p)
        (generator (R := R) (D := D) (p := p)) p) := by
  unfold normOp
  exact Commute.sum_right _ _ _
    (fun i _=>(boundary_generator (R := R) (D := D) (p := p)).pow_right i)

set_option backward.isDefEq.respectTransparency false in
theorem boundary_difference :
    Commute (boundary : Module.End R (Relative R D p))
      (((1 : Module.End R (Relative R D p)) - generator (R := R) (D := D) (p := p)) : Module.End R (Relative R D p)) := by
  apply LinearMap.ext
  intro z
  change boundary
      ((((1 : Module.End R (Relative R D p)) - generator (R := R) (D := D) (p := p)) :
        Module.End R (Relative R D p)) z) =
    (((1 : Module.End R (Relative R D p)) - generator (R := R) (D := D) (p := p)) :
      Module.End R (Relative R D p)) (boundary z)
  simp only [LinearMap.sub_apply, Module.End.one_apply]
  rw [LinearMap.map_sub (R := R) (S := R) (σ := RingHom.id R)
    (M := Relative R D p) (M₂ := Relative R D p)
    (boundary (R := R) (D := D) (p := p))]
  have hComm : boundary (generator z) = generator (boundary z) :=
    LinearMap.congr_fun (boundary_generator (R := R) (D := D) (p := p)).eq z
  rw [hComm]

set_option backward.isDefEq.respectTransparency false in
theorem southCoefficient_difference (z : Relative R D p) :
    southCoefficient (R := R) (D := D) (p := p) ((((1 : Module.End R (Relative R D p)) -
      generator (R := R) (D := D) (p := p)) : Module.End R (Relative R D p)) z)=0 := by
  simp only [LinearMap.sub_apply,Module.End.one_apply,map_sub,southCoefficient_generator,sub_self]

set_option backward.isDefEq.respectTransparency false in
/-- Completed relative TARGET algebra. An actual equivariant prism from
south to north would provide a sequence satisfying these premises. The
geometric construction, rather than any assumed invariance principle, is
responsible for the boundary recurrence and the last zero. -/
theorem no_sequence [Nontrivial R]
    (n : ℕ) (b : ℕ→Relative R D p)
    (hFirst : boundary (b 0)=southPole)
    (hBoundary : ∀k<n,boundary (b (k+1))=
      altOp (R := R) (M := Relative R D p)
        (normOp (R := R) (M := Relative R D p)
          (generator (R := R) (D := D) (p := p)) p)
        (((1 : Module.End R (Relative R D p)) - generator (R := R) (D := D) (p := p)) : Module.End R (Relative R D p)) k (b k))
    (hLast : b n=0) : False := by
  apply dold_algebra (R := R) (M := Relative R D p)
    (boundary (R := R) (D := D) (p := p))
    (normOp (R := R) (M := Relative R D p)
      (generator (R := R) (D := D) (p := p)) p)
    (((1 : Module.End R (Relative R D p)) - generator (R := R) (D := D) (p := p)) : Module.End R (Relative R D p))
    (southPole (R := R) (D := D) (p := p))
    (southCoefficient (R := R) (D := D) (p := p))
    (LinearMap.ext (boundary_squared (R := R) (D := D) (p := p)))
    (boundary_norm (R := R) (D := D) (p := p)).eq
    (boundary_difference (R := R) (D := D) (p := p)).eq
    (boundary_southPole (R := R) (D := D) (p := p))
    (southCoefficient_difference (R := R) (D := D) (p := p))
    (by rw [southCoefficient_southPole];exact (one_ne_zero : (1 : R) ≠ 0))
    (exactness (R := R) (D := D) (p := p)).2
    (exactness (R := R) (D := D) (p := p)).1 n b hFirst hBoundary hLast

end FairDivision.Topology.AAK.SuspensionRelativeChains
