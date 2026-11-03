import FairDivision.Topology.Volovikov.ShiftedCyclicAlgebra
import FairDivision.LinearAlgebra.MatrixSpecializationRank
import RequestProject.Dvoretzky.Dold.Algebra

/-!
# Exact cyclic difference/norm on one nonempty label-support block

The block consists of all assignments b:J→Z/p. If ε has a nonzero j₀
coordinate, translation b↦b+ε is free of order p. The projection Q keeps
precisely b(j₀)=0. Among the p translates exactly one survives, so its
conjugate sum is the identity. DKGM's proved projection lemma supplies
norm/difference exactness; rank-nullity gives the specialized rank sum.

The whole argument allows different generators on different support
blocks. It does not assert one genuine cyclic subgroup moves all target
characters simultaneously.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.Volovikov.CyclicLabelBlockExactness

open scoped BigOperators Classical
open Dvoretzky.Dold

variable {p : ℕ} [Fact p.Prime] {J : Type*} [Fintype J]

abbrev Labels (p : ℕ) (J : Type*):=J→ZMod p

/-- Coefficient pullback, with the same PLUS shift as twisted join chains. -/
def action {K : Type*} [Field K] (ε : Labels p J) :
    Module.End K (Labels p J→K) where
  toFun f:=fun b=>f (b+ε)
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

theorem action_power {K : Type*} [Field K] (ε : Labels p J)
    (n : ℕ) (f : Labels p J→K) (b : Labels p J) :
    ((action (K:=K) ε)^n) f b=f (b+n•ε) := by
  induction n generalizing b with
  | zero=>simp
  | succ n ih=>
      rw [pow_succ',Module.End.mul_apply]
      change ((action ε)^n) f (b+ε)=_
      rw [ih]
      congr 1
      simp only [succ_nsmul]
      abel

@[simp] theorem p_smul_labels (ε : Labels p J) : p•ε=0 := by
  funext j
  simp [nsmul_eq_mul]

theorem action_order {K : Type*} [Field K] (ε : Labels p J) :
    (action (K:=K) ε)^p=1 := by
  apply LinearMap.ext
  intro f
  funext b
  simp only [action_power,p_smul_labels,add_zero,Module.End.one_apply]

/-- Choose one literal hyperplane transversal to the cyclic orbit. -/
def projection {K : Type*} [Field K] (j₀ : J) :
    Module.End K (Labels p J→K) where
  toFun f:=fun b=>if b j₀=0 then f b else 0
  map_add' f g:=by funext b;by_cases hb:b j₀=0 <;> simp [hb]
  map_smul' c f:=by funext b;by_cases hb:b j₀=0 <;> simp [hb]

/-- Exactly one exponent in the actual range 0,...,p−1 reaches the
transversal. Its value is (-b(j₀)/ε(j₀)).val. -/
theorem unique_transversal_index (ε b : Labels p J) (j₀ : J) (hε : ε j₀≠0) :
    ∃k : ℕ,k<p ∧ (b+k•ε) j₀=0 ∧
      ∀i : ℕ,i<p→(b+i•ε) j₀=0→i=k := by
  let root : ZMod p:= -b j₀/ε j₀
  let k:=root.val
  have hk : k<p:=ZMod.val_lt root
  have hkCast : (k : ZMod p)=root:=ZMod.natCast_zmod_val root
  have hRoot : (b+k•ε) j₀=0 := by
    change b j₀+k•ε j₀=0
    rw [nsmul_eq_mul,hkCast]
    dsimp only [root]
    rw [div_mul_cancel₀ _ hε,add_neg_cancel]
  refine ⟨k,hk,hRoot,?_⟩
  intro i hi hZero
  have hCast : (i : ZMod p)=root := by
    apply (eq_div_iff hε).mpr
    change b j₀+i•ε j₀=0 at hZero
    rw [nsmul_eq_mul] at hZero
    change (i : ZMod p)*ε j₀= -b j₀
    linear_combination hZero
  have hVal:=congrArg ZMod.val hCast
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hi] using hVal

/-- The actual fundamental-domain projection identity. -/
theorem projection_trace {K : Type*} [Field K]
    (ε : Labels p J) (j₀ : J) (hε : ε j₀≠0) (f : Labels p J→K) :
    (∑i∈Finset.range p,((action ε)^i)
      (projection j₀ (((action ε)^(p-i)) f)))=f := by
  classical
  funext b
  have hTerm (i : ℕ) (hi : i<p) :
      (((action ε)^i) (projection j₀ (((action ε)^(p-i)) f))) b=
        if (b+i•ε) j₀=0 then f b else 0 := by
    rw [action_power]
    change (if (b+i•ε) j₀=0 then ((action ε)^(p-i)) f (b+i•ε) else 0)=_
    rw [action_power]
    have hShift : b+i•ε+(p-i)•ε=b := by
      rw [add_assoc,←add_nsmul,Nat.add_sub_of_le hi.le,p_smul_labels,add_zero]
    rw [hShift]
  simp only [Finset.sum_apply]
  obtain ⟨k,hk,hZero,hUnique⟩:=unique_transversal_index ε b j₀ hε
  rw [Finset.sum_eq_single k]
  · rw [hTerm k hk,if_pos hZero]
  · intro i hi hne
    rw [hTerm i (Finset.mem_range.mp hi),if_neg]
    exact fun h=>hne (hUnique i (Finset.mem_range.mp hi) h)
  · intro h
    exact (h (Finset.mem_range.mpr hk)).elim

/-- Actual norm/difference exactness on the support block, obtained from
the imported cyclic Dold projection theorem with ZERO augmentation. -/
theorem action_exact {K : Type*} [Field K]
    (ε : Labels p J) (j₀ : J) (hε : ε j₀≠0) :
    LinearMap.range (normOp (action (K:=K) ε) p)=LinearMap.ker (1-action (K:=K) ε) ∧
      LinearMap.range (1-action (K:=K) ε)=LinearMap.ker (normOp (action (K:=K) ε) p) := by
  obtain ⟨hDifference,hNorm⟩:=exact_of_proj (action (K:=K) ε) (projection j₀)
    p (Fact.out : p.Prime).pos (action_order ε)
    (0 : Labels p J→K) (0 : (Labels p J→K)→ₗ[K]K)
    (by
      intro f
      simpa only [LinearMap.zero_apply,zero_smul,sub_zero] using
        projection_trace ε j₀ hε f)
  constructor
  · apply Submodule.ext
    intro f
    constructor
    · rintro ⟨g,rfl⟩
      change (1-action (K:=K) ε) (normOp (action (K:=K) ε) p g)=0
      rw [←Module.End.mul_apply,sub_mul_normOp _ p (action_order ε),
        LinearMap.zero_apply]
    · intro hf
      obtain ⟨g,c,hg⟩:=hDifference f hf
      refine ⟨g,?_⟩
      simpa only [smul_zero,add_zero] using hg.symm
  · apply Submodule.ext
    intro f
    constructor
    · rintro ⟨g,rfl⟩
      change normOp (action (K:=K) ε) p ((1-action (K:=K) ε) g)=0
      rw [←Module.End.mul_apply,normOp_mul_sub _ p (action_order ε),
        LinearMap.zero_apply]
    · intro hf
      obtain ⟨g,c,hg⟩:=hNorm f hf
      refine ⟨g,?_⟩
      simpa only [smul_zero,add_zero] using hg.symm

/-- The concrete polynomial-matrix convention used by generic supports:
row b reads the coefficient at b+ε. -/
def translateMatrix (R : Type*) [Ring R] (ε : Labels p J) :
    Matrix (Labels p J) (Labels p J) R := by
  classical
  exact fun b c=>if c=b+ε then 1 else 0

theorem translateMatrix_mulVecLin {K : Type*} [Field K] (ε : Labels p J) :
    (translateMatrix K ε).mulVecLin=action ε := by
  classical
  apply LinearMap.ext
  intro f
  funext b
  simp [translateMatrix,action,Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct,ite_mul]

def normMatrix (R : Type*) [Ring R] (ε : Labels p J) :
    Matrix (Labels p J) (Labels p J) R := ∑i∈Finset.range p,(translateMatrix R ε)^i

theorem normMatrix_mulVecLin {K : Type*} [Field K] (ε : Labels p J) :
    (normMatrix K ε).mulVecLin=normOp (action ε) p := by
  classical
  unfold normMatrix normOp
  change Matrix.toLin' (∑i∈Finset.range p,(translateMatrix K ε)^i)=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change Matrix.toLin' ((translateMatrix K ε)^i)=(action (K:=K) ε)^i
  rw [Matrix.toLin'_pow,Matrix.toLin'_apply',translateMatrix_mulVecLin]

/-- Specialized complementary ranks. This uses exactness/rank-nullity,
without counting cyclic orbit representatives or Jordan blocks. -/
theorem translate_rank_sum {K : Type*} [Field K]
    (ε : Labels p J) (j₀ : J) (hε : ε j₀≠0) :
    (1-translateMatrix K ε).rank+(normMatrix K ε).rank=Fintype.card (Labels p J) := by
  classical
  have hExact:=(action_exact (K:=K) ε j₀ hε).1
  have hNullity:=(1-action (K:=K) ε).finrank_range_add_finrank_ker
  rw [←hExact,Module.finrank_fintype_fun_eq_card] at hNullity
  change Module.finrank K (LinearMap.range (1-translateMatrix K ε).mulVecLin)+
    Module.finrank K (LinearMap.range (normMatrix K ε).mulVecLin)=_
  have hSub : (1-translateMatrix K ε).mulVecLin=1-action ε := by
    change Matrix.toLin' (1-translateMatrix K ε)=_
    simp only [map_sub,Matrix.toLin'_one,Matrix.toLin'_apply',Matrix.mulVecLin_one,
      translateMatrix_mulVecLin,Module.End.one_eq_id]
  rw [hSub,normMatrix_mulVecLin]
  exact hNullity

/-- The same rank sum in the generator-minus-one convention used by the
actual shifted displacement. Kernels agree since the two maps are negatives. -/
theorem difference_rank_sum {K : Type*} [Field K]
    (ε : Labels p J) (j₀ : J) (hε : ε j₀≠0) :
    (translateMatrix K ε-1).rank+(normMatrix K ε).rank=Fintype.card (Labels p J) := by
  classical
  have hKernel : LinearMap.ker (action (K:=K) ε-1)=LinearMap.ker (1-action ε) := by
    apply Submodule.ext
    intro f
    simp only [LinearMap.mem_ker,LinearMap.sub_apply,Module.End.one_apply,sub_eq_zero]
    exact eq_comm
  have hNullity:=(action (K:=K) ε-1).finrank_range_add_finrank_ker
  rw [hKernel,←(action_exact (K:=K) ε j₀ hε).1,
    Module.finrank_fintype_fun_eq_card] at hNullity
  have hSub : (translateMatrix K ε-1).mulVecLin=action ε-1 := by
    change Matrix.toLin' (translateMatrix K ε-1)=_
    simp only [map_sub,Matrix.toLin'_one,Matrix.toLin'_apply',Matrix.mulVecLin_one,
      translateMatrix_mulVecLin,Module.End.one_eq_id]
  change Module.finrank K (LinearMap.range (translateMatrix K ε-1).mulVecLin)+
    Module.finrank K (LinearMap.range (normMatrix K ε).mulVecLin)=_
  rw [hSub,normMatrix_mulVecLin]
  exact hNullity

end FairDivision.Topology.Volovikov.CyclicLabelBlockExactness
