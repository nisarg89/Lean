import FairDivision.Topology.Volovikov.CyclicLabelBlockExactness
import Mathlib.LinearAlgebra.Matrix.CharP

/-!
# Generic shifted-cyclic exactness on every nonempty character-support block

Use independent polynomial weights X_q for the genuine generators. On a
block of label assignments b:J→Z/p, the displacement is the actual matrix
Σ_q X_q (P_{ε_q}−1). It is p-nilpotent. Specialize just one weight to 1
and all others to 0; whenever that generator moves one occupied color,
the specialized difference/norm ranks sum to the block's dimension.
Specialization cannot increase generic rank, so the generic displacement
and its (p−1)-power are exact in both directions over the fraction field.

Crucially, the chosen generator may depend on the occupied-color block.
The independent variables, and hence the final shifted operator, remain
one common family for all blocks. No cyclic subgroup is asserted to act
freely on the entire twisted target.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.Topology.Volovikov.ShiftedCyclicSupportMatrices

open scoped BigOperators Classical
open Dvoretzky.Dold
open CyclicLabelBlockExactness
open FairDivision.LinearAlgebra

variable {p r : ℕ} [Fact p.Prime] {J : Type*} [Fintype J]

abbrev Coefficients (p r : ℕ) := MvPolynomial (Fin r) (ZMod p)
abbrev GenericField (p r : ℕ) := FractionRing (Coefficients p r)

/-- Literal translation matrices compose by addition of label shifts. -/
theorem translateMatrix_add {R : Type*} [CommRing R]
    (ε η : Labels p J) :
    translateMatrix R ε*translateMatrix R η=translateMatrix R (ε+η) := by
  classical
  ext b c
  change (∑ j : Labels p J,
    (if j=b+ε then (1 : R) else 0)*(if c=j+η then (1 : R) else 0))=
      (if c=b+(ε+η) then (1 : R) else 0)
  rw [Finset.sum_eq_single (b+ε)]
  · rw [if_pos rfl,one_mul]
    simp only [add_assoc]
  · intro j _ hj
    rw [if_neg hj,zero_mul]
  · intro h
    exact (h (Finset.mem_univ (b+ε))).elim

@[simp] theorem translateMatrix_zero {R : Type*} [CommRing R] :
    translateMatrix R (0 : Labels p J)=1 := by
  classical
  ext b c
  simp [translateMatrix,Matrix.one_apply,eq_comm]

/-- This statement is proved in the coefficient ring, before passing to
its fraction field or specializing any polynomial variable. -/
theorem translateMatrix_power {R : Type*} [CommRing R]
    (ε : Labels p J) (n : ℕ) :
    (translateMatrix R ε)^n=translateMatrix R (n•ε) := by
  induction n with
  | zero=>simp
  | succ n ih=>
      rw [pow_succ,ih,translateMatrix_add]
      congr 1
      simp only [succ_nsmul]

@[simp] theorem translateMatrix_order {R : Type*} [CommRing R]
    (ε : Labels p J) : (translateMatrix R ε)^p=1 := by
  rw [translateMatrix_power,p_smul_labels,translateMatrix_zero]

theorem translateMatrix_commute {R : Type*} [CommRing R]
    (ε η : Labels p J) : Commute (translateMatrix R ε) (translateMatrix R η) := by
  change translateMatrix R ε*translateMatrix R η=translateMatrix R η*translateMatrix R ε
  rw [translateMatrix_add,translateMatrix_add,add_comm ε η]

@[simp] theorem translateMatrix_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R→+*S) (ε : Labels p J) :
    (translateMatrix R ε).map f=translateMatrix S ε := by
  classical
  ext b c
  simp [translateMatrix,Matrix.map_apply]

/-- Actual common polynomial displacement on this occupied-color block. -/
def difference (ε : Fin r→Labels p J) :
    Matrix (Labels p J) (Labels p J) (Coefficients p r) :=
  ∑q : Fin r,(MvPolynomial.X q : Coefficients p r)•
    (translateMatrix (Coefficients p r) (ε q)-1)

/-- The complementary operator is the actual (p−1)-power, not an
independently chosen matrix with a stipulated kernel. -/
def norm (ε : Fin r→Labels p J) :
    Matrix (Labels p J) (Labels p J) (Coefficients p r) := (difference ε)^(p-1)

theorem difference_power (ε : Fin r→Labels p J) : (difference ε)^p=0 := by
  classical
  unfold difference
  apply ShiftedCyclicAlgebra.sum_pow_zero p
  · intro q hq k hk
    exact ((((translateMatrix_commute (ε q) (ε k)).sub_right (Commute.one_right _)).sub_left
      (Commute.one_left _)).smul_left (MvPolynomial.X q)).smul_right (MvPolynomial.X k)
  · intro q hq
    rw [smul_pow,sub_pow_char_of_commute p (Commute.one_right _),
      translateMatrix_order,one_pow,sub_self,smul_zero]

theorem difference_mul_norm (ε : Fin r→Labels p J) : difference ε*norm ε=0 := by
  unfold norm
  rw [←pow_succ']
  have hp : p-1+1=p:=Nat.sub_add_cancel (Fact.out : p.Prime).one_le
  rw [hp,difference_power]

theorem norm_mul_difference (ε : Fin r→Labels p J) : norm ε*difference ε=0 := by
  unfold norm
  rw [←pow_succ]
  have hp : p-1+1=p:=Nat.sub_add_cancel (Fact.out : p.Prime).one_le
  rw [hp,difference_power]

/-- A specialization selecting one genuine generator, in the ORIGINAL
polynomial ring; no evaluation map on the fraction field is used. -/
def selectGenerator (q : Fin r) : Coefficients p r→+*ZMod p :=
  MvPolynomial.eval₂Hom (RingHom.id _) (Pi.single q 1)

theorem difference_select (ε : Fin r→Labels p J) (q : Fin r) :
    (difference ε).map (selectGenerator q)=translateMatrix (ZMod p) (ε q)-1 := by
  classical
  ext b c
  simp [difference,selectGenerator,Matrix.map_apply,Matrix.sum_apply,Matrix.smul_apply,
    Matrix.sub_apply,Matrix.one_apply,translateMatrix,Pi.single_apply,smul_eq_mul]

/-- The specialized complementary power is the usual cyclic norm. The
polynomial identity from ShiftedCyclicAlgebra retains odd-prime signs. -/
theorem norm_select (ε : Fin r→Labels p J) (q : Fin r) :
    (norm ε).map (selectGenerator q)=normMatrix (ZMod p) (ε q) := by
  classical
  change (selectGenerator q).mapMatrix ((difference ε)^(p-1))=_
  rw [map_pow]
  change ((difference ε).map (selectGenerator q))^(p-1)=_
  rw [difference_select]
  have h:=ShiftedCyclicAlgebra.norm_one_add p (ZMod p)
    (translateMatrix (ZMod p) (ε q)-1)
  have hBase : (1 : Matrix (Labels p J) (Labels p J) (ZMod p))+
      (translateMatrix (ZMod p) (ε q)-1)=translateMatrix (ZMod p) (ε q) := by abel
  simpa only [hBase,normMatrix] using h.symm

/-- Two-sided generic exactness with the local nonzero-character datum
fully discharged by the actual cyclic transversal proof. -/
theorem generic_exact (ε : Fin r→Labels p J) (q : Fin r) (j₀ : J)
    (hε : ε q j₀≠0) :
    LinearMap.range ((norm ε).map
      (algebraMap (Coefficients p r) (GenericField p r))).mulVecLin=
      LinearMap.ker ((difference ε).map
        (algebraMap (Coefficients p r) (GenericField p r))).mulVecLin ∧
    LinearMap.range ((difference ε).map
      (algebraMap (Coefficients p r) (GenericField p r))).mulVecLin=
      LinearMap.ker ((norm ε).map
        (algebraMap (Coefficients p r) (GenericField p r))).mulVecLin := by
  have hSpecializedRank :
      ((difference ε).map (selectGenerator q)).rank+
        ((norm ε).map (selectGenerator q)).rank=Fintype.card (Labels p J) := by
    rw [difference_select,norm_select]
    exact difference_rank_sum (ε q) j₀ hε
  exact generic_pair_exact
    (algebraMap (Coefficients p r) (GenericField p r))
    (IsFractionRing.injective (Coefficients p r) (GenericField p r)) (selectGenerator q)
    (difference ε) (norm ε) (difference_mul_norm ε) (norm_mul_difference ε)
    hSpecializedRank

/-- Every occupied-color block may choose its own useful generator. This
is the hypothesis supplied by nontriviality of each target character. -/
theorem generic_exact_of_nonempty (ε : Fin r→Labels p J)
    (hJ : Nonempty J) (hNontrivial : ∀j : J,∃q : Fin r,ε q j≠0) :
    LinearMap.range ((norm ε).map
      (algebraMap (Coefficients p r) (GenericField p r))).mulVecLin=
      LinearMap.ker ((difference ε).map
        (algebraMap (Coefficients p r) (GenericField p r))).mulVecLin ∧
    LinearMap.range ((difference ε).map
      (algebraMap (Coefficients p r) (GenericField p r))).mulVecLin=
      LinearMap.ker ((norm ε).map
        (algebraMap (Coefficients p r) (GenericField p r))).mulVecLin := by
  obtain ⟨j⟩:=hJ
  obtain ⟨q,hq⟩:=hNontrivial j
  exact generic_exact ε q j hq

/-- The actual generic scalar weights, shared between every target block
and the source cone sequence. -/
def weights (q : Fin r) : GenericField p r :=
  algebraMap (Coefficients p r) (GenericField p r) (MvPolynomial.X q)

/-- Coefficient transport of the displacement is entrywise ring mapping,
not a specialization of a rational function with possibly zero denominator. -/
theorem difference_map {K : Type*} [Field K]
    (f : Coefficients p r→+*K) (ε : Fin r→Labels p J) :
    (difference ε).map f=∑q : Fin r,f (MvPolynomial.X q)•(translateMatrix K (ε q)-1) := by
  classical
  ext b c
  simp [difference,Matrix.map_apply,Matrix.sum_apply,Matrix.smul_apply,Matrix.sub_apply,
    Matrix.one_apply,translateMatrix,map_sum,map_sub,map_mul,smul_eq_mul]

theorem generic_difference_linear (ε : Fin r→Labels p J) :
    ((difference ε).map (algebraMap (Coefficients p r) (GenericField p r))).mulVecLin=
      ShiftedCyclicAlgebra.displacement (weights (p:=p) (r:=r))
        (fun q=>action (K:=GenericField p r) (ε q)) := by
  classical
  rw [difference_map]
  change Matrix.toLin' (∑q : Fin r,
    weights q•(translateMatrix (GenericField p r) (ε q)-1))=_
  let T : Matrix (Labels p J) (Labels p J) (GenericField p r) ≃ₗ[GenericField p r]
      ((Labels p J → GenericField p r) →ₗ[GenericField p r]
        (Labels p J → GenericField p r)) := Matrix.toLin'
  change T.toLinearMap.toAddMonoidHom (∑ q : Fin r,
    weights q • (translateMatrix (GenericField p r) (ε q) - 1)) = _
  rw [map_sum]
  unfold ShiftedCyclicAlgebra.displacement
  apply Finset.sum_congr rfl
  intro q hq
  change T (weights q • (translateMatrix (GenericField p r) (ε q) - 1)) = _
  rw [T.map_smul]
  have hSub : T (translateMatrix (GenericField p r) (ε q) - 1) =
      T (translateMatrix (GenericField p r) (ε q)) - T 1 :=
    T.map_sub (translateMatrix (GenericField p r) (ε q)) 1
  rw [hSub]
  simp only [T, Matrix.toLin'_apply', translateMatrix_mulVecLin,
    Matrix.mulVecLin_one, Module.End.one_eq_id]

theorem generic_norm_linear (ε : Fin r→Labels p J) :
    ((norm ε).map (algebraMap (Coefficients p r) (GenericField p r))).mulVecLin=
      (ShiftedCyclicAlgebra.displacement (weights (p:=p) (r:=r))
        (fun q=>action (K:=GenericField p r) (ε q)))^(p-1) := by
  classical
  unfold norm
  change Matrix.toLin' ((algebraMap (Coefficients p r) (GenericField p r)).mapMatrix
    ((difference ε)^(p-1)))=_
  rw [map_pow,Matrix.toLin'_pow]
  change (((difference ε).map
    (algebraMap (Coefficients p r) (GenericField p r))).mulVecLin)^(p-1)=_
  rw [generic_difference_linear]

/-- The support-block endpoint in the same endomorphism language as the
source shifted cyclic sequence and the oriented target chain action. -/
theorem displacement_exact (ε : Fin r→Labels p J)
    (hJ : Nonempty J) (hNontrivial : ∀j : J,∃q : Fin r,ε q j≠0) :
    let u:=ShiftedCyclicAlgebra.displacement (weights (p:=p) (r:=r))
      (fun q=>action (K:=GenericField p r) (ε q))
    LinearMap.range (u^(p-1))=LinearMap.ker u ∧
      LinearMap.range u=LinearMap.ker (u^(p-1)) := by
  have h:=generic_exact_of_nonempty ε hJ hNontrivial
  simpa only [generic_norm_linear,generic_difference_linear] using h

end FairDivision.Topology.Volovikov.ShiftedCyclicSupportMatrices
