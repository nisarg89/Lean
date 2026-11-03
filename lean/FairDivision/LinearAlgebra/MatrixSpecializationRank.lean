import FairDivision.LinearAlgebra.RankMinorConverse
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Specialization cannot increase generic matrix rank

A nonzero minor after specialization was already a nonzero polynomial
minor. An injective map to a generic coefficient field preserves that
nonzero determinant. Reuse the shared rank-by-minors proof originally
written for FE; BF's shifted-cyclic argument imports no FE certificate.

No evaluation map on the fraction field is assumed: such a map need not
exist when denominators vanish at the specialization. All determinant
transport takes place in the original coefficient ring.
-/

set_option autoImplicit false

namespace FairDivision.LinearAlgebra

/-- Compare specialization with an injective generic coefficient map.
The source ring is arbitrary; the two destination coefficient rings are
fields so the existing rank-by-minors criterion applies directly. -/
theorem rank_specialization_le_generic
    {R K L : Type*} [CommRing R] [Field K] [Field L]
    {m n : Type*} [Fintype m] [Fintype n]
    (generic : R→+*K) (hGeneric : Function.Injective generic)
    (specialize : R→+*L) (A : Matrix m n R) :
    (A.map specialize).rank≤(A.map generic).rank := by
  classical
  obtain ⟨rows,cols,hDet⟩:=exists_nonzero_minor_at_rank (A.map specialize)
  have hSpecialized : specialize ((A.submatrix rows cols).det)≠0 := by
    intro hZero
    apply hDet
    rw [Matrix.submatrix_map]
    change (specialize.mapMatrix (A.submatrix rows cols)).det=0
    rw [←specialize.map_det]
    exact hZero
  have hOriginal : (A.submatrix rows cols).det≠0 := by
    intro hZero
    exact hSpecialized (by rw [hZero,map_zero])
  have hGenericDet : ((A.map generic).submatrix rows cols).det≠0 := by
    rw [Matrix.submatrix_map]
    change (generic.mapMatrix (A.submatrix rows cols)).det≠0
    rw [←generic.map_det]
    intro hZero
    apply hOriginal
    exact hGeneric (by simpa only [map_zero] using hZero)
  simpa only [Fintype.card_fin] using
    rank_at_least_of_nonzero_minor (A.map generic) rows cols hGenericDet

/-- In particular, specialization rank is bounded by rank over any
fraction field of the original integral domain. -/
theorem rank_specialization_le_fractionField
    {R K L : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field L]
    {m n : Type*} [Fintype m] [Fintype n]
    (specialize : R→+*L) (A : Matrix m n R) :
    (A.map specialize).rank≤(A.map (algebraMap R K)).rank :=
  rank_specialization_le_generic (algebraMap R K) (IsFractionRing.injective R K) specialize A

/-- The exact polynomial matrix specialization needed by the elementary
abelian shifted-cyclic obstruction. Every finite row and column type is
allowed, not just square permutation matrices. -/
theorem rank_polynomial_evaluation_le_fractionRing
    {F σ m n : Type*} [Field F] [Fintype m] [Fintype n]
    (values : σ→F) (A : Matrix m n (MvPolynomial σ F)) :
    (A.map (MvPolynomial.eval₂Hom (RingHom.id F) values)).rank≤
      (A.map (algebraMap (MvPolynomial σ F) (FractionRing (MvPolynomial σ F)))).rank :=
  rank_specialization_le_fractionField (MvPolynomial.eval₂Hom (RingHom.id F) values) A

/-- Dimension saturation turns the elementary range/kernel inclusion into
equality. This is Mathlib rank-nullity and equality of finite-dimensional
submodules, specialized to the matrix representation used by the chain maps. -/
theorem matrix_range_eq_ker_of_rank_sum
    {K ι : Type*} [Field K] [Fintype ι]
    (A B : Matrix ι ι K) (hAB : A*B=0)
    (hRank : Fintype.card ι≤A.rank+B.rank) :
    LinearMap.range B.mulVecLin=LinearMap.ker A.mulVecLin := by
  have hInclusion : LinearMap.range B.mulVecLin≤LinearMap.ker A.mulVecLin := by
    rw [LinearMap.range_le_ker_iff,←Matrix.mulVecLin_mul,hAB,Matrix.mulVecLin_zero]
  apply Submodule.eq_of_le_of_finrank_le hInclusion
  have hNullity := A.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at hNullity
  change Module.finrank K (LinearMap.ker A.mulVecLin)≤B.rank
  change A.rank+Module.finrank K (LinearMap.ker A.mulVecLin)=Fintype.card ι at hNullity
  omega

/-- If a specialized pair is dimension-exact and its generic composition
vanishes, specialization monotonicity forces generic exactness. No division
by the group order or specialization of rational denominators is involved. -/
theorem generic_pair_range_eq_ker
    {R K L ι : Type*} [CommRing R] [Field K] [Field L] [Fintype ι]
    (generic : R→+*K) (hGeneric : Function.Injective generic)
    (specialize : R→+*L) (A B : Matrix ι ι R)
    (hAB : A*B=0)
    (hSpecial : Fintype.card ι≤(A.map specialize).rank+(B.map specialize).rank) :
    LinearMap.range (B.map generic).mulVecLin=LinearMap.ker (A.map generic).mulVecLin := by
  apply matrix_range_eq_ker_of_rank_sum
  · rw [←Matrix.map_mul,hAB]
    ext i j
    simp
  · have hA := rank_specialization_le_generic generic hGeneric specialize A
    have hB := rank_specialization_le_generic generic hGeneric specialize B
    omega

/-- Two-sided generic norm/difference exactness follows from a single
specialization having complementary ranks and the two nilpotent product
identities. This is the finite permutation-orbit case needed by BF's
external elementary-abelian obstruction. -/
theorem generic_pair_exact
    {R K L ι : Type*} [CommRing R] [Field K] [Field L] [Fintype ι]
    (generic : R→+*K) (hGeneric : Function.Injective generic)
    (specialize : R→+*L) (A B : Matrix ι ι R)
    (hAB : A*B=0) (hBA : B*A=0)
    (hSpecial : (A.map specialize).rank+(B.map specialize).rank=Fintype.card ι) :
    LinearMap.range (B.map generic).mulVecLin=LinearMap.ker (A.map generic).mulVecLin ∧
    LinearMap.range (A.map generic).mulVecLin=LinearMap.ker (B.map generic).mulVecLin := by
  constructor
  · exact generic_pair_range_eq_ker generic hGeneric specialize A B hAB hSpecial.ge
  · apply generic_pair_range_eq_ker generic hGeneric specialize B A hBA
    omega

end FairDivision.LinearAlgebra
