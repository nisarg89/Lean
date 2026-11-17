import RandomSizeMetricDistortion.Numerics.Finite0.Common
set_option linter.all false
set_option maxHeartbeats 0
set_option maxRecDepth 0
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
open scoped BigOperators
open Set

namespace MetricDistortion.Contracts.Numerics_FiniteFamily0
namespace Cell80_high_internal_top
private noncomputable def qValues : Fin 4 → ℚ := ![(2560194441361411634035332625786753705/3139746840559905098530757082937511738 : ℚ),(6000415769046838870700000000000000000/4709620260839857647796135624406267607 : ℚ),(48025976461681748192444566168687221083/17497194926901001805723840371623039515 : ℚ),(-6067798831014036795741000000000000000/3499438985380200361144768074324607903 : ℚ)]
private noncomputable abbrev e2 : PolyExpr := SharedFiniteSemantics22.e2 qValues
private noncomputable abbrev e10 : PolyExpr := SharedFiniteSemantics22.e10 qValues
private noncomputable abbrev e14 : PolyExpr := SharedFiniteSemantics22.e14 qValues
private noncomputable abbrev e18 : PolyExpr := SharedFiniteSemantics22.e18 qValues
private noncomputable abbrev e62 : PolyExpr := SharedFiniteSemantics22.e62 qValues
private noncomputable abbrev e144 : PolyExpr := SharedFiniteSemantics22.e144 qValues
private noncomputable abbrev node_1 := SharedFiniteSemantics22.node_1 qValues
private noncomputable abbrev node_2 := SharedFiniteSemantics22.node_2 qValues
private noncomputable abbrev node_3 := SharedFiniteSemantics22.node_3 qValues
private noncomputable abbrev node_4 := SharedFiniteSemantics22.node_4 qValues
private noncomputable abbrev node_5 := SharedFiniteSemantics22.node_5 qValues
private noncomputable abbrev node_6 := SharedFiniteSemantics22.node_6 qValues
private noncomputable abbrev node_7 := SharedFiniteSemantics22.node_7 qValues
private noncomputable abbrev node_8 := SharedFiniteSemantics22.node_8 qValues
private noncomputable abbrev node_9 := SharedFiniteSemantics22.node_9 qValues
private noncomputable abbrev node_10 := SharedFiniteSemantics22.node_10 qValues
private noncomputable abbrev node_11 := SharedFiniteSemantics22.node_11 qValues
private noncomputable abbrev node_12 := SharedFiniteSemantics22.node_12 qValues
private noncomputable abbrev node_13 := SharedFiniteSemantics22.node_13 qValues
private noncomputable abbrev node_14 := SharedFiniteSemantics22.node_14 qValues
private noncomputable abbrev node_15 := SharedFiniteSemantics22.node_15 qValues
private noncomputable abbrev node_16 := SharedFiniteSemantics22.node_16 qValues
private noncomputable abbrev node_17 := SharedFiniteSemantics22.node_17 qValues
private noncomputable abbrev node_18 := SharedFiniteSemantics22.node_18 qValues
private noncomputable abbrev node_19 := SharedFiniteSemantics22.node_19 qValues
private noncomputable abbrev node_20 := SharedFiniteSemantics22.node_20 qValues
private noncomputable abbrev node_21 := SharedFiniteSemantics22.node_21 qValues
private noncomputable abbrev node_40 := SharedFiniteSemantics22.node_40 qValues
private noncomputable abbrev node_41 := SharedFiniteSemantics22.node_41 qValues
private noncomputable abbrev node_42 := SharedFiniteSemantics22.node_42 qValues
private noncomputable abbrev node_43 := SharedFiniteSemantics22.node_43 qValues
private noncomputable abbrev node_44 := SharedFiniteSemantics22.node_44 qValues
private noncomputable abbrev node_58 := SharedFiniteSemantics22.node_58 qValues
private noncomputable abbrev node_59 := SharedFiniteSemantics22.node_59 qValues
private noncomputable abbrev node_60 := SharedFiniteSemantics22.node_60 qValues
private noncomputable abbrev node_61 := SharedFiniteSemantics22.node_61 qValues
private noncomputable abbrev node_62 := SharedFiniteSemantics22.node_62 qValues
private noncomputable abbrev node_93 := SharedFiniteSemantics22.node_93 qValues
private noncomputable abbrev node_94 := SharedFiniteSemantics22.node_94 qValues
private noncomputable abbrev node_106 := SharedFiniteSemantics22.node_106 qValues
private noncomputable abbrev node_107 := SharedFiniteSemantics22.node_107 qValues
private noncomputable abbrev node_108 := SharedFiniteSemantics22.node_108 qValues
private noncomputable abbrev node_109 := SharedFiniteSemantics22.node_109 qValues
private noncomputable abbrev node_110 := SharedFiniteSemantics22.node_110 qValues
private noncomputable abbrev node_111 := SharedFiniteSemantics22.node_111 qValues
private noncomputable abbrev node_112 := SharedFiniteSemantics22.node_112 qValues
private noncomputable abbrev node_113 := SharedFiniteSemantics22.node_113 qValues
private noncomputable abbrev node_114 := SharedFiniteSemantics22.node_114 qValues
private noncomputable abbrev node_115 := SharedFiniteSemantics22.node_115 qValues
private noncomputable abbrev node_116 := SharedFiniteSemantics22.node_116 qValues
private noncomputable abbrev node_117 := SharedFiniteSemantics22.node_117 qValues
private noncomputable abbrev node_118 := SharedFiniteSemantics22.node_118 qValues
private noncomputable abbrev node_119 := SharedFiniteSemantics22.node_119 qValues
private noncomputable abbrev node_124 := SharedFiniteSemantics22.node_124 qValues
private noncomputable abbrev node_125 := SharedFiniteSemantics22.node_125 qValues
private noncomputable abbrev node_126 := SharedFiniteSemantics22.node_126 qValues
private noncomputable abbrev node_127 := SharedFiniteSemantics22.node_127 qValues
private noncomputable abbrev node_128 := SharedFiniteSemantics22.node_128 qValues
private noncomputable abbrev node_129 := SharedFiniteSemantics22.node_129 qValues
private noncomputable abbrev node_143 := SharedFiniteSemantics22.node_143 qValues
private noncomputable abbrev node_144 := SharedFiniteSemantics22.node_144 qValues
private noncomputable abbrev semantic_H_81 := SharedFiniteSemantics22.semantic_H_81 qValues
private noncomputable abbrev semantic_H_92 := SharedFiniteSemantics22.semantic_H_92 qValues
private noncomputable abbrev semantic_H_105 := SharedFiniteSemantics22.semantic_H_105 qValues
private noncomputable abbrev semantic_psi_39 := SharedFiniteSemantics22.semantic_psi_39 qValues
private noncomputable abbrev semantic_psi_57 := SharedFiniteSemantics22.semantic_psi_57 qValues
private noncomputable abbrev semantic_psi_142 := SharedFiniteSemantics22.semantic_psi_142 qValues
private noncomputable def aPoint (x : Fin 4 → ℝ) : ℝ := bStar+(x 0-bStar)*x 1
private noncomputable def capPoint (x : Fin 4 → ℝ) : ℝ := x 0+(1-x 0)*x 2
private noncomputable def rPoint (x : Fin 4 → ℝ) : ℝ := capPoint x+(1-capPoint x)*x 3
private noncomputable def yPoint (x : Fin 4 → ℝ) : ℝ := aPoint x+capPoint x-x 0
private theorem point_10 (x : Fin 4 → ℝ) : eval e10 x = aPoint x := by
  simp only [node_2,node_3,node_6,node_7,node_8,node_9,node_10] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_18 (x : Fin 4 → ℝ) : eval e18 x = rPoint x := by
  simp only [node_1,node_2,node_4,node_5,node_11,node_12,node_13,node_14,node_15,node_16,node_17,node_18] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_2 (x : Fin 4 → ℝ) : eval e2 x = x 0 := by
  simp only [node_2] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_14 (x : Fin 4 → ℝ) : eval e14 x = capPoint x := by
  simp only [node_1,node_2,node_4,node_11,node_12,node_13,node_14] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_62 (x : Fin 4 → ℝ) : eval e62 x = yPoint x := by
  simp only [node_1,node_2,node_3,node_4,node_6,node_7,node_8,node_9,node_10,node_11,node_12,node_13,node_14,node_61,node_62] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem price_lambda_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceLambda 80 p = ((2560194441361411634035332625786753705/3139746840559905098530757082937511738 : ℝ)+(6000415769046838870700000000000000000/4709620260839857647796135624406267607 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell80,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 80 p = (((48025976461681748192444566168687221083/17497194926901001805723840371623039515 : ℝ)+(-6067798831014036795741000000000000000/3499438985380200361144768074324607903 : ℝ)*p)-(145513/100000 : ℝ)*(1/1 : ℝ))/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell80,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e144 x = (x 0*(1-x 0))*(aPoint x+priceLambda 80 (x 0)*(HStar (yPoint x)-HStar (aPoint x)-HStar (capPoint x))+priceTau 80 (x 0)*psiStar (rPoint x)+(cStar-aPoint x-eta (0 : Fin 9)*psiStar (aPoint x))-(cStar-capPoint x-eta (0 : Fin 9)*psiStar (capPoint x))) := by
  have hp0 : x 0 ≠ 0 := ne_of_gt hp.1
  have hp1 : x 0 ≠ 1 := ne_of_lt hp.2
  have heps : 1-x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  rw [price_lambda_normal _ hp,price_tau_normal _ hp]
  simp only [node_1,node_11,node_12,node_15,node_19,node_20,node_21,node_40,node_41,node_42,node_43,node_44,node_58,node_59,node_60,node_93,node_94,node_106,node_107,node_108,node_109,node_110,node_111,node_112,node_113,node_114,node_115,node_116,node_117,node_118,node_119,node_124,node_125,node_126,node_127,node_128,node_129,node_143,node_144,semantic_H_81,semantic_H_92,semantic_H_105,semantic_psi_39,semantic_psi_57,semantic_psi_142,point_10,point_18,point_2,point_14,point_62]
  norm_num [qValues,eta,etas,Fin.val_zero,sourceDenom,muStar,cStar] at *
  generalize HStar (yPoint x) = z0 at *
  generalize HStar (aPoint x) = z1 at *
  generalize psiStar (aPoint x) = z2 at *
  generalize psiStar (rPoint x) = z3 at *
  generalize HStar (capPoint x) = z4 at *
  generalize psiStar (capPoint x) = z5 at *
  generalize sourceB (capPoint x) = z6 at *
  generalize sourceJ (yPoint x) (capPoint x) = z7 at *
  generalize sourcePD (capPoint x) (rPoint x) (rPoint x-capPoint x) = z8 at *
  generalize sourceF0 (aPoint x) = z9 at *
  generalize sourceInc (aPoint x) (1-x 0) = z10 at *
  generalize sourceInc (aPoint x) ((1-x 0)*x 2) = z11 at *
  generalize sourcePD (aPoint x) (rPoint x) (rPoint x-aPoint x) = z12 at *
  field_simp [hp0,heps] <;> ring
theorem actual_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) (ha : bStar < aPoint x) (hA : bStar < capPoint x)
    (hL : lambdaStar (x 0) = priceLambda 80 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 80 (x 0)) :
    (1)*eval e144 x = (x 0*(1-x 0))*(internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_neg (not_le.mpr ha),if_neg (not_le.mpr hA),hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (2864583333333333/5000000000000000 : ℚ) (2916666666666667/5000000000000000 : ℚ)) x → eval e144 x ≤ 0)
    (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((2864583333333333/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((2916666666666667/5000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 80 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 80 p)
    (hkb : ((2916666666666667/5000000000000000 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((2864583333333333/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r)
    (hcase : bStar < a) :
    internalResidual (0 : Fin 9) a p A r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxA,hxr⟩ := h7 (2864583333333333/5000000000000000 : ℚ) (2916666666666667/5000000000000000 : ℚ) bStar p a A r hpcell hkb hr.2 hap hcase hpA hAr
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,capPoint] using hxa
  have hAx : capPoint x = A := by simpa only [aPoint,rPoint,capPoint] using hxA
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,capPoint] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 80 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 80 (x 0) := by simpa only [hxp] using hT
  have hflag : bStar < aPoint x := by simpa only [hax] using hcase
  have hflagA : bStar < capPoint x := by rw [hAx]; exact hcase.trans_le (hap.trans hpA)
  have hb := hbound x hx
  have hv : (1 : ℝ)*eval e144 x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 1) hb
  rw [actual_identity hs x hpx hflag hflagA hLx hTx] at hv
  have hscale : 0 < x 0*(1-x 0) := mul_pos hpx.1 (sub_pos.mpr hpx.2)
  have hv : internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x) ≤ 0 := le_of_not_gt (fun hpos => (not_lt_of_ge hv) (mul_pos hscale hpos))
  simpa only [hxp,hax,hAx,hrx] using hv
private noncomputable def tape : List TapeOp := [
.const (1/1 : ℚ),
.var 0,
.var 1,
.var 2,
.var 3,
.const (2840189/5000000 : ℚ),
.const (-2840189/5000000 : ℚ),
.add 1 6,
.mul 7 2,
.add 5 8,
.neg 1,
.add 0 10,
.mul 11 3,
.add 1 12,
.neg 13,
.add 0 14,
.mul 15 4,
.add 13 16,
.const (113609/200000 : ℚ),
.neg 9,
.add 18 19,
.const (1085/4818 : ℚ),
.const (19/73 : ℚ),
.mul 22 9,
.mul 9 9,
.const (35/146 : ℚ),
.mul 25 24,
.add 23 26,
.mul 24 24,
.mul 28 28,
.mul 29 29,
.mul 30 30,
.const (1/2 : ℚ),
.mul 32 31,
.add 27 33,
.neg 34,
.add 21 35,
.const (4818/3733 : ℚ),
.mul 37 36,
.const (145513/100000 : ℚ),
.mul 39 38,
.neg 40,
.add 20 41,
.add 18 14,
.mul 22 13,
.mul 13 13,
.mul 25 45,
.add 44 46,
.mul 45 45,
.mul 48 48,
.mul 49 49,
.mul 50 50,
.mul 32 51,
.add 47 52,
.neg 53,
.add 21 54,
.mul 37 55,
.mul 39 56,
.neg 57,
.add 43 58,
.add 9 13,
.add 60 10,
.mul 21 61,
.mul 61 61,
.const (19/146 : ℚ),
.mul 64 63,
.mul 61 63,
.const (35/438 : ℚ),
.mul 67 66,
.add 65 68,
.mul 63 63,
.mul 70 70,
.mul 71 71,
.mul 72 72,
.mul 61 73,
.const (1/66 : ℚ),
.mul 75 74,
.add 69 76,
.neg 77,
.add 62 78,
.mul 37 79,
.mul 21 9,
.mul 64 24,
.mul 9 24,
.mul 67 83,
.add 82 84,
.mul 9 31,
.mul 75 86,
.add 85 87,
.neg 88,
.add 81 89,
.mul 37 90,
.neg 91,
.add 80 92,
.mul 21 13,
.mul 64 45,
.mul 13 45,
.mul 67 96,
.add 95 97,
.mul 13 51,
.mul 75 99,
.add 98 100,
.neg 101,
.add 94 102,
.mul 37 103,
.neg 104,
.add 93 105,
.const (2560194441361411634035332625786753705/3139746840559905098530757082937511738 : ℚ),
.const (6000415769046838870700000000000000000/4709620260839857647796135624406267607 : ℚ),
.mul 108 1,
.add 107 109,
.const (48025976461681748192444566168687221083/17497194926901001805723840371623039515 : ℚ),
.const (-6067798831014036795741000000000000000/3499438985380200361144768074324607903 : ℚ),
.mul 112 1,
.add 111 113,
.mul 1 11,
.const (-145513/100000 : ℚ),
.add 114 116,
.mul 117 115,
.add 9 42,
.neg 59,
.add 119 120,
.mul 121 115,
.mul 110 106,
.add 122 123,
.mul 22 17,
.mul 17 17,
.mul 25 126,
.add 125 127,
.mul 126 126,
.mul 129 129,
.mul 130 130,
.mul 131 131,
.mul 32 132,
.add 128 133,
.neg 134,
.add 21 135,
.mul 37 136,
.mul 118 137,
.add 124 138]
private noncomputable def ssaQVals : Fin 18 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(-2840189/5000000 : ℚ),(113609/200000 : ℚ),(1085/4818 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ),(4818/3733 : ℚ),(145513/100000 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(2560194441361411634035332625786753705/3139746840559905098530757082937511738 : ℚ),(6000415769046838870700000000000000000/4709620260839857647796135624406267607 : ℚ),(48025976461681748192444566168687221083/17497194926901001805723840371623039515 : ℚ),(-6067798831014036795741000000000000000/3499438985380200361144768074324607903 : ℚ),(-145513/100000 : ℚ)]
private theorem ssa_tape : MetricDistortion.OptimizedSSAFinite0.S_13a624ffc1a70c2e.p140 ssaQVals = tape := by rfl
private noncomputable def computed (D : Int) (B : Fin 4 → FixedTape.I) : FixedTape.Row :=
  MetricDistortion.OptimizedSSAFinite0.S_13a624ffc1a70c2e.computed ssaQVals D B
private theorem ssa_matches (D : Int) (B : Fin 4 → FixedTape.I) :
    (FixedTape.rowsAux D B [] tape).getD 139 FixedTape.zeroRow = computed D B := by
  rw [←ssa_tape]
  exact MetricDistortion.OptimizedSSAFinite0.S_13a624ffc1a70c2e.ssa_matches ssaQVals D B

attribute [irreducible] computed
private noncomputable def faceI (B : Fin 4 → FixedTape.I) (i : Fin 4) (upper : Bool) : Fin 4 → FixedTape.I :=
  Function.update B i (let z := if upper then (B i).hi else (B i).lo; ⟨z,z⟩)
private noncomputable def splitI (B : Fin 4 → FixedTape.I) (i : Fin 4) (z : Int) (upper : Bool) : Fin 4 → FixedTape.I :=
  Function.update B i (if upper then ⟨z,(B i).hi⟩ else ⟨(B i).lo,z⟩)
private theorem decode_face (D : Int) (B : Fin 4 → FixedTape.I) (i : Fin 4) (upper : Bool) :
    faceBox (FixedTape.decodeBox D B) i upper = FixedTape.decodeBox D (faceI B i upper) := by
  funext j
  by_cases hj : j=i
  · subst j
    cases upper <;> simp [faceBox,faceI,FixedTape.decodeBox,FixedTape.decode]
  · simp [faceBox,faceI,FixedTape.decodeBox,FixedTape.decode,hj]
private theorem decode_split (D : Int) (B : Fin 4 → FixedTape.I) (i : Fin 4) (z : Int) (upper : Bool) :
    splitBox (FixedTape.decodeBox D B) i ((z : ℚ)/(D : ℚ)) upper = FixedTape.decodeBox D (splitI B i z upper) := by
  funext j
  by_cases hj : j=i
  · subst j
    cases upper <;> simp [splitBox,splitI,FixedTape.decodeBox,FixedTape.decode]
  · simp [splitBox,splitI,FixedTape.decodeBox,FixedTape.decode,hj]
private theorem decode_zeroRow (D : Int) : FixedTape.decodeRow D FixedTape.zeroRow = zeroTapeBounds := by
  simp [FixedTape.decodeRow,FixedTape.decode,FixedTape.zeroRow,FixedTape.zero,zeroTapeBounds]
private noncomputable def denominator : Int := 205894999931330970547583306564244056623571868593525835003764792036651507324251612307907831398400000000000000000000000
private theorem denominator_positive : 0 < denominator := by decide +kernel
private noncomputable def candidateRows (B : Fin 4 → FixedTape.I) : List TapeBounds :=
  (FixedTape.rowsAux denominator B [] tape).map (FixedTape.decodeRow denominator)
private theorem root_in_range : 139 < tape.length := by decide +kernel
private theorem references_valid : tapeRefsValidAux 0 tape = true := by decide +kernel
private theorem candidate_valid (h : Needs) (B : Fin 4 → FixedTape.I) :
    tapeCheck (FixedTape.decodeBox denominator B) tape (candidateRows B) = true :=
  h.child_10.1 denominator denominator_positive B tape references_valid
private theorem candidate_root (B : Fin 4 → FixedTape.I) :
    (candidateRows B).getD 139 zeroTapeBounds = FixedTape.decodeRow denominator (computed denominator B) := by
  unfold candidateRows
  rw [←decode_zeroRow denominator,List.getD_map,ssa_matches]
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨117960677043991688149886273963700120935034278765437068066115672535942592486866350441305040121892512806144573440000000,120105416626609746545756924251207069535970694295827178656987368256435712856799576289713389932507487193855426560000000⟩,⟨0,205894999931330970547583306564244056623571868593525835003764792036651507324251612307907831398400000000000000000000000⟩,⟨0,205894999931330970547583306564244056623571868593525835003764792036651507324251612307907831398400000000000000000000000⟩,⟨0,205894999931330970547583306564244056623571868593525835003764792036651507324251612307907831398400000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := splitI ibox0 2 102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 false
private noncomputable def ibox2 : Fin 4 → FixedTape.I := faceI ibox1 3 false
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 2 51473749982832742636895826641061014155892967148381458750941198009162876831062903076976957849600000000000000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 2 25736874991416371318447913320530507077946483574190729375470599004581438415531451538488478924800000000000000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox4 0 119033046835300717347821599107453595235502486530632123361551520396189152671832963365509215027200000000000000000000000 false
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox5 0 118496861939646202748853936535576858085268382648034595713833596466065872579349656903407127574546256403072286720000000 false
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox6 2 12868437495708185659223956660265253538973241787095364687735299502290719207765725769244239462400000000000000000000000 false
private noncomputable def ibox8 : Fin 4 → FixedTape.I := faceI ibox7 2 false
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox8 1 102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 false
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox8 1 102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 true
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox6 2 12868437495708185659223956660265253538973241787095364687735299502290719207765725769244239462400000000000000000000000 true
private noncomputable def ibox12 : Fin 4 → FixedTape.I := faceI ibox11 2 false
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox5 0 118496861939646202748853936535576858085268382648034595713833596466065872579349656903407127574546256403072286720000000 true
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox13 2 12868437495708185659223956660265253538973241787095364687735299502290719207765725769244239462400000000000000000000000 false
private noncomputable def ibox15 : Fin 4 → FixedTape.I := faceI ibox14 2 false
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox15 1 102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 false
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox15 1 102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 true
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox13 2 12868437495708185659223956660265253538973241787095364687735299502290719207765725769244239462400000000000000000000000 true
private noncomputable def ibox19 : Fin 4 → FixedTape.I := faceI ibox18 2 false
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox4 0 119033046835300717347821599107453595235502486530632123361551520396189152671832963365509215027200000000000000000000000 true
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox20 1 102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 false
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox21 2 12868437495708185659223956660265253538973241787095364687735299502290719207765725769244239462400000000000000000000000 false
private noncomputable def ibox23 : Fin 4 → FixedTape.I := splitI ibox22 0 119569231730955231946789261679330332385736590413229651009269444326312432764316269827611302479853743596927713280000000 false
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox22 0 119569231730955231946789261679330332385736590413229651009269444326312432764316269827611302479853743596927713280000000 true
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox21 2 12868437495708185659223956660265253538973241787095364687735299502290719207765725769244239462400000000000000000000000 true
private noncomputable def ibox26 : Fin 4 → FixedTape.I := splitI ibox25 0 119569231730955231946789261679330332385736590413229651009269444326312432764316269827611302479853743596927713280000000 false
private noncomputable def ibox27 : Fin 4 → FixedTape.I := splitI ibox25 0 119569231730955231946789261679330332385736590413229651009269444326312432764316269827611302479853743596927713280000000 true
private noncomputable def ibox28 : Fin 4 → FixedTape.I := splitI ibox20 1 102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 true
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox28 2 12868437495708185659223956660265253538973241787095364687735299502290719207765725769244239462400000000000000000000000 false
private noncomputable def ibox30 : Fin 4 → FixedTape.I := splitI ibox29 1 154421249948498227910687479923183042467678901445144376252823594027488630493188709230930873548800000000000000000000000 false
private noncomputable def ibox31 : Fin 4 → FixedTape.I := splitI ibox30 0 119569231730955231946789261679330332385736590413229651009269444326312432764316269827611302479853743596927713280000000 false
private noncomputable def ibox32 : Fin 4 → FixedTape.I := splitI ibox30 0 119569231730955231946789261679330332385736590413229651009269444326312432764316269827611302479853743596927713280000000 true
private noncomputable def ibox33 : Fin 4 → FixedTape.I := splitI ibox29 1 154421249948498227910687479923183042467678901445144376252823594027488630493188709230930873548800000000000000000000000 true
private noncomputable def ibox34 : Fin 4 → FixedTape.I := splitI ibox33 2 6434218747854092829611978330132626769486620893547682343867649751145359603882862884622119731200000000000000000000000 false
private noncomputable def ibox35 : Fin 4 → FixedTape.I := faceI ibox34 2 false
private noncomputable def ibox36 : Fin 4 → FixedTape.I := splitI ibox33 2 6434218747854092829611978330132626769486620893547682343867649751145359603882862884622119731200000000000000000000000 true
private noncomputable def ibox37 : Fin 4 → FixedTape.I := splitI ibox28 2 12868437495708185659223956660265253538973241787095364687735299502290719207765725769244239462400000000000000000000000 true
private noncomputable def ibox38 : Fin 4 → FixedTape.I := splitI ibox37 1 154421249948498227910687479923183042467678901445144376252823594027488630493188709230930873548800000000000000000000000 false
private noncomputable def ibox39 : Fin 4 → FixedTape.I := splitI ibox37 1 154421249948498227910687479923183042467678901445144376252823594027488630493188709230930873548800000000000000000000000 true
private noncomputable def ibox40 : Fin 4 → FixedTape.I := splitI ibox3 2 25736874991416371318447913320530507077946483574190729375470599004581438415531451538488478924800000000000000000000000 true
private noncomputable def ibox41 : Fin 4 → FixedTape.I := splitI ibox40 0 119033046835300717347821599107453595235502486530632123361551520396189152671832963365509215027200000000000000000000000 false
private noncomputable def ibox42 : Fin 4 → FixedTape.I := splitI ibox41 2 38605312487124556977671869980795760616919725361286094063205898506872157623297177307732718387200000000000000000000000 false
private noncomputable def ibox43 : Fin 4 → FixedTape.I := splitI ibox42 1 102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 false
private noncomputable def ibox44 : Fin 4 → FixedTape.I := splitI ibox42 1 102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 true
private noncomputable def ibox45 : Fin 4 → FixedTape.I := splitI ibox41 2 38605312487124556977671869980795760616919725361286094063205898506872157623297177307732718387200000000000000000000000 true
private noncomputable def ibox46 : Fin 4 → FixedTape.I := faceI ibox45 2 false
private noncomputable def ibox47 : Fin 4 → FixedTape.I := splitI ibox46 1 102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 false
private noncomputable def ibox48 : Fin 4 → FixedTape.I := splitI ibox46 1 102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 true
private noncomputable def ibox49 : Fin 4 → FixedTape.I := splitI ibox40 0 119033046835300717347821599107453595235502486530632123361551520396189152671832963365509215027200000000000000000000000 true
private noncomputable def ibox50 : Fin 4 → FixedTape.I := splitI ibox49 1 102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 false
private noncomputable def ibox51 : Fin 4 → FixedTape.I := splitI ibox50 2 38605312487124556977671869980795760616919725361286094063205898506872157623297177307732718387200000000000000000000000 false
private noncomputable def ibox52 : Fin 4 → FixedTape.I := splitI ibox50 2 38605312487124556977671869980795760616919725361286094063205898506872157623297177307732718387200000000000000000000000 true
private noncomputable def ibox53 : Fin 4 → FixedTape.I := splitI ibox49 1 102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 true
private noncomputable def ibox54 : Fin 4 → FixedTape.I := splitI ibox53 2 38605312487124556977671869980795760616919725361286094063205898506872157623297177307732718387200000000000000000000000 false
private noncomputable def ibox55 : Fin 4 → FixedTape.I := splitI ibox53 2 38605312487124556977671869980795760616919725361286094063205898506872157623297177307732718387200000000000000000000000 true
private noncomputable def ibox56 : Fin 4 → FixedTape.I := splitI ibox2 2 51473749982832742636895826641061014155892967148381458750941198009162876831062903076976957849600000000000000000000000 true
private noncomputable def ibox57 : Fin 4 → FixedTape.I := splitI ibox56 2 77210624974249113955343739961591521233839450722572188126411797013744315246594354615465436774400000000000000000000000 false
private noncomputable def ibox58 : Fin 4 → FixedTape.I := splitI ibox57 0 119033046835300717347821599107453595235502486530632123361551520396189152671832963365509215027200000000000000000000000 false
private noncomputable def ibox59 : Fin 4 → FixedTape.I := splitI ibox58 2 64342187478540928296119783301326267694866208935476823438676497511453596038828628846221197312000000000000000000000000 false
private noncomputable def ibox60 : Fin 4 → FixedTape.I := splitI ibox58 2 64342187478540928296119783301326267694866208935476823438676497511453596038828628846221197312000000000000000000000000 true
private noncomputable def ibox61 : Fin 4 → FixedTape.I := splitI ibox57 0 119033046835300717347821599107453595235502486530632123361551520396189152671832963365509215027200000000000000000000000 true
private noncomputable def ibox62 : Fin 4 → FixedTape.I := splitI ibox61 2 64342187478540928296119783301326267694866208935476823438676497511453596038828628846221197312000000000000000000000000 false
private noncomputable def ibox63 : Fin 4 → FixedTape.I := splitI ibox61 2 64342187478540928296119783301326267694866208935476823438676497511453596038828628846221197312000000000000000000000000 true
private noncomputable def ibox64 : Fin 4 → FixedTape.I := splitI ibox56 2 77210624974249113955343739961591521233839450722572188126411797013744315246594354615465436774400000000000000000000000 true
private noncomputable def ibox65 : Fin 4 → FixedTape.I := splitI ibox64 0 119033046835300717347821599107453595235502486530632123361551520396189152671832963365509215027200000000000000000000000 false
private noncomputable def ibox66 : Fin 4 → FixedTape.I := splitI ibox64 0 119033046835300717347821599107453595235502486530632123361551520396189152671832963365509215027200000000000000000000000 true
private noncomputable def ibox67 : Fin 4 → FixedTape.I := splitI ibox0 2 102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 true
private noncomputable def ibox68 : Fin 4 → FixedTape.I := splitI ibox67 3 102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 false
private noncomputable def ibox69 : Fin 4 → FixedTape.I := splitI ibox68 2 154421249948498227910687479923183042467678901445144376252823594027488630493188709230930873548800000000000000000000000 false
private noncomputable def ibox70 : Fin 4 → FixedTape.I := faceI ibox69 3 false
private noncomputable def ibox71 : Fin 4 → FixedTape.I := splitI ibox70 2 128684374957081856592239566602652535389732417870953646877352995022907192077657257692442394624000000000000000000000000 false
private noncomputable def ibox72 : Fin 4 → FixedTape.I := splitI ibox71 0 119033046835300717347821599107453595235502486530632123361551520396189152671832963365509215027200000000000000000000000 false
private noncomputable def ibox73 : Fin 4 → FixedTape.I := splitI ibox71 0 119033046835300717347821599107453595235502486530632123361551520396189152671832963365509215027200000000000000000000000 true
private noncomputable def ibox74 : Fin 4 → FixedTape.I := splitI ibox70 2 128684374957081856592239566602652535389732417870953646877352995022907192077657257692442394624000000000000000000000000 true
private noncomputable def ibox75 : Fin 4 → FixedTape.I := splitI ibox74 2 141552812452790042251463523262917788928705659658049011565088294525197911285422983461686634086400000000000000000000000 false
private noncomputable def ibox76 : Fin 4 → FixedTape.I := splitI ibox74 2 141552812452790042251463523262917788928705659658049011565088294525197911285422983461686634086400000000000000000000000 true
private noncomputable def ibox77 : Fin 4 → FixedTape.I := splitI ibox68 2 154421249948498227910687479923183042467678901445144376252823594027488630493188709230930873548800000000000000000000000 true
private noncomputable def ibox78 : Fin 4 → FixedTape.I := splitI ibox77 2 180158124939914599229135393243713549545625385019335105628294193032070068908720160769419352473600000000000000000000000 false
private noncomputable def ibox79 : Fin 4 → FixedTape.I := faceI ibox78 3 false
private noncomputable def ibox80 : Fin 4 → FixedTape.I := splitI ibox79 2 167289687444206413569911436583448296006652143232239740940558893529779349700954435000175113011200000000000000000000000 false
private noncomputable def ibox81 : Fin 4 → FixedTape.I := splitI ibox79 2 167289687444206413569911436583448296006652143232239740940558893529779349700954435000175113011200000000000000000000000 true
private noncomputable def ibox82 : Fin 4 → FixedTape.I := splitI ibox77 2 180158124939914599229135393243713549545625385019335105628294193032070068908720160769419352473600000000000000000000000 true
private noncomputable def ibox83 : Fin 4 → FixedTape.I := splitI ibox82 2 193026562435622784888359349903978803084598626806430470316029492534360788116485886538663591936000000000000000000000000 false
private noncomputable def ibox84 : Fin 4 → FixedTape.I := faceI ibox83 2 false
private noncomputable def ibox85 : Fin 4 → FixedTape.I := splitI ibox82 2 193026562435622784888359349903978803084598626806430470316029492534360788116485886538663591936000000000000000000000000 true
private noncomputable def ibox86 : Fin 4 → FixedTape.I := faceI ibox85 2 false
private noncomputable def ibox87 : Fin 4 → FixedTape.I := splitI ibox67 3 102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 true
private noncomputable def ibox88 : Fin 4 → FixedTape.I := splitI ibox87 2 154421249948498227910687479923183042467678901445144376252823594027488630493188709230930873548800000000000000000000000 false
private noncomputable def ibox89 : Fin 4 → FixedTape.I := faceI ibox88 3 false
private noncomputable def ibox90 : Fin 4 → FixedTape.I := splitI ibox89 2 128684374957081856592239566602652535389732417870953646877352995022907192077657257692442394624000000000000000000000000 false
private noncomputable def ibox91 : Fin 4 → FixedTape.I := splitI ibox90 2 115815937461373670933015609942387281850759176083858282189617695520616472869891531923198155161600000000000000000000000 false
private noncomputable def ibox92 : Fin 4 → FixedTape.I := splitI ibox90 2 115815937461373670933015609942387281850759176083858282189617695520616472869891531923198155161600000000000000000000000 true
private noncomputable def ibox93 : Fin 4 → FixedTape.I := splitI ibox89 2 128684374957081856592239566602652535389732417870953646877352995022907192077657257692442394624000000000000000000000000 true
private noncomputable def ibox94 : Fin 4 → FixedTape.I := splitI ibox93 2 141552812452790042251463523262917788928705659658049011565088294525197911285422983461686634086400000000000000000000000 false
private noncomputable def ibox95 : Fin 4 → FixedTape.I := splitI ibox93 2 141552812452790042251463523262917788928705659658049011565088294525197911285422983461686634086400000000000000000000000 true
private noncomputable def ibox96 : Fin 4 → FixedTape.I := splitI ibox87 2 154421249948498227910687479923183042467678901445144376252823594027488630493188709230930873548800000000000000000000000 true
private noncomputable def ibox97 : Fin 4 → FixedTape.I := splitI ibox96 2 180158124939914599229135393243713549545625385019335105628294193032070068908720160769419352473600000000000000000000000 false
private noncomputable def ibox98 : Fin 4 → FixedTape.I := faceI ibox97 3 false
private noncomputable def ibox99 : Fin 4 → FixedTape.I := splitI ibox98 2 167289687444206413569911436583448296006652143232239740940558893529779349700954435000175113011200000000000000000000000 false
private noncomputable def ibox100 : Fin 4 → FixedTape.I := splitI ibox98 2 167289687444206413569911436583448296006652143232239740940558893529779349700954435000175113011200000000000000000000000 true
private noncomputable def ibox101 : Fin 4 → FixedTape.I := splitI ibox96 2 180158124939914599229135393243713549545625385019335105628294193032070068908720160769419352473600000000000000000000000 true
private noncomputable def ibox102 : Fin 4 → FixedTape.I := splitI ibox101 2 193026562435622784888359349903978803084598626806430470316029492534360788116485886538663591936000000000000000000000000 false
private noncomputable def ibox103 : Fin 4 → FixedTape.I := faceI ibox102 2 false
private noncomputable def ibox104 : Fin 4 → FixedTape.I := splitI ibox101 2 193026562435622784888359349903978803084598626806430470316029492534360788116485886538663591936000000000000000000000000 true
private noncomputable def ibox105 : Fin 4 → FixedTape.I := faceI ibox104 2 false
private noncomputable def tree105 : TapeTree := .direct (candidateRows ibox105)
attribute [irreducible] tree105
private theorem sign_105 : (computed denominator ibox105).value.hi ≤ 0 := by decide +kernel
private theorem accepted_105 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox105) tree105 = true := by
  simp only [tree105,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  refine ⟨root_in_range,candidate_valid h ibox105,?_⟩
  rw [candidate_root]
  simpa [FixedTape.decodeRow,FixedTape.decode] using (h.child_10.2.2.2.1 denominator (computed denominator ibox105).value.hi denominator_positive).1 sign_105
private noncomputable def tree104 : TapeTree := .face 2 false (candidateRows ibox104) tree105
attribute [irreducible] tree104
private theorem sign_104 : ((computed denominator ibox104).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_104 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox104) tree104 = true := by
  simp only [tree104,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox104,?_,accepted_105 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox104)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox104).gradient 2).hi) denominator_positive).1 sign_104
private noncomputable def tree103 : TapeTree := .direct (candidateRows ibox103)
attribute [irreducible] tree103
private theorem sign_103 : (computed denominator ibox103).value.hi ≤ 0 := by decide +kernel
private theorem accepted_103 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox103) tree103 = true := by
  simp only [tree103,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  refine ⟨root_in_range,candidate_valid h ibox103,?_⟩
  rw [candidate_root]
  simpa [FixedTape.decodeRow,FixedTape.decode] using (h.child_10.2.2.2.1 denominator (computed denominator ibox103).value.hi denominator_positive).1 sign_103
private noncomputable def tree102 : TapeTree := .face 2 false (candidateRows ibox102) tree103
attribute [irreducible] tree102
private theorem sign_102 : ((computed denominator ibox102).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_102 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox102) tree102 = true := by
  simp only [tree102,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox102,?_,accepted_103 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox102)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox102).gradient 2).hi) denominator_positive).1 sign_102
private noncomputable def tree101 : TapeTree := .split 2 (((193026562435622784888359349903978803084598626806430470316029492534360788116485886538663591936000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree102 tree104
attribute [irreducible] tree101
private theorem accepted_101 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox101) tree101 = true := by
  simp only [tree101,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox101 2 (193026562435622784888359349903978803084598626806430470316029492534360788116485886538663591936000000000000000000000000 : Int) false,decode_split denominator ibox101 2 (193026562435622784888359349903978803084598626806430470316029492534360788116485886538663591936000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_102 h,accepted_104 h⟩
private noncomputable def tree100 : TapeTree := .centered (candidateRows ibox100) (candidateRows (FixedTape.midBox ibox100))
attribute [irreducible] tree100
private theorem sign_100 : 2*denominator*(computed denominator (FixedTape.midBox ibox100)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox100).gradient k).lo.natAbs ((computed denominator ibox100).gradient k).hi.natAbs : Int)*((ibox100 k).hi-(ibox100 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox100
    (computed denominator ibox100) (computed denominator (FixedTape.midBox ibox100))
    (by decide +kernel)
private theorem midpoint_even_100 : ∀ k, 2 ∣ (ibox100 k).lo+(ibox100 k).hi := by decide +kernel
private theorem accepted_100 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox100) tree100 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox100 midpoint_even_100
  simp only [tree100,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox100,candidate_valid h (FixedTape.midBox ibox100),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox100 139 (FixedTape.rowsAux denominator ibox100 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox100) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_100
private noncomputable def tree99 : TapeTree := .centered (candidateRows ibox99) (candidateRows (FixedTape.midBox ibox99))
attribute [irreducible] tree99
private theorem sign_99 : 2*denominator*(computed denominator (FixedTape.midBox ibox99)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox99).gradient k).lo.natAbs ((computed denominator ibox99).gradient k).hi.natAbs : Int)*((ibox99 k).hi-(ibox99 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox99
    (computed denominator ibox99) (computed denominator (FixedTape.midBox ibox99))
    (by decide +kernel)
private theorem midpoint_even_99 : ∀ k, 2 ∣ (ibox99 k).lo+(ibox99 k).hi := by decide +kernel
private theorem accepted_99 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox99) tree99 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox99 midpoint_even_99
  simp only [tree99,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox99,candidate_valid h (FixedTape.midBox ibox99),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox99 139 (FixedTape.rowsAux denominator ibox99 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox99) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_99
private noncomputable def tree98 : TapeTree := .split 2 (((167289687444206413569911436583448296006652143232239740940558893529779349700954435000175113011200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree99 tree100
attribute [irreducible] tree98
private theorem accepted_98 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox98) tree98 = true := by
  simp only [tree98,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox98 2 (167289687444206413569911436583448296006652143232239740940558893529779349700954435000175113011200000000000000000000000 : Int) false,decode_split denominator ibox98 2 (167289687444206413569911436583448296006652143232239740940558893529779349700954435000175113011200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_99 h,accepted_100 h⟩
private noncomputable def tree97 : TapeTree := .face 3 false (candidateRows ibox97) tree98
attribute [irreducible] tree97
private theorem sign_97 : ((computed denominator ibox97).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_97 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox97) tree97 = true := by
  simp only [tree97,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox97,?_,accepted_98 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox97)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox97).gradient 3).hi) denominator_positive).1 sign_97
private noncomputable def tree96 : TapeTree := .split 2 (((180158124939914599229135393243713549545625385019335105628294193032070068908720160769419352473600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree97 tree101
attribute [irreducible] tree96
private theorem accepted_96 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox96) tree96 = true := by
  simp only [tree96,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox96 2 (180158124939914599229135393243713549545625385019335105628294193032070068908720160769419352473600000000000000000000000 : Int) false,decode_split denominator ibox96 2 (180158124939914599229135393243713549545625385019335105628294193032070068908720160769419352473600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_97 h,accepted_101 h⟩
private noncomputable def tree95 : TapeTree := .centered (candidateRows ibox95) (candidateRows (FixedTape.midBox ibox95))
attribute [irreducible] tree95
private theorem sign_95 : 2*denominator*(computed denominator (FixedTape.midBox ibox95)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox95).gradient k).lo.natAbs ((computed denominator ibox95).gradient k).hi.natAbs : Int)*((ibox95 k).hi-(ibox95 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox95
    (computed denominator ibox95) (computed denominator (FixedTape.midBox ibox95))
    (by decide +kernel)
private theorem midpoint_even_95 : ∀ k, 2 ∣ (ibox95 k).lo+(ibox95 k).hi := by decide +kernel
private theorem accepted_95 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox95) tree95 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox95 midpoint_even_95
  simp only [tree95,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox95,candidate_valid h (FixedTape.midBox ibox95),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox95 139 (FixedTape.rowsAux denominator ibox95 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox95) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_95
private noncomputable def tree94 : TapeTree := .centered (candidateRows ibox94) (candidateRows (FixedTape.midBox ibox94))
attribute [irreducible] tree94
private theorem sign_94 : 2*denominator*(computed denominator (FixedTape.midBox ibox94)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox94).gradient k).lo.natAbs ((computed denominator ibox94).gradient k).hi.natAbs : Int)*((ibox94 k).hi-(ibox94 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox94
    (computed denominator ibox94) (computed denominator (FixedTape.midBox ibox94))
    (by decide +kernel)
private theorem midpoint_even_94 : ∀ k, 2 ∣ (ibox94 k).lo+(ibox94 k).hi := by decide +kernel
private theorem accepted_94 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox94) tree94 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox94 midpoint_even_94
  simp only [tree94,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox94,candidate_valid h (FixedTape.midBox ibox94),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox94 139 (FixedTape.rowsAux denominator ibox94 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox94) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_94
private noncomputable def tree93 : TapeTree := .split 2 (((141552812452790042251463523262917788928705659658049011565088294525197911285422983461686634086400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree94 tree95
attribute [irreducible] tree93
private theorem accepted_93 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox93) tree93 = true := by
  simp only [tree93,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox93 2 (141552812452790042251463523262917788928705659658049011565088294525197911285422983461686634086400000000000000000000000 : Int) false,decode_split denominator ibox93 2 (141552812452790042251463523262917788928705659658049011565088294525197911285422983461686634086400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_94 h,accepted_95 h⟩
private noncomputable def tree92 : TapeTree := .centered (candidateRows ibox92) (candidateRows (FixedTape.midBox ibox92))
attribute [irreducible] tree92
private theorem sign_92 : 2*denominator*(computed denominator (FixedTape.midBox ibox92)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox92).gradient k).lo.natAbs ((computed denominator ibox92).gradient k).hi.natAbs : Int)*((ibox92 k).hi-(ibox92 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox92
    (computed denominator ibox92) (computed denominator (FixedTape.midBox ibox92))
    (by decide +kernel)
private theorem midpoint_even_92 : ∀ k, 2 ∣ (ibox92 k).lo+(ibox92 k).hi := by decide +kernel
private theorem accepted_92 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox92) tree92 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox92 midpoint_even_92
  simp only [tree92,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox92,candidate_valid h (FixedTape.midBox ibox92),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox92 139 (FixedTape.rowsAux denominator ibox92 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox92) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_92
private noncomputable def tree91 : TapeTree := .centered (candidateRows ibox91) (candidateRows (FixedTape.midBox ibox91))
attribute [irreducible] tree91
private theorem sign_91 : 2*denominator*(computed denominator (FixedTape.midBox ibox91)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox91).gradient k).lo.natAbs ((computed denominator ibox91).gradient k).hi.natAbs : Int)*((ibox91 k).hi-(ibox91 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox91
    (computed denominator ibox91) (computed denominator (FixedTape.midBox ibox91))
    (by decide +kernel)
private theorem midpoint_even_91 : ∀ k, 2 ∣ (ibox91 k).lo+(ibox91 k).hi := by decide +kernel
private theorem accepted_91 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox91) tree91 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox91 midpoint_even_91
  simp only [tree91,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox91,candidate_valid h (FixedTape.midBox ibox91),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox91 139 (FixedTape.rowsAux denominator ibox91 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox91) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_91
private noncomputable def tree90 : TapeTree := .split 2 (((115815937461373670933015609942387281850759176083858282189617695520616472869891531923198155161600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree91 tree92
attribute [irreducible] tree90
private theorem accepted_90 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox90) tree90 = true := by
  simp only [tree90,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox90 2 (115815937461373670933015609942387281850759176083858282189617695520616472869891531923198155161600000000000000000000000 : Int) false,decode_split denominator ibox90 2 (115815937461373670933015609942387281850759176083858282189617695520616472869891531923198155161600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_91 h,accepted_92 h⟩
private noncomputable def tree89 : TapeTree := .split 2 (((128684374957081856592239566602652535389732417870953646877352995022907192077657257692442394624000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree90 tree93
attribute [irreducible] tree89
private theorem accepted_89 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox89) tree89 = true := by
  simp only [tree89,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox89 2 (128684374957081856592239566602652535389732417870953646877352995022907192077657257692442394624000000000000000000000000 : Int) false,decode_split denominator ibox89 2 (128684374957081856592239566602652535389732417870953646877352995022907192077657257692442394624000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_90 h,accepted_93 h⟩
private noncomputable def tree88 : TapeTree := .face 3 false (candidateRows ibox88) tree89
attribute [irreducible] tree88
private theorem sign_88 : ((computed denominator ibox88).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_88 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox88) tree88 = true := by
  simp only [tree88,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox88,?_,accepted_89 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox88)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox88).gradient 3).hi) denominator_positive).1 sign_88
private noncomputable def tree87 : TapeTree := .split 2 (((154421249948498227910687479923183042467678901445144376252823594027488630493188709230930873548800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree88 tree96
attribute [irreducible] tree87
private theorem accepted_87 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox87) tree87 = true := by
  simp only [tree87,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox87 2 (154421249948498227910687479923183042467678901445144376252823594027488630493188709230930873548800000000000000000000000 : Int) false,decode_split denominator ibox87 2 (154421249948498227910687479923183042467678901445144376252823594027488630493188709230930873548800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_88 h,accepted_96 h⟩
private noncomputable def tree86 : TapeTree := .direct (candidateRows ibox86)
attribute [irreducible] tree86
private theorem sign_86 : (computed denominator ibox86).value.hi ≤ 0 := by decide +kernel
private theorem accepted_86 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox86) tree86 = true := by
  simp only [tree86,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  refine ⟨root_in_range,candidate_valid h ibox86,?_⟩
  rw [candidate_root]
  simpa [FixedTape.decodeRow,FixedTape.decode] using (h.child_10.2.2.2.1 denominator (computed denominator ibox86).value.hi denominator_positive).1 sign_86
private noncomputable def tree85 : TapeTree := .face 2 false (candidateRows ibox85) tree86
attribute [irreducible] tree85
private theorem sign_85 : ((computed denominator ibox85).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_85 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox85) tree85 = true := by
  simp only [tree85,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox85,?_,accepted_86 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox85)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox85).gradient 2).hi) denominator_positive).1 sign_85
private noncomputable def tree84 : TapeTree := .direct (candidateRows ibox84)
attribute [irreducible] tree84
private theorem sign_84 : (computed denominator ibox84).value.hi ≤ 0 := by decide +kernel
private theorem accepted_84 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox84) tree84 = true := by
  simp only [tree84,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  refine ⟨root_in_range,candidate_valid h ibox84,?_⟩
  rw [candidate_root]
  simpa [FixedTape.decodeRow,FixedTape.decode] using (h.child_10.2.2.2.1 denominator (computed denominator ibox84).value.hi denominator_positive).1 sign_84
private noncomputable def tree83 : TapeTree := .face 2 false (candidateRows ibox83) tree84
attribute [irreducible] tree83
private theorem sign_83 : ((computed denominator ibox83).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_83 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox83) tree83 = true := by
  simp only [tree83,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox83,?_,accepted_84 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox83)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox83).gradient 2).hi) denominator_positive).1 sign_83
private noncomputable def tree82 : TapeTree := .split 2 (((193026562435622784888359349903978803084598626806430470316029492534360788116485886538663591936000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree83 tree85
attribute [irreducible] tree82
private theorem accepted_82 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox82) tree82 = true := by
  simp only [tree82,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox82 2 (193026562435622784888359349903978803084598626806430470316029492534360788116485886538663591936000000000000000000000000 : Int) false,decode_split denominator ibox82 2 (193026562435622784888359349903978803084598626806430470316029492534360788116485886538663591936000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_83 h,accepted_85 h⟩
private noncomputable def tree81 : TapeTree := .centered (candidateRows ibox81) (candidateRows (FixedTape.midBox ibox81))
attribute [irreducible] tree81
private theorem sign_81 : 2*denominator*(computed denominator (FixedTape.midBox ibox81)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox81).gradient k).lo.natAbs ((computed denominator ibox81).gradient k).hi.natAbs : Int)*((ibox81 k).hi-(ibox81 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox81
    (computed denominator ibox81) (computed denominator (FixedTape.midBox ibox81))
    (by decide +kernel)
private theorem midpoint_even_81 : ∀ k, 2 ∣ (ibox81 k).lo+(ibox81 k).hi := by decide +kernel
private theorem accepted_81 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox81) tree81 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox81 midpoint_even_81
  simp only [tree81,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox81,candidate_valid h (FixedTape.midBox ibox81),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox81 139 (FixedTape.rowsAux denominator ibox81 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox81) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_81
private noncomputable def tree80 : TapeTree := .centered (candidateRows ibox80) (candidateRows (FixedTape.midBox ibox80))
attribute [irreducible] tree80
private theorem sign_80 : 2*denominator*(computed denominator (FixedTape.midBox ibox80)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox80).gradient k).lo.natAbs ((computed denominator ibox80).gradient k).hi.natAbs : Int)*((ibox80 k).hi-(ibox80 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox80
    (computed denominator ibox80) (computed denominator (FixedTape.midBox ibox80))
    (by decide +kernel)
private theorem midpoint_even_80 : ∀ k, 2 ∣ (ibox80 k).lo+(ibox80 k).hi := by decide +kernel
private theorem accepted_80 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox80) tree80 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox80 midpoint_even_80
  simp only [tree80,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox80,candidate_valid h (FixedTape.midBox ibox80),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox80 139 (FixedTape.rowsAux denominator ibox80 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox80) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_80
private noncomputable def tree79 : TapeTree := .split 2 (((167289687444206413569911436583448296006652143232239740940558893529779349700954435000175113011200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree80 tree81
attribute [irreducible] tree79
private theorem accepted_79 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox79) tree79 = true := by
  simp only [tree79,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox79 2 (167289687444206413569911436583448296006652143232239740940558893529779349700954435000175113011200000000000000000000000 : Int) false,decode_split denominator ibox79 2 (167289687444206413569911436583448296006652143232239740940558893529779349700954435000175113011200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_80 h,accepted_81 h⟩
private noncomputable def tree78 : TapeTree := .face 3 false (candidateRows ibox78) tree79
attribute [irreducible] tree78
private theorem sign_78 : ((computed denominator ibox78).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_78 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox78) tree78 = true := by
  simp only [tree78,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox78,?_,accepted_79 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox78)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox78).gradient 3).hi) denominator_positive).1 sign_78
private noncomputable def tree77 : TapeTree := .split 2 (((180158124939914599229135393243713549545625385019335105628294193032070068908720160769419352473600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree78 tree82
attribute [irreducible] tree77
private theorem accepted_77 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox77) tree77 = true := by
  simp only [tree77,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox77 2 (180158124939914599229135393243713549545625385019335105628294193032070068908720160769419352473600000000000000000000000 : Int) false,decode_split denominator ibox77 2 (180158124939914599229135393243713549545625385019335105628294193032070068908720160769419352473600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_78 h,accepted_82 h⟩
private noncomputable def tree76 : TapeTree := .centered (candidateRows ibox76) (candidateRows (FixedTape.midBox ibox76))
attribute [irreducible] tree76
private theorem sign_76 : 2*denominator*(computed denominator (FixedTape.midBox ibox76)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox76).gradient k).lo.natAbs ((computed denominator ibox76).gradient k).hi.natAbs : Int)*((ibox76 k).hi-(ibox76 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox76
    (computed denominator ibox76) (computed denominator (FixedTape.midBox ibox76))
    (by decide +kernel)
private theorem midpoint_even_76 : ∀ k, 2 ∣ (ibox76 k).lo+(ibox76 k).hi := by decide +kernel
private theorem accepted_76 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox76) tree76 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox76 midpoint_even_76
  simp only [tree76,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox76,candidate_valid h (FixedTape.midBox ibox76),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox76 139 (FixedTape.rowsAux denominator ibox76 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox76) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_76
private noncomputable def tree75 : TapeTree := .centered (candidateRows ibox75) (candidateRows (FixedTape.midBox ibox75))
attribute [irreducible] tree75
private theorem sign_75 : 2*denominator*(computed denominator (FixedTape.midBox ibox75)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox75).gradient k).lo.natAbs ((computed denominator ibox75).gradient k).hi.natAbs : Int)*((ibox75 k).hi-(ibox75 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox75
    (computed denominator ibox75) (computed denominator (FixedTape.midBox ibox75))
    (by decide +kernel)
private theorem midpoint_even_75 : ∀ k, 2 ∣ (ibox75 k).lo+(ibox75 k).hi := by decide +kernel
private theorem accepted_75 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox75) tree75 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox75 midpoint_even_75
  simp only [tree75,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox75,candidate_valid h (FixedTape.midBox ibox75),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox75 139 (FixedTape.rowsAux denominator ibox75 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox75) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_75
private noncomputable def tree74 : TapeTree := .split 2 (((141552812452790042251463523262917788928705659658049011565088294525197911285422983461686634086400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree75 tree76
attribute [irreducible] tree74
private theorem accepted_74 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox74) tree74 = true := by
  simp only [tree74,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox74 2 (141552812452790042251463523262917788928705659658049011565088294525197911285422983461686634086400000000000000000000000 : Int) false,decode_split denominator ibox74 2 (141552812452790042251463523262917788928705659658049011565088294525197911285422983461686634086400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_75 h,accepted_76 h⟩
private noncomputable def tree73 : TapeTree := .centered (candidateRows ibox73) (candidateRows (FixedTape.midBox ibox73))
attribute [irreducible] tree73
private theorem sign_73 : 2*denominator*(computed denominator (FixedTape.midBox ibox73)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox73).gradient k).lo.natAbs ((computed denominator ibox73).gradient k).hi.natAbs : Int)*((ibox73 k).hi-(ibox73 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox73
    (computed denominator ibox73) (computed denominator (FixedTape.midBox ibox73))
    (by decide +kernel)
private theorem midpoint_even_73 : ∀ k, 2 ∣ (ibox73 k).lo+(ibox73 k).hi := by decide +kernel
private theorem accepted_73 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox73) tree73 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox73 midpoint_even_73
  simp only [tree73,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox73,candidate_valid h (FixedTape.midBox ibox73),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox73 139 (FixedTape.rowsAux denominator ibox73 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox73) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_73
private noncomputable def tree72 : TapeTree := .centered (candidateRows ibox72) (candidateRows (FixedTape.midBox ibox72))
attribute [irreducible] tree72
private theorem sign_72 : 2*denominator*(computed denominator (FixedTape.midBox ibox72)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox72).gradient k).lo.natAbs ((computed denominator ibox72).gradient k).hi.natAbs : Int)*((ibox72 k).hi-(ibox72 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox72
    (computed denominator ibox72) (computed denominator (FixedTape.midBox ibox72))
    (by decide +kernel)
private theorem midpoint_even_72 : ∀ k, 2 ∣ (ibox72 k).lo+(ibox72 k).hi := by decide +kernel
private theorem accepted_72 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox72) tree72 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox72 midpoint_even_72
  simp only [tree72,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox72,candidate_valid h (FixedTape.midBox ibox72),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox72 139 (FixedTape.rowsAux denominator ibox72 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox72) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_72
private noncomputable def tree71 : TapeTree := .split 0 (((119033046835300717347821599107453595235502486530632123361551520396189152671832963365509215027200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree72 tree73
attribute [irreducible] tree71
private theorem accepted_71 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox71) tree71 = true := by
  simp only [tree71,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox71 0 (119033046835300717347821599107453595235502486530632123361551520396189152671832963365509215027200000000000000000000000 : Int) false,decode_split denominator ibox71 0 (119033046835300717347821599107453595235502486530632123361551520396189152671832963365509215027200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_72 h,accepted_73 h⟩
private noncomputable def tree70 : TapeTree := .split 2 (((128684374957081856592239566602652535389732417870953646877352995022907192077657257692442394624000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree71 tree74
attribute [irreducible] tree70
private theorem accepted_70 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox70) tree70 = true := by
  simp only [tree70,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox70 2 (128684374957081856592239566602652535389732417870953646877352995022907192077657257692442394624000000000000000000000000 : Int) false,decode_split denominator ibox70 2 (128684374957081856592239566602652535389732417870953646877352995022907192077657257692442394624000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_71 h,accepted_74 h⟩
private noncomputable def tree69 : TapeTree := .face 3 false (candidateRows ibox69) tree70
attribute [irreducible] tree69
private theorem sign_69 : ((computed denominator ibox69).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_69 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox69) tree69 = true := by
  simp only [tree69,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox69,?_,accepted_70 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox69)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox69).gradient 3).hi) denominator_positive).1 sign_69
private noncomputable def tree68 : TapeTree := .split 2 (((154421249948498227910687479923183042467678901445144376252823594027488630493188709230930873548800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree69 tree77
attribute [irreducible] tree68
private theorem accepted_68 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox68) tree68 = true := by
  simp only [tree68,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox68 2 (154421249948498227910687479923183042467678901445144376252823594027488630493188709230930873548800000000000000000000000 : Int) false,decode_split denominator ibox68 2 (154421249948498227910687479923183042467678901445144376252823594027488630493188709230930873548800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_69 h,accepted_77 h⟩
private noncomputable def tree67 : TapeTree := .split 3 (((102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree68 tree87
attribute [irreducible] tree67
private theorem accepted_67 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox67) tree67 = true := by
  simp only [tree67,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox67 3 (102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 : Int) false,decode_split denominator ibox67 3 (102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_68 h,accepted_87 h⟩
private noncomputable def tree66 : TapeTree := .centered (candidateRows ibox66) (candidateRows (FixedTape.midBox ibox66))
attribute [irreducible] tree66
private theorem sign_66 : 2*denominator*(computed denominator (FixedTape.midBox ibox66)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox66).gradient k).lo.natAbs ((computed denominator ibox66).gradient k).hi.natAbs : Int)*((ibox66 k).hi-(ibox66 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox66
    (computed denominator ibox66) (computed denominator (FixedTape.midBox ibox66))
    (by decide +kernel)
private theorem midpoint_even_66 : ∀ k, 2 ∣ (ibox66 k).lo+(ibox66 k).hi := by decide +kernel
private theorem accepted_66 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox66) tree66 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox66 midpoint_even_66
  simp only [tree66,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox66,candidate_valid h (FixedTape.midBox ibox66),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox66 139 (FixedTape.rowsAux denominator ibox66 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox66) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_66
private noncomputable def tree65 : TapeTree := .centered (candidateRows ibox65) (candidateRows (FixedTape.midBox ibox65))
attribute [irreducible] tree65
private theorem sign_65 : 2*denominator*(computed denominator (FixedTape.midBox ibox65)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox65).gradient k).lo.natAbs ((computed denominator ibox65).gradient k).hi.natAbs : Int)*((ibox65 k).hi-(ibox65 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox65
    (computed denominator ibox65) (computed denominator (FixedTape.midBox ibox65))
    (by decide +kernel)
private theorem midpoint_even_65 : ∀ k, 2 ∣ (ibox65 k).lo+(ibox65 k).hi := by decide +kernel
private theorem accepted_65 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox65) tree65 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox65 midpoint_even_65
  simp only [tree65,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox65,candidate_valid h (FixedTape.midBox ibox65),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox65 139 (FixedTape.rowsAux denominator ibox65 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox65) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_65
private noncomputable def tree64 : TapeTree := .split 0 (((119033046835300717347821599107453595235502486530632123361551520396189152671832963365509215027200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree65 tree66
attribute [irreducible] tree64
private theorem accepted_64 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox64) tree64 = true := by
  simp only [tree64,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox64 0 (119033046835300717347821599107453595235502486530632123361551520396189152671832963365509215027200000000000000000000000 : Int) false,decode_split denominator ibox64 0 (119033046835300717347821599107453595235502486530632123361551520396189152671832963365509215027200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_65 h,accepted_66 h⟩
private noncomputable def tree63 : TapeTree := .centered (candidateRows ibox63) (candidateRows (FixedTape.midBox ibox63))
attribute [irreducible] tree63
private theorem sign_63 : 2*denominator*(computed denominator (FixedTape.midBox ibox63)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox63).gradient k).lo.natAbs ((computed denominator ibox63).gradient k).hi.natAbs : Int)*((ibox63 k).hi-(ibox63 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox63
    (computed denominator ibox63) (computed denominator (FixedTape.midBox ibox63))
    (by decide +kernel)
private theorem midpoint_even_63 : ∀ k, 2 ∣ (ibox63 k).lo+(ibox63 k).hi := by decide +kernel
private theorem accepted_63 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox63) tree63 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox63 midpoint_even_63
  simp only [tree63,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox63,candidate_valid h (FixedTape.midBox ibox63),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox63 139 (FixedTape.rowsAux denominator ibox63 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox63) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_63
private noncomputable def tree62 : TapeTree := .centered (candidateRows ibox62) (candidateRows (FixedTape.midBox ibox62))
attribute [irreducible] tree62
private theorem sign_62 : 2*denominator*(computed denominator (FixedTape.midBox ibox62)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox62).gradient k).lo.natAbs ((computed denominator ibox62).gradient k).hi.natAbs : Int)*((ibox62 k).hi-(ibox62 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox62
    (computed denominator ibox62) (computed denominator (FixedTape.midBox ibox62))
    (by decide +kernel)
private theorem midpoint_even_62 : ∀ k, 2 ∣ (ibox62 k).lo+(ibox62 k).hi := by decide +kernel
private theorem accepted_62 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox62) tree62 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox62 midpoint_even_62
  simp only [tree62,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox62,candidate_valid h (FixedTape.midBox ibox62),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox62 139 (FixedTape.rowsAux denominator ibox62 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox62) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_62
private noncomputable def tree61 : TapeTree := .split 2 (((64342187478540928296119783301326267694866208935476823438676497511453596038828628846221197312000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree62 tree63
attribute [irreducible] tree61
private theorem accepted_61 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox61) tree61 = true := by
  simp only [tree61,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox61 2 (64342187478540928296119783301326267694866208935476823438676497511453596038828628846221197312000000000000000000000000 : Int) false,decode_split denominator ibox61 2 (64342187478540928296119783301326267694866208935476823438676497511453596038828628846221197312000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_62 h,accepted_63 h⟩
private noncomputable def tree60 : TapeTree := .centered (candidateRows ibox60) (candidateRows (FixedTape.midBox ibox60))
attribute [irreducible] tree60
private theorem sign_60 : 2*denominator*(computed denominator (FixedTape.midBox ibox60)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox60).gradient k).lo.natAbs ((computed denominator ibox60).gradient k).hi.natAbs : Int)*((ibox60 k).hi-(ibox60 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox60
    (computed denominator ibox60) (computed denominator (FixedTape.midBox ibox60))
    (by decide +kernel)
private theorem midpoint_even_60 : ∀ k, 2 ∣ (ibox60 k).lo+(ibox60 k).hi := by decide +kernel
private theorem accepted_60 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox60) tree60 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox60 midpoint_even_60
  simp only [tree60,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox60,candidate_valid h (FixedTape.midBox ibox60),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox60 139 (FixedTape.rowsAux denominator ibox60 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox60) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_60
private noncomputable def tree59 : TapeTree := .centered (candidateRows ibox59) (candidateRows (FixedTape.midBox ibox59))
attribute [irreducible] tree59
private theorem sign_59 : 2*denominator*(computed denominator (FixedTape.midBox ibox59)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox59).gradient k).lo.natAbs ((computed denominator ibox59).gradient k).hi.natAbs : Int)*((ibox59 k).hi-(ibox59 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox59
    (computed denominator ibox59) (computed denominator (FixedTape.midBox ibox59))
    (by decide +kernel)
private theorem midpoint_even_59 : ∀ k, 2 ∣ (ibox59 k).lo+(ibox59 k).hi := by decide +kernel
private theorem accepted_59 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox59) tree59 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox59 midpoint_even_59
  simp only [tree59,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox59,candidate_valid h (FixedTape.midBox ibox59),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox59 139 (FixedTape.rowsAux denominator ibox59 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox59) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_59
private noncomputable def tree58 : TapeTree := .split 2 (((64342187478540928296119783301326267694866208935476823438676497511453596038828628846221197312000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree59 tree60
attribute [irreducible] tree58
private theorem accepted_58 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox58) tree58 = true := by
  simp only [tree58,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox58 2 (64342187478540928296119783301326267694866208935476823438676497511453596038828628846221197312000000000000000000000000 : Int) false,decode_split denominator ibox58 2 (64342187478540928296119783301326267694866208935476823438676497511453596038828628846221197312000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_59 h,accepted_60 h⟩
private noncomputable def tree57 : TapeTree := .split 0 (((119033046835300717347821599107453595235502486530632123361551520396189152671832963365509215027200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree58 tree61
attribute [irreducible] tree57
private theorem accepted_57 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox57) tree57 = true := by
  simp only [tree57,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox57 0 (119033046835300717347821599107453595235502486530632123361551520396189152671832963365509215027200000000000000000000000 : Int) false,decode_split denominator ibox57 0 (119033046835300717347821599107453595235502486530632123361551520396189152671832963365509215027200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_58 h,accepted_61 h⟩
private noncomputable def tree56 : TapeTree := .split 2 (((77210624974249113955343739961591521233839450722572188126411797013744315246594354615465436774400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree57 tree64
attribute [irreducible] tree56
private theorem accepted_56 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox56) tree56 = true := by
  simp only [tree56,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox56 2 (77210624974249113955343739961591521233839450722572188126411797013744315246594354615465436774400000000000000000000000 : Int) false,decode_split denominator ibox56 2 (77210624974249113955343739961591521233839450722572188126411797013744315246594354615465436774400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_57 h,accepted_64 h⟩
private noncomputable def tree55 : TapeTree := .centered (candidateRows ibox55) (candidateRows (FixedTape.midBox ibox55))
attribute [irreducible] tree55
private theorem sign_55 : 2*denominator*(computed denominator (FixedTape.midBox ibox55)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox55).gradient k).lo.natAbs ((computed denominator ibox55).gradient k).hi.natAbs : Int)*((ibox55 k).hi-(ibox55 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox55
    (computed denominator ibox55) (computed denominator (FixedTape.midBox ibox55))
    (by decide +kernel)
private theorem midpoint_even_55 : ∀ k, 2 ∣ (ibox55 k).lo+(ibox55 k).hi := by decide +kernel
private theorem accepted_55 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox55) tree55 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox55 midpoint_even_55
  simp only [tree55,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox55,candidate_valid h (FixedTape.midBox ibox55),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox55 139 (FixedTape.rowsAux denominator ibox55 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox55) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_55
private noncomputable def tree54 : TapeTree := .centered (candidateRows ibox54) (candidateRows (FixedTape.midBox ibox54))
attribute [irreducible] tree54
private theorem sign_54 : 2*denominator*(computed denominator (FixedTape.midBox ibox54)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox54).gradient k).lo.natAbs ((computed denominator ibox54).gradient k).hi.natAbs : Int)*((ibox54 k).hi-(ibox54 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox54
    (computed denominator ibox54) (computed denominator (FixedTape.midBox ibox54))
    (by decide +kernel)
private theorem midpoint_even_54 : ∀ k, 2 ∣ (ibox54 k).lo+(ibox54 k).hi := by decide +kernel
private theorem accepted_54 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox54) tree54 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox54 midpoint_even_54
  simp only [tree54,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox54,candidate_valid h (FixedTape.midBox ibox54),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox54 139 (FixedTape.rowsAux denominator ibox54 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox54) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_54
private noncomputable def tree53 : TapeTree := .split 2 (((38605312487124556977671869980795760616919725361286094063205898506872157623297177307732718387200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree54 tree55
attribute [irreducible] tree53
private theorem accepted_53 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox53) tree53 = true := by
  simp only [tree53,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox53 2 (38605312487124556977671869980795760616919725361286094063205898506872157623297177307732718387200000000000000000000000 : Int) false,decode_split denominator ibox53 2 (38605312487124556977671869980795760616919725361286094063205898506872157623297177307732718387200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_54 h,accepted_55 h⟩
private noncomputable def tree52 : TapeTree := .centered (candidateRows ibox52) (candidateRows (FixedTape.midBox ibox52))
attribute [irreducible] tree52
private theorem sign_52 : 2*denominator*(computed denominator (FixedTape.midBox ibox52)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox52).gradient k).lo.natAbs ((computed denominator ibox52).gradient k).hi.natAbs : Int)*((ibox52 k).hi-(ibox52 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox52
    (computed denominator ibox52) (computed denominator (FixedTape.midBox ibox52))
    (by decide +kernel)
private theorem midpoint_even_52 : ∀ k, 2 ∣ (ibox52 k).lo+(ibox52 k).hi := by decide +kernel
private theorem accepted_52 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox52) tree52 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox52 midpoint_even_52
  simp only [tree52,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox52,candidate_valid h (FixedTape.midBox ibox52),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox52 139 (FixedTape.rowsAux denominator ibox52 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox52) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_52
private noncomputable def tree51 : TapeTree := .centered (candidateRows ibox51) (candidateRows (FixedTape.midBox ibox51))
attribute [irreducible] tree51
private theorem sign_51 : 2*denominator*(computed denominator (FixedTape.midBox ibox51)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox51).gradient k).lo.natAbs ((computed denominator ibox51).gradient k).hi.natAbs : Int)*((ibox51 k).hi-(ibox51 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox51
    (computed denominator ibox51) (computed denominator (FixedTape.midBox ibox51))
    (by decide +kernel)
private theorem midpoint_even_51 : ∀ k, 2 ∣ (ibox51 k).lo+(ibox51 k).hi := by decide +kernel
private theorem accepted_51 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox51) tree51 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox51 midpoint_even_51
  simp only [tree51,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox51,candidate_valid h (FixedTape.midBox ibox51),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox51 139 (FixedTape.rowsAux denominator ibox51 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox51) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_51
private noncomputable def tree50 : TapeTree := .split 2 (((38605312487124556977671869980795760616919725361286094063205898506872157623297177307732718387200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree51 tree52
attribute [irreducible] tree50
private theorem accepted_50 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox50) tree50 = true := by
  simp only [tree50,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox50 2 (38605312487124556977671869980795760616919725361286094063205898506872157623297177307732718387200000000000000000000000 : Int) false,decode_split denominator ibox50 2 (38605312487124556977671869980795760616919725361286094063205898506872157623297177307732718387200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_51 h,accepted_52 h⟩
private noncomputable def tree49 : TapeTree := .split 1 (((102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree50 tree53
attribute [irreducible] tree49
private theorem accepted_49 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox49) tree49 = true := by
  simp only [tree49,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox49 1 (102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 : Int) false,decode_split denominator ibox49 1 (102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_50 h,accepted_53 h⟩
private noncomputable def tree48 : TapeTree := .centered (candidateRows ibox48) (candidateRows (FixedTape.midBox ibox48))
attribute [irreducible] tree48
private theorem sign_48 : 2*denominator*(computed denominator (FixedTape.midBox ibox48)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox48).gradient k).lo.natAbs ((computed denominator ibox48).gradient k).hi.natAbs : Int)*((ibox48 k).hi-(ibox48 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox48
    (computed denominator ibox48) (computed denominator (FixedTape.midBox ibox48))
    (by decide +kernel)
private theorem midpoint_even_48 : ∀ k, 2 ∣ (ibox48 k).lo+(ibox48 k).hi := by decide +kernel
private theorem accepted_48 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox48) tree48 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox48 midpoint_even_48
  simp only [tree48,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox48,candidate_valid h (FixedTape.midBox ibox48),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox48 139 (FixedTape.rowsAux denominator ibox48 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox48) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_48
private noncomputable def tree47 : TapeTree := .centered (candidateRows ibox47) (candidateRows (FixedTape.midBox ibox47))
attribute [irreducible] tree47
private theorem sign_47 : 2*denominator*(computed denominator (FixedTape.midBox ibox47)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox47).gradient k).lo.natAbs ((computed denominator ibox47).gradient k).hi.natAbs : Int)*((ibox47 k).hi-(ibox47 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox47
    (computed denominator ibox47) (computed denominator (FixedTape.midBox ibox47))
    (by decide +kernel)
private theorem midpoint_even_47 : ∀ k, 2 ∣ (ibox47 k).lo+(ibox47 k).hi := by decide +kernel
private theorem accepted_47 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox47) tree47 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox47 midpoint_even_47
  simp only [tree47,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox47,candidate_valid h (FixedTape.midBox ibox47),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox47 139 (FixedTape.rowsAux denominator ibox47 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox47) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_47
private noncomputable def tree46 : TapeTree := .split 1 (((102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree47 tree48
attribute [irreducible] tree46
private theorem accepted_46 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox46) tree46 = true := by
  simp only [tree46,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox46 1 (102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 : Int) false,decode_split denominator ibox46 1 (102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_47 h,accepted_48 h⟩
private noncomputable def tree45 : TapeTree := .face 2 false (candidateRows ibox45) tree46
attribute [irreducible] tree45
private theorem sign_45 : ((computed denominator ibox45).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_45 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox45) tree45 = true := by
  simp only [tree45,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox45,?_,accepted_46 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox45)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox45).gradient 2).hi) denominator_positive).1 sign_45
private noncomputable def tree44 : TapeTree := .centered (candidateRows ibox44) (candidateRows (FixedTape.midBox ibox44))
attribute [irreducible] tree44
private theorem sign_44 : 2*denominator*(computed denominator (FixedTape.midBox ibox44)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox44).gradient k).lo.natAbs ((computed denominator ibox44).gradient k).hi.natAbs : Int)*((ibox44 k).hi-(ibox44 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox44
    (computed denominator ibox44) (computed denominator (FixedTape.midBox ibox44))
    (by decide +kernel)
private theorem midpoint_even_44 : ∀ k, 2 ∣ (ibox44 k).lo+(ibox44 k).hi := by decide +kernel
private theorem accepted_44 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox44) tree44 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox44 midpoint_even_44
  simp only [tree44,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox44,candidate_valid h (FixedTape.midBox ibox44),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox44 139 (FixedTape.rowsAux denominator ibox44 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox44) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_44
private noncomputable def tree43 : TapeTree := .centered (candidateRows ibox43) (candidateRows (FixedTape.midBox ibox43))
attribute [irreducible] tree43
private theorem sign_43 : 2*denominator*(computed denominator (FixedTape.midBox ibox43)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox43).gradient k).lo.natAbs ((computed denominator ibox43).gradient k).hi.natAbs : Int)*((ibox43 k).hi-(ibox43 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox43
    (computed denominator ibox43) (computed denominator (FixedTape.midBox ibox43))
    (by decide +kernel)
private theorem midpoint_even_43 : ∀ k, 2 ∣ (ibox43 k).lo+(ibox43 k).hi := by decide +kernel
private theorem accepted_43 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox43) tree43 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox43 midpoint_even_43
  simp only [tree43,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox43,candidate_valid h (FixedTape.midBox ibox43),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox43 139 (FixedTape.rowsAux denominator ibox43 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox43) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_43
private noncomputable def tree42 : TapeTree := .split 1 (((102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree43 tree44
attribute [irreducible] tree42
private theorem accepted_42 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox42) tree42 = true := by
  simp only [tree42,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox42 1 (102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 : Int) false,decode_split denominator ibox42 1 (102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_43 h,accepted_44 h⟩
private noncomputable def tree41 : TapeTree := .split 2 (((38605312487124556977671869980795760616919725361286094063205898506872157623297177307732718387200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree42 tree45
attribute [irreducible] tree41
private theorem accepted_41 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox41) tree41 = true := by
  simp only [tree41,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox41 2 (38605312487124556977671869980795760616919725361286094063205898506872157623297177307732718387200000000000000000000000 : Int) false,decode_split denominator ibox41 2 (38605312487124556977671869980795760616919725361286094063205898506872157623297177307732718387200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_42 h,accepted_45 h⟩
private noncomputable def tree40 : TapeTree := .split 0 (((119033046835300717347821599107453595235502486530632123361551520396189152671832963365509215027200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree41 tree49
attribute [irreducible] tree40
private theorem accepted_40 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox40) tree40 = true := by
  simp only [tree40,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox40 0 (119033046835300717347821599107453595235502486530632123361551520396189152671832963365509215027200000000000000000000000 : Int) false,decode_split denominator ibox40 0 (119033046835300717347821599107453595235502486530632123361551520396189152671832963365509215027200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_41 h,accepted_49 h⟩
private noncomputable def tree39 : TapeTree := .centered (candidateRows ibox39) (candidateRows (FixedTape.midBox ibox39))
attribute [irreducible] tree39
private theorem sign_39 : 2*denominator*(computed denominator (FixedTape.midBox ibox39)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox39).gradient k).lo.natAbs ((computed denominator ibox39).gradient k).hi.natAbs : Int)*((ibox39 k).hi-(ibox39 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox39
    (computed denominator ibox39) (computed denominator (FixedTape.midBox ibox39))
    (by decide +kernel)
private theorem midpoint_even_39 : ∀ k, 2 ∣ (ibox39 k).lo+(ibox39 k).hi := by decide +kernel
private theorem accepted_39 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox39) tree39 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox39 midpoint_even_39
  simp only [tree39,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox39,candidate_valid h (FixedTape.midBox ibox39),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox39 139 (FixedTape.rowsAux denominator ibox39 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox39) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_39
private noncomputable def tree38 : TapeTree := .centered (candidateRows ibox38) (candidateRows (FixedTape.midBox ibox38))
attribute [irreducible] tree38
private theorem sign_38 : 2*denominator*(computed denominator (FixedTape.midBox ibox38)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox38).gradient k).lo.natAbs ((computed denominator ibox38).gradient k).hi.natAbs : Int)*((ibox38 k).hi-(ibox38 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox38
    (computed denominator ibox38) (computed denominator (FixedTape.midBox ibox38))
    (by decide +kernel)
private theorem midpoint_even_38 : ∀ k, 2 ∣ (ibox38 k).lo+(ibox38 k).hi := by decide +kernel
private theorem accepted_38 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox38) tree38 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox38 midpoint_even_38
  simp only [tree38,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox38,candidate_valid h (FixedTape.midBox ibox38),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox38 139 (FixedTape.rowsAux denominator ibox38 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox38) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_38
private noncomputable def tree37 : TapeTree := .split 1 (((154421249948498227910687479923183042467678901445144376252823594027488630493188709230930873548800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree38 tree39
attribute [irreducible] tree37
private theorem accepted_37 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox37) tree37 = true := by
  simp only [tree37,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox37 1 (154421249948498227910687479923183042467678901445144376252823594027488630493188709230930873548800000000000000000000000 : Int) false,decode_split denominator ibox37 1 (154421249948498227910687479923183042467678901445144376252823594027488630493188709230930873548800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_38 h,accepted_39 h⟩
private noncomputable def tree36 : TapeTree := .centered (candidateRows ibox36) (candidateRows (FixedTape.midBox ibox36))
attribute [irreducible] tree36
private theorem sign_36 : 2*denominator*(computed denominator (FixedTape.midBox ibox36)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox36).gradient k).lo.natAbs ((computed denominator ibox36).gradient k).hi.natAbs : Int)*((ibox36 k).hi-(ibox36 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox36
    (computed denominator ibox36) (computed denominator (FixedTape.midBox ibox36))
    (by decide +kernel)
private theorem midpoint_even_36 : ∀ k, 2 ∣ (ibox36 k).lo+(ibox36 k).hi := by decide +kernel
private theorem accepted_36 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox36) tree36 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox36 midpoint_even_36
  simp only [tree36,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox36,candidate_valid h (FixedTape.midBox ibox36),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox36 139 (FixedTape.rowsAux denominator ibox36 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox36) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_36
private noncomputable def tree35 : TapeTree := .centered (candidateRows ibox35) (candidateRows (FixedTape.midBox ibox35))
attribute [irreducible] tree35
private theorem sign_35 : 2*denominator*(computed denominator (FixedTape.midBox ibox35)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox35).gradient k).lo.natAbs ((computed denominator ibox35).gradient k).hi.natAbs : Int)*((ibox35 k).hi-(ibox35 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox35
    (computed denominator ibox35) (computed denominator (FixedTape.midBox ibox35))
    (by decide +kernel)
private theorem midpoint_even_35 : ∀ k, 2 ∣ (ibox35 k).lo+(ibox35 k).hi := by decide +kernel
private theorem accepted_35 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox35) tree35 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox35 midpoint_even_35
  simp only [tree35,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox35,candidate_valid h (FixedTape.midBox ibox35),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox35 139 (FixedTape.rowsAux denominator ibox35 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox35) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_35
private noncomputable def tree34 : TapeTree := .face 2 false (candidateRows ibox34) tree35
attribute [irreducible] tree34
private theorem sign_34 : ((computed denominator ibox34).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_34 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox34) tree34 = true := by
  simp only [tree34,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox34,?_,accepted_35 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox34)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox34).gradient 2).hi) denominator_positive).1 sign_34
private noncomputable def tree33 : TapeTree := .split 2 (((6434218747854092829611978330132626769486620893547682343867649751145359603882862884622119731200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree34 tree36
attribute [irreducible] tree33
private theorem accepted_33 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox33) tree33 = true := by
  simp only [tree33,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox33 2 (6434218747854092829611978330132626769486620893547682343867649751145359603882862884622119731200000000000000000000000 : Int) false,decode_split denominator ibox33 2 (6434218747854092829611978330132626769486620893547682343867649751145359603882862884622119731200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_34 h,accepted_36 h⟩
private noncomputable def tree32 : TapeTree := .centered (candidateRows ibox32) (candidateRows (FixedTape.midBox ibox32))
attribute [irreducible] tree32
private theorem sign_32 : 2*denominator*(computed denominator (FixedTape.midBox ibox32)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox32).gradient k).lo.natAbs ((computed denominator ibox32).gradient k).hi.natAbs : Int)*((ibox32 k).hi-(ibox32 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox32
    (computed denominator ibox32) (computed denominator (FixedTape.midBox ibox32))
    (by decide +kernel)
private theorem midpoint_even_32 : ∀ k, 2 ∣ (ibox32 k).lo+(ibox32 k).hi := by decide +kernel
private theorem accepted_32 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox32) tree32 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox32 midpoint_even_32
  simp only [tree32,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox32,candidate_valid h (FixedTape.midBox ibox32),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox32 139 (FixedTape.rowsAux denominator ibox32 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox32) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_32
private noncomputable def tree31 : TapeTree := .centered (candidateRows ibox31) (candidateRows (FixedTape.midBox ibox31))
attribute [irreducible] tree31
private theorem sign_31 : 2*denominator*(computed denominator (FixedTape.midBox ibox31)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox31).gradient k).lo.natAbs ((computed denominator ibox31).gradient k).hi.natAbs : Int)*((ibox31 k).hi-(ibox31 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox31
    (computed denominator ibox31) (computed denominator (FixedTape.midBox ibox31))
    (by decide +kernel)
private theorem midpoint_even_31 : ∀ k, 2 ∣ (ibox31 k).lo+(ibox31 k).hi := by decide +kernel
private theorem accepted_31 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox31) tree31 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox31 midpoint_even_31
  simp only [tree31,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox31,candidate_valid h (FixedTape.midBox ibox31),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox31 139 (FixedTape.rowsAux denominator ibox31 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox31) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_31
private noncomputable def tree30 : TapeTree := .split 0 (((119569231730955231946789261679330332385736590413229651009269444326312432764316269827611302479853743596927713280000000 : Int) : ℚ)/(denominator : ℚ)) tree31 tree32
attribute [irreducible] tree30
private theorem accepted_30 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox30) tree30 = true := by
  simp only [tree30,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox30 0 (119569231730955231946789261679330332385736590413229651009269444326312432764316269827611302479853743596927713280000000 : Int) false,decode_split denominator ibox30 0 (119569231730955231946789261679330332385736590413229651009269444326312432764316269827611302479853743596927713280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_31 h,accepted_32 h⟩
private noncomputable def tree29 : TapeTree := .split 1 (((154421249948498227910687479923183042467678901445144376252823594027488630493188709230930873548800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree30 tree33
attribute [irreducible] tree29
private theorem accepted_29 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox29) tree29 = true := by
  simp only [tree29,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox29 1 (154421249948498227910687479923183042467678901445144376252823594027488630493188709230930873548800000000000000000000000 : Int) false,decode_split denominator ibox29 1 (154421249948498227910687479923183042467678901445144376252823594027488630493188709230930873548800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_30 h,accepted_33 h⟩
private noncomputable def tree28 : TapeTree := .split 2 (((12868437495708185659223956660265253538973241787095364687735299502290719207765725769244239462400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree29 tree37
attribute [irreducible] tree28
private theorem accepted_28 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox28) tree28 = true := by
  simp only [tree28,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox28 2 (12868437495708185659223956660265253538973241787095364687735299502290719207765725769244239462400000000000000000000000 : Int) false,decode_split denominator ibox28 2 (12868437495708185659223956660265253538973241787095364687735299502290719207765725769244239462400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_29 h,accepted_37 h⟩
private noncomputable def tree27 : TapeTree := .centered (candidateRows ibox27) (candidateRows (FixedTape.midBox ibox27))
attribute [irreducible] tree27
private theorem sign_27 : 2*denominator*(computed denominator (FixedTape.midBox ibox27)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox27).gradient k).lo.natAbs ((computed denominator ibox27).gradient k).hi.natAbs : Int)*((ibox27 k).hi-(ibox27 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox27
    (computed denominator ibox27) (computed denominator (FixedTape.midBox ibox27))
    (by decide +kernel)
private theorem midpoint_even_27 : ∀ k, 2 ∣ (ibox27 k).lo+(ibox27 k).hi := by decide +kernel
private theorem accepted_27 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox27) tree27 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox27 midpoint_even_27
  simp only [tree27,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox27,candidate_valid h (FixedTape.midBox ibox27),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox27 139 (FixedTape.rowsAux denominator ibox27 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox27) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_27
private noncomputable def tree26 : TapeTree := .centered (candidateRows ibox26) (candidateRows (FixedTape.midBox ibox26))
attribute [irreducible] tree26
private theorem sign_26 : 2*denominator*(computed denominator (FixedTape.midBox ibox26)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox26).gradient k).lo.natAbs ((computed denominator ibox26).gradient k).hi.natAbs : Int)*((ibox26 k).hi-(ibox26 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox26
    (computed denominator ibox26) (computed denominator (FixedTape.midBox ibox26))
    (by decide +kernel)
private theorem midpoint_even_26 : ∀ k, 2 ∣ (ibox26 k).lo+(ibox26 k).hi := by decide +kernel
private theorem accepted_26 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox26) tree26 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox26 midpoint_even_26
  simp only [tree26,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox26,candidate_valid h (FixedTape.midBox ibox26),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox26 139 (FixedTape.rowsAux denominator ibox26 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox26) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_26
private noncomputable def tree25 : TapeTree := .split 0 (((119569231730955231946789261679330332385736590413229651009269444326312432764316269827611302479853743596927713280000000 : Int) : ℚ)/(denominator : ℚ)) tree26 tree27
attribute [irreducible] tree25
private theorem accepted_25 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox25) tree25 = true := by
  simp only [tree25,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox25 0 (119569231730955231946789261679330332385736590413229651009269444326312432764316269827611302479853743596927713280000000 : Int) false,decode_split denominator ibox25 0 (119569231730955231946789261679330332385736590413229651009269444326312432764316269827611302479853743596927713280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_26 h,accepted_27 h⟩
private noncomputable def tree24 : TapeTree := .centered (candidateRows ibox24) (candidateRows (FixedTape.midBox ibox24))
attribute [irreducible] tree24
private theorem sign_24 : 2*denominator*(computed denominator (FixedTape.midBox ibox24)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox24).gradient k).lo.natAbs ((computed denominator ibox24).gradient k).hi.natAbs : Int)*((ibox24 k).hi-(ibox24 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox24
    (computed denominator ibox24) (computed denominator (FixedTape.midBox ibox24))
    (by decide +kernel)
private theorem midpoint_even_24 : ∀ k, 2 ∣ (ibox24 k).lo+(ibox24 k).hi := by decide +kernel
private theorem accepted_24 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox24) tree24 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox24 midpoint_even_24
  simp only [tree24,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox24,candidate_valid h (FixedTape.midBox ibox24),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox24 139 (FixedTape.rowsAux denominator ibox24 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox24) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_24
private noncomputable def tree23 : TapeTree := .centered (candidateRows ibox23) (candidateRows (FixedTape.midBox ibox23))
attribute [irreducible] tree23
private theorem sign_23 : 2*denominator*(computed denominator (FixedTape.midBox ibox23)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox23).gradient k).lo.natAbs ((computed denominator ibox23).gradient k).hi.natAbs : Int)*((ibox23 k).hi-(ibox23 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox23
    (computed denominator ibox23) (computed denominator (FixedTape.midBox ibox23))
    (by decide +kernel)
private theorem midpoint_even_23 : ∀ k, 2 ∣ (ibox23 k).lo+(ibox23 k).hi := by decide +kernel
private theorem accepted_23 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox23) tree23 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox23 midpoint_even_23
  simp only [tree23,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox23,candidate_valid h (FixedTape.midBox ibox23),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox23 139 (FixedTape.rowsAux denominator ibox23 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox23) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_23
private noncomputable def tree22 : TapeTree := .split 0 (((119569231730955231946789261679330332385736590413229651009269444326312432764316269827611302479853743596927713280000000 : Int) : ℚ)/(denominator : ℚ)) tree23 tree24
attribute [irreducible] tree22
private theorem accepted_22 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox22) tree22 = true := by
  simp only [tree22,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox22 0 (119569231730955231946789261679330332385736590413229651009269444326312432764316269827611302479853743596927713280000000 : Int) false,decode_split denominator ibox22 0 (119569231730955231946789261679330332385736590413229651009269444326312432764316269827611302479853743596927713280000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_23 h,accepted_24 h⟩
private noncomputable def tree21 : TapeTree := .split 2 (((12868437495708185659223956660265253538973241787095364687735299502290719207765725769244239462400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree22 tree25
attribute [irreducible] tree21
private theorem accepted_21 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox21) tree21 = true := by
  simp only [tree21,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox21 2 (12868437495708185659223956660265253538973241787095364687735299502290719207765725769244239462400000000000000000000000 : Int) false,decode_split denominator ibox21 2 (12868437495708185659223956660265253538973241787095364687735299502290719207765725769244239462400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_22 h,accepted_25 h⟩
private noncomputable def tree20 : TapeTree := .split 1 (((102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree21 tree28
attribute [irreducible] tree20
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox20 1 (102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 : Int) false,decode_split denominator ibox20 1 (102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_21 h,accepted_28 h⟩
private noncomputable def tree19 : TapeTree := .centered (candidateRows ibox19) (candidateRows (FixedTape.midBox ibox19))
attribute [irreducible] tree19
private theorem sign_19 : 2*denominator*(computed denominator (FixedTape.midBox ibox19)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox19).gradient k).lo.natAbs ((computed denominator ibox19).gradient k).hi.natAbs : Int)*((ibox19 k).hi-(ibox19 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox19
    (computed denominator ibox19) (computed denominator (FixedTape.midBox ibox19))
    (by decide +kernel)
private theorem midpoint_even_19 : ∀ k, 2 ∣ (ibox19 k).lo+(ibox19 k).hi := by decide +kernel
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox19 midpoint_even_19
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox19,candidate_valid h (FixedTape.midBox ibox19),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox19 139 (FixedTape.rowsAux denominator ibox19 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox19) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_19
private noncomputable def tree18 : TapeTree := .face 2 false (candidateRows ibox18) tree19
attribute [irreducible] tree18
private theorem sign_18 : ((computed denominator ibox18).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_18 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox18) tree18 = true := by
  simp only [tree18,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox18,?_,accepted_19 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox18)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox18).gradient 2).hi) denominator_positive).1 sign_18
private noncomputable def tree17 : TapeTree := .centered (candidateRows ibox17) (candidateRows (FixedTape.midBox ibox17))
attribute [irreducible] tree17
private theorem sign_17 : 2*denominator*(computed denominator (FixedTape.midBox ibox17)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox17).gradient k).lo.natAbs ((computed denominator ibox17).gradient k).hi.natAbs : Int)*((ibox17 k).hi-(ibox17 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox17
    (computed denominator ibox17) (computed denominator (FixedTape.midBox ibox17))
    (by decide +kernel)
private theorem midpoint_even_17 : ∀ k, 2 ∣ (ibox17 k).lo+(ibox17 k).hi := by decide +kernel
private theorem accepted_17 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox17) tree17 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox17 midpoint_even_17
  simp only [tree17,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox17,candidate_valid h (FixedTape.midBox ibox17),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox17 139 (FixedTape.rowsAux denominator ibox17 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox17) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_17
private noncomputable def tree16 : TapeTree := .centered (candidateRows ibox16) (candidateRows (FixedTape.midBox ibox16))
attribute [irreducible] tree16
private theorem sign_16 : 2*denominator*(computed denominator (FixedTape.midBox ibox16)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox16).gradient k).lo.natAbs ((computed denominator ibox16).gradient k).hi.natAbs : Int)*((ibox16 k).hi-(ibox16 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox16
    (computed denominator ibox16) (computed denominator (FixedTape.midBox ibox16))
    (by decide +kernel)
private theorem midpoint_even_16 : ∀ k, 2 ∣ (ibox16 k).lo+(ibox16 k).hi := by decide +kernel
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox16 midpoint_even_16
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox16,candidate_valid h (FixedTape.midBox ibox16),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox16 139 (FixedTape.rowsAux denominator ibox16 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox16) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_16
private noncomputable def tree15 : TapeTree := .split 1 (((102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree16 tree17
attribute [irreducible] tree15
private theorem accepted_15 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox15) tree15 = true := by
  simp only [tree15,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox15 1 (102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 : Int) false,decode_split denominator ibox15 1 (102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_16 h,accepted_17 h⟩
private noncomputable def tree14 : TapeTree := .face 2 false (candidateRows ibox14) tree15
attribute [irreducible] tree14
private theorem sign_14 : ((computed denominator ibox14).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_14 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox14) tree14 = true := by
  simp only [tree14,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox14,?_,accepted_15 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox14)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox14).gradient 2).hi) denominator_positive).1 sign_14
private noncomputable def tree13 : TapeTree := .split 2 (((12868437495708185659223956660265253538973241787095364687735299502290719207765725769244239462400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree14 tree18
attribute [irreducible] tree13
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox13 2 (12868437495708185659223956660265253538973241787095364687735299502290719207765725769244239462400000000000000000000000 : Int) false,decode_split denominator ibox13 2 (12868437495708185659223956660265253538973241787095364687735299502290719207765725769244239462400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_14 h,accepted_18 h⟩
private noncomputable def tree12 : TapeTree := .centered (candidateRows ibox12) (candidateRows (FixedTape.midBox ibox12))
attribute [irreducible] tree12
private theorem sign_12 : 2*denominator*(computed denominator (FixedTape.midBox ibox12)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox12).gradient k).lo.natAbs ((computed denominator ibox12).gradient k).hi.natAbs : Int)*((ibox12 k).hi-(ibox12 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox12
    (computed denominator ibox12) (computed denominator (FixedTape.midBox ibox12))
    (by decide +kernel)
private theorem midpoint_even_12 : ∀ k, 2 ∣ (ibox12 k).lo+(ibox12 k).hi := by decide +kernel
private theorem accepted_12 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox12) tree12 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox12 midpoint_even_12
  simp only [tree12,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox12,candidate_valid h (FixedTape.midBox ibox12),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox12 139 (FixedTape.rowsAux denominator ibox12 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox12) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_12
private noncomputable def tree11 : TapeTree := .face 2 false (candidateRows ibox11) tree12
attribute [irreducible] tree11
private theorem sign_11 : ((computed denominator ibox11).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox11,?_,accepted_12 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox11)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox11).gradient 2).hi) denominator_positive).1 sign_11
private noncomputable def tree10 : TapeTree := .centered (candidateRows ibox10) (candidateRows (FixedTape.midBox ibox10))
attribute [irreducible] tree10
private theorem sign_10 : 2*denominator*(computed denominator (FixedTape.midBox ibox10)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox10).gradient k).lo.natAbs ((computed denominator ibox10).gradient k).hi.natAbs : Int)*((ibox10 k).hi-(ibox10 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox10
    (computed denominator ibox10) (computed denominator (FixedTape.midBox ibox10))
    (by decide +kernel)
private theorem midpoint_even_10 : ∀ k, 2 ∣ (ibox10 k).lo+(ibox10 k).hi := by decide +kernel
private theorem accepted_10 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox10) tree10 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox10 midpoint_even_10
  simp only [tree10,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox10,candidate_valid h (FixedTape.midBox ibox10),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox10 139 (FixedTape.rowsAux denominator ibox10 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox10) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_10
private noncomputable def tree9 : TapeTree := .centered (candidateRows ibox9) (candidateRows (FixedTape.midBox ibox9))
attribute [irreducible] tree9
private theorem sign_9 : 2*denominator*(computed denominator (FixedTape.midBox ibox9)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox9).gradient k).lo.natAbs ((computed denominator ibox9).gradient k).hi.natAbs : Int)*((ibox9 k).hi-(ibox9 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox9
    (computed denominator ibox9) (computed denominator (FixedTape.midBox ibox9))
    (by decide +kernel)
private theorem midpoint_even_9 : ∀ k, 2 ∣ (ibox9 k).lo+(ibox9 k).hi := by decide +kernel
private theorem accepted_9 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox9) tree9 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox9 midpoint_even_9
  simp only [tree9,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox9,candidate_valid h (FixedTape.midBox ibox9),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox9 139 (FixedTape.rowsAux denominator ibox9 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox9) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_9
private noncomputable def tree8 : TapeTree := .split 1 (((102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree9 tree10
attribute [irreducible] tree8
private theorem accepted_8 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox8) tree8 = true := by
  simp only [tree8,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox8 1 (102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 : Int) false,decode_split denominator ibox8 1 (102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_9 h,accepted_10 h⟩
private noncomputable def tree7 : TapeTree := .face 2 false (candidateRows ibox7) tree8
attribute [irreducible] tree7
private theorem sign_7 : ((computed denominator ibox7).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_7 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox7) tree7 = true := by
  simp only [tree7,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox7,?_,accepted_8 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox7)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox7).gradient 2).hi) denominator_positive).1 sign_7
private noncomputable def tree6 : TapeTree := .split 2 (((12868437495708185659223956660265253538973241787095364687735299502290719207765725769244239462400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree7 tree11
attribute [irreducible] tree6
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox6 2 (12868437495708185659223956660265253538973241787095364687735299502290719207765725769244239462400000000000000000000000 : Int) false,decode_split denominator ibox6 2 (12868437495708185659223956660265253538973241787095364687735299502290719207765725769244239462400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_7 h,accepted_11 h⟩
private noncomputable def tree5 : TapeTree := .split 0 (((118496861939646202748853936535576858085268382648034595713833596466065872579349656903407127574546256403072286720000000 : Int) : ℚ)/(denominator : ℚ)) tree6 tree13
attribute [irreducible] tree5
private theorem accepted_5 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox5) tree5 = true := by
  simp only [tree5,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox5 0 (118496861939646202748853936535576858085268382648034595713833596466065872579349656903407127574546256403072286720000000 : Int) false,decode_split denominator ibox5 0 (118496861939646202748853936535576858085268382648034595713833596466065872579349656903407127574546256403072286720000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_6 h,accepted_13 h⟩
private noncomputable def tree4 : TapeTree := .split 0 (((119033046835300717347821599107453595235502486530632123361551520396189152671832963365509215027200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree5 tree20
attribute [irreducible] tree4
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox4 0 (119033046835300717347821599107453595235502486530632123361551520396189152671832963365509215027200000000000000000000000 : Int) false,decode_split denominator ibox4 0 (119033046835300717347821599107453595235502486530632123361551520396189152671832963365509215027200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_5 h,accepted_20 h⟩
private noncomputable def tree3 : TapeTree := .split 2 (((25736874991416371318447913320530507077946483574190729375470599004581438415531451538488478924800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree40
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 2 (25736874991416371318447913320530507077946483574190729375470599004581438415531451538488478924800000000000000000000000 : Int) false,decode_split denominator ibox3 2 (25736874991416371318447913320530507077946483574190729375470599004581438415531451538488478924800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_40 h⟩
private noncomputable def tree2 : TapeTree := .split 2 (((51473749982832742636895826641061014155892967148381458750941198009162876831062903076976957849600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree56
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 2 (51473749982832742636895826641061014155892967148381458750941198009162876831062903076976957849600000000000000000000000 : Int) false,decode_split denominator ibox2 2 (51473749982832742636895826641061014155892967148381458750941198009162876831062903076976957849600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_3 h,accepted_56 h⟩
private noncomputable def tree1 : TapeTree := .face 3 false (candidateRows ibox1) tree2
attribute [irreducible] tree1
private theorem sign_1 : ((computed denominator ibox1).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_1 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox1) tree1 = true := by
  simp only [tree1,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox1,?_,accepted_2 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox1)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox1).gradient 3).hi) denominator_positive).1 sign_1
private noncomputable def tree0 : TapeTree := .split 2 (((102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree1 tree67
attribute [irreducible] tree0
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox0 2 (102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 : Int) false,decode_split denominator ibox0 2 (102947499965665485273791653282122028311785934296762917501882396018325753662125806153953915699200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_1 h,accepted_67 h⟩
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (2864583333333333/5000000000000000 : ℚ) (2916666666666667/5000000000000000 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 139 = e144 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (2864583333333333/5000000000000000 : ℚ) (2916666666666667/5000000000000000 : ℚ)) x → eval e144 x ≤ 0 := by
  have hb := h.child_4 tape 139 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell80_high_internal_top

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell80_high_internal_top
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((2864583333333333/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((2916666666666667/5000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 80 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 80 p)
    (hkb : ((2916666666666667/5000000000000000 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((2864583333333333/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r)
    (hcase : bStar < a), internalResidual (0 : Fin 9) a p A r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell80_high_internal_top.cell_bound h.child_8 h.child_9 (Cell80_high_internal_top.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell80_high_internal_top
