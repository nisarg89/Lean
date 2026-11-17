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
namespace Cell82_high_internal_top
private noncomputable def qValues : Fin 4 → ℚ := ![(488818812087987275148974075716309201/765009503352876130741088263783650690 : ℚ),(120476634322514743483000000000000000/76500950335287613074108826378365069 : ℚ),(7122990648613693814028653621313407827/2447993446348686974108042905340132934 : ℚ),(-2465919159250615945862500000000000000/1223996723174343487054021452670066467 : ℚ)]
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
    priceLambda 82 p = ((488818812087987275148974075716309201/765009503352876130741088263783650690 : ℝ)+(120476634322514743483000000000000000/76500950335287613074108826378365069 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell82,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 82 p = (((7122990648613693814028653621313407827/2447993446348686974108042905340132934 : ℝ)+(-2465919159250615945862500000000000000/1223996723174343487054021452670066467 : ℝ)*p)-(145513/100000 : ℝ)*(1/1 : ℝ))/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell82,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e144 x = (x 0*(1-x 0))*(aPoint x+priceLambda 82 (x 0)*(HStar (yPoint x)-HStar (aPoint x)-HStar (capPoint x))+priceTau 82 (x 0)*psiStar (rPoint x)+(cStar-aPoint x-eta (0 : Fin 9)*psiStar (aPoint x))-(cStar-capPoint x-eta (0 : Fin 9)*psiStar (capPoint x))) := by
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
    (hL : lambdaStar (x 0) = priceLambda 82 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 82 (x 0)) :
    (1)*eval e144 x = (x 0*(1-x 0))*(internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_neg (not_le.mpr ha),if_neg (not_le.mpr hA),hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (19/32 : ℚ) (3020833333333333/5000000000000000 : ℚ)) x → eval e144 x ≤ 0)
    (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((19/32 : ℚ) : ℝ) < p ∧ p ≤ ((3020833333333333/5000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 82 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 82 p)
    (hkb : ((3020833333333333/5000000000000000 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((19/32 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r)
    (hcase : bStar < a) :
    internalResidual (0 : Fin 9) a p A r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxA,hxr⟩ := h7 (19/32 : ℚ) (3020833333333333/5000000000000000 : ℚ) bStar p a A r hpcell hkb hr.2 hap hcase hpA hAr
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,capPoint] using hxa
  have hAx : capPoint x = A := by simpa only [aPoint,rPoint,capPoint] using hxA
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,capPoint] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 82 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 82 (x 0) := by simpa only [hxp] using hT
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
.const (488818812087987275148974075716309201/765009503352876130741088263783650690 : ℚ),
.const (120476634322514743483000000000000000/76500950335287613074108826378365069 : ℚ),
.mul 108 1,
.add 107 109,
.const (7122990648613693814028653621313407827/2447993446348686974108042905340132934 : ℚ),
.const (-2465919159250615945862500000000000000/1223996723174343487054021452670066467 : ℚ),
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
private noncomputable def ssaQVals : Fin 18 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(-2840189/5000000 : ℚ),(113609/200000 : ℚ),(1085/4818 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ),(4818/3733 : ℚ),(145513/100000 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(488818812087987275148974075716309201/765009503352876130741088263783650690 : ℚ),(120476634322514743483000000000000000/76500950335287613074108826378365069 : ℚ),(7122990648613693814028653621313407827/2447993446348686974108042905340132934 : ℚ),(-2465919159250615945862500000000000000/1223996723174343487054021452670066467 : ℚ),(-145513/100000 : ℚ)]
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
private noncomputable def denominator : Int := 384276602612854841892722974909122831489305020349604942755943747846436993562603373652791105945600000000000000000000000
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
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨228164232801382562373804266352291681196774855832577934761341600283821964927795753106344719155200000000000000000000000,232167114078599774691746623150605584509923455853030886961381324350226166547823015152761722335241756480592936960000000⟩,⟨0,384276602612854841892722974909122831489305020349604942755943747846436993562603373652791105945600000000000000000000000⟩,⟨0,384276602612854841892722974909122831489305020349604942755943747846436993562603373652791105945600000000000000000000000⟩,⟨0,384276602612854841892722974909122831489305020349604942755943747846436993562603373652791105945600000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := splitI ibox0 2 192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 false
private noncomputable def ibox2 : Fin 4 → FixedTape.I := faceI ibox1 3 false
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 2 96069150653213710473180743727280707872326255087401235688985936961609248390650843413197776486400000000000000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 2 48034575326606855236590371863640353936163127543700617844492968480804624195325421706598888243200000000000000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox4 1 192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 false
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox5 0 230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 false
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox6 1 96069150653213710473180743727280707872326255087401235688985936961609248390650843413197776486400000000000000000000000 false
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox6 1 96069150653213710473180743727280707872326255087401235688985936961609248390650843413197776486400000000000000000000000 true
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox5 0 230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 true
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox9 1 96069150653213710473180743727280707872326255087401235688985936961609248390650843413197776486400000000000000000000000 false
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox9 1 96069150653213710473180743727280707872326255087401235688985936961609248390650843413197776486400000000000000000000000 true
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox4 1 192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 true
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox12 0 230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 false
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox13 2 24017287663303427618295185931820176968081563771850308922246484240402312097662710853299444121600000000000000000000000 false
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox14 1 288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 false
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox14 1 288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 true
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox16 1 336242027286247986656132603045482477553141892805904324911450779365632369367277951946192217702400000000000000000000000 false
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox16 1 336242027286247986656132603045482477553141892805904324911450779365632369367277951946192217702400000000000000000000000 true
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox13 2 24017287663303427618295185931820176968081563771850308922246484240402312097662710853299444121600000000000000000000000 true
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox19 1 288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 false
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox19 1 288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 true
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox12 0 230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 true
private noncomputable def ibox23 : Fin 4 → FixedTape.I := splitI ibox22 1 288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 false
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox23 2 24017287663303427618295185931820176968081563771850308922246484240402312097662710853299444121600000000000000000000000 false
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox23 2 24017287663303427618295185931820176968081563771850308922246484240402312097662710853299444121600000000000000000000000 true
private noncomputable def ibox26 : Fin 4 → FixedTape.I := splitI ibox22 1 288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 true
private noncomputable def ibox27 : Fin 4 → FixedTape.I := splitI ibox26 2 24017287663303427618295185931820176968081563771850308922246484240402312097662710853299444121600000000000000000000000 false
private noncomputable def ibox28 : Fin 4 → FixedTape.I := splitI ibox27 1 336242027286247986656132603045482477553141892805904324911450779365632369367277951946192217702400000000000000000000000 false
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox27 1 336242027286247986656132603045482477553141892805904324911450779365632369367277951946192217702400000000000000000000000 true
private noncomputable def ibox30 : Fin 4 → FixedTape.I := splitI ibox26 2 24017287663303427618295185931820176968081563771850308922246484240402312097662710853299444121600000000000000000000000 true
private noncomputable def ibox31 : Fin 4 → FixedTape.I := splitI ibox3 2 48034575326606855236590371863640353936163127543700617844492968480804624195325421706598888243200000000000000000000000 true
private noncomputable def ibox32 : Fin 4 → FixedTape.I := splitI ibox31 1 192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 false
private noncomputable def ibox33 : Fin 4 → FixedTape.I := splitI ibox32 0 230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 false
private noncomputable def ibox34 : Fin 4 → FixedTape.I := splitI ibox32 0 230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 true
private noncomputable def ibox35 : Fin 4 → FixedTape.I := splitI ibox31 1 192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 true
private noncomputable def ibox36 : Fin 4 → FixedTape.I := splitI ibox35 0 230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 false
private noncomputable def ibox37 : Fin 4 → FixedTape.I := splitI ibox36 2 72051862989910282854885557795460530904244691315550926766739452721206936292988132559898332364800000000000000000000000 false
private noncomputable def ibox38 : Fin 4 → FixedTape.I := splitI ibox37 1 288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 false
private noncomputable def ibox39 : Fin 4 → FixedTape.I := splitI ibox37 1 288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 true
private noncomputable def ibox40 : Fin 4 → FixedTape.I := splitI ibox36 2 72051862989910282854885557795460530904244691315550926766739452721206936292988132559898332364800000000000000000000000 true
private noncomputable def ibox41 : Fin 4 → FixedTape.I := splitI ibox35 0 230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 true
private noncomputable def ibox42 : Fin 4 → FixedTape.I := splitI ibox41 2 72051862989910282854885557795460530904244691315550926766739452721206936292988132559898332364800000000000000000000000 false
private noncomputable def ibox43 : Fin 4 → FixedTape.I := splitI ibox42 1 288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 false
private noncomputable def ibox44 : Fin 4 → FixedTape.I := splitI ibox42 1 288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 true
private noncomputable def ibox45 : Fin 4 → FixedTape.I := splitI ibox41 2 72051862989910282854885557795460530904244691315550926766739452721206936292988132559898332364800000000000000000000000 true
private noncomputable def ibox46 : Fin 4 → FixedTape.I := splitI ibox2 2 96069150653213710473180743727280707872326255087401235688985936961609248390650843413197776486400000000000000000000000 true
private noncomputable def ibox47 : Fin 4 → FixedTape.I := splitI ibox46 2 144103725979820565709771115590921061808489382631101853533478905442413872585976265119796664729600000000000000000000000 false
private noncomputable def ibox48 : Fin 4 → FixedTape.I := splitI ibox47 1 192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 false
private noncomputable def ibox49 : Fin 4 → FixedTape.I := splitI ibox48 0 230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 false
private noncomputable def ibox50 : Fin 4 → FixedTape.I := splitI ibox48 0 230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 true
private noncomputable def ibox51 : Fin 4 → FixedTape.I := splitI ibox47 1 192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 true
private noncomputable def ibox52 : Fin 4 → FixedTape.I := splitI ibox51 0 230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 false
private noncomputable def ibox53 : Fin 4 → FixedTape.I := splitI ibox51 0 230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 true
private noncomputable def ibox54 : Fin 4 → FixedTape.I := splitI ibox46 2 144103725979820565709771115590921061808489382631101853533478905442413872585976265119796664729600000000000000000000000 true
private noncomputable def ibox55 : Fin 4 → FixedTape.I := splitI ibox54 0 230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 false
private noncomputable def ibox56 : Fin 4 → FixedTape.I := splitI ibox54 0 230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 true
private noncomputable def ibox57 : Fin 4 → FixedTape.I := splitI ibox56 1 192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 false
private noncomputable def ibox58 : Fin 4 → FixedTape.I := splitI ibox56 1 192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 true
private noncomputable def ibox59 : Fin 4 → FixedTape.I := splitI ibox0 2 192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 true
private noncomputable def ibox60 : Fin 4 → FixedTape.I := splitI ibox59 3 192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 false
private noncomputable def ibox61 : Fin 4 → FixedTape.I := splitI ibox60 2 288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 false
private noncomputable def ibox62 : Fin 4 → FixedTape.I := faceI ibox61 3 false
private noncomputable def ibox63 : Fin 4 → FixedTape.I := splitI ibox62 2 240172876633034276182951859318201769680815637718503089222464842404023120976627108532994441216000000000000000000000000 false
private noncomputable def ibox64 : Fin 4 → FixedTape.I := splitI ibox63 0 230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 false
private noncomputable def ibox65 : Fin 4 → FixedTape.I := splitI ibox63 0 230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 true
private noncomputable def ibox66 : Fin 4 → FixedTape.I := splitI ibox62 2 240172876633034276182951859318201769680815637718503089222464842404023120976627108532994441216000000000000000000000000 true
private noncomputable def ibox67 : Fin 4 → FixedTape.I := splitI ibox66 2 264190164296337703801247045250021946648897201490353398144711326644425433074289819386293885337600000000000000000000000 false
private noncomputable def ibox68 : Fin 4 → FixedTape.I := splitI ibox67 1 192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 false
private noncomputable def ibox69 : Fin 4 → FixedTape.I := splitI ibox67 1 192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 true
private noncomputable def ibox70 : Fin 4 → FixedTape.I := splitI ibox66 2 264190164296337703801247045250021946648897201490353398144711326644425433074289819386293885337600000000000000000000000 true
private noncomputable def ibox71 : Fin 4 → FixedTape.I := faceI ibox70 2 false
private noncomputable def ibox72 : Fin 4 → FixedTape.I := splitI ibox60 2 288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 true
private noncomputable def ibox73 : Fin 4 → FixedTape.I := splitI ibox72 2 336242027286247986656132603045482477553141892805904324911450779365632369367277951946192217702400000000000000000000000 false
private noncomputable def ibox74 : Fin 4 → FixedTape.I := faceI ibox73 3 false
private noncomputable def ibox75 : Fin 4 → FixedTape.I := splitI ibox74 2 312224739622944559037837417113662300585060329034054015989204295125230057269615241092892773580800000000000000000000000 false
private noncomputable def ibox76 : Fin 4 → FixedTape.I := faceI ibox75 2 false
private noncomputable def ibox77 : Fin 4 → FixedTape.I := splitI ibox74 2 312224739622944559037837417113662300585060329034054015989204295125230057269615241092892773580800000000000000000000000 true
private noncomputable def ibox78 : Fin 4 → FixedTape.I := faceI ibox77 2 false
private noncomputable def ibox79 : Fin 4 → FixedTape.I := splitI ibox72 2 336242027286247986656132603045482477553141892805904324911450779365632369367277951946192217702400000000000000000000000 true
private noncomputable def ibox80 : Fin 4 → FixedTape.I := splitI ibox79 2 360259314949551414274427788977302654521223456577754633833697263606034681464940662799491661824000000000000000000000000 false
private noncomputable def ibox81 : Fin 4 → FixedTape.I := faceI ibox80 2 false
private noncomputable def ibox82 : Fin 4 → FixedTape.I := splitI ibox79 2 360259314949551414274427788977302654521223456577754633833697263606034681464940662799491661824000000000000000000000000 true
private noncomputable def ibox83 : Fin 4 → FixedTape.I := faceI ibox82 2 false
private noncomputable def ibox84 : Fin 4 → FixedTape.I := splitI ibox59 3 192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 true
private noncomputable def ibox85 : Fin 4 → FixedTape.I := splitI ibox84 2 288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 false
private noncomputable def ibox86 : Fin 4 → FixedTape.I := faceI ibox85 3 false
private noncomputable def ibox87 : Fin 4 → FixedTape.I := splitI ibox86 2 240172876633034276182951859318201769680815637718503089222464842404023120976627108532994441216000000000000000000000000 false
private noncomputable def ibox88 : Fin 4 → FixedTape.I := splitI ibox87 2 216155588969730848564656673386381592712734073946652780300218358163620808878964397679694997094400000000000000000000000 false
private noncomputable def ibox89 : Fin 4 → FixedTape.I := splitI ibox87 2 216155588969730848564656673386381592712734073946652780300218358163620808878964397679694997094400000000000000000000000 true
private noncomputable def ibox90 : Fin 4 → FixedTape.I := splitI ibox86 2 240172876633034276182951859318201769680815637718503089222464842404023120976627108532994441216000000000000000000000000 true
private noncomputable def ibox91 : Fin 4 → FixedTape.I := splitI ibox90 2 264190164296337703801247045250021946648897201490353398144711326644425433074289819386293885337600000000000000000000000 false
private noncomputable def ibox92 : Fin 4 → FixedTape.I := splitI ibox90 2 264190164296337703801247045250021946648897201490353398144711326644425433074289819386293885337600000000000000000000000 true
private noncomputable def ibox93 : Fin 4 → FixedTape.I := splitI ibox84 2 288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 true
private noncomputable def ibox94 : Fin 4 → FixedTape.I := splitI ibox93 2 336242027286247986656132603045482477553141892805904324911450779365632369367277951946192217702400000000000000000000000 false
private noncomputable def ibox95 : Fin 4 → FixedTape.I := faceI ibox94 3 false
private noncomputable def ibox96 : Fin 4 → FixedTape.I := splitI ibox95 2 312224739622944559037837417113662300585060329034054015989204295125230057269615241092892773580800000000000000000000000 false
private noncomputable def ibox97 : Fin 4 → FixedTape.I := splitI ibox95 2 312224739622944559037837417113662300585060329034054015989204295125230057269615241092892773580800000000000000000000000 true
private noncomputable def ibox98 : Fin 4 → FixedTape.I := faceI ibox97 2 false
private noncomputable def ibox99 : Fin 4 → FixedTape.I := splitI ibox93 2 336242027286247986656132603045482477553141892805904324911450779365632369367277951946192217702400000000000000000000000 true
private noncomputable def ibox100 : Fin 4 → FixedTape.I := splitI ibox99 2 360259314949551414274427788977302654521223456577754633833697263606034681464940662799491661824000000000000000000000000 false
private noncomputable def ibox101 : Fin 4 → FixedTape.I := faceI ibox100 2 false
private noncomputable def ibox102 : Fin 4 → FixedTape.I := splitI ibox99 2 360259314949551414274427788977302654521223456577754633833697263606034681464940662799491661824000000000000000000000000 true
private noncomputable def ibox103 : Fin 4 → FixedTape.I := faceI ibox102 2 false
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
private noncomputable def tree101 : TapeTree := .centered (candidateRows ibox101) (candidateRows (FixedTape.midBox ibox101))
attribute [irreducible] tree101
private theorem sign_101 : 2*denominator*(computed denominator (FixedTape.midBox ibox101)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox101).gradient k).lo.natAbs ((computed denominator ibox101).gradient k).hi.natAbs : Int)*((ibox101 k).hi-(ibox101 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox101
    (computed denominator ibox101) (computed denominator (FixedTape.midBox ibox101))
    (by decide +kernel)
private theorem midpoint_even_101 : ∀ k, 2 ∣ (ibox101 k).lo+(ibox101 k).hi := by decide +kernel
private theorem accepted_101 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox101) tree101 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox101 midpoint_even_101
  simp only [tree101,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox101,candidate_valid h (FixedTape.midBox ibox101),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox101 139 (FixedTape.rowsAux denominator ibox101 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox101) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_101
private noncomputable def tree100 : TapeTree := .face 2 false (candidateRows ibox100) tree101
attribute [irreducible] tree100
private theorem sign_100 : ((computed denominator ibox100).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_100 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox100) tree100 = true := by
  simp only [tree100,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox100,?_,accepted_101 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox100)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox100).gradient 2).hi) denominator_positive).1 sign_100
private noncomputable def tree99 : TapeTree := .split 2 (((360259314949551414274427788977302654521223456577754633833697263606034681464940662799491661824000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree100 tree102
attribute [irreducible] tree99
private theorem accepted_99 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox99) tree99 = true := by
  simp only [tree99,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox99 2 (360259314949551414274427788977302654521223456577754633833697263606034681464940662799491661824000000000000000000000000 : Int) false,decode_split denominator ibox99 2 (360259314949551414274427788977302654521223456577754633833697263606034681464940662799491661824000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_100 h,accepted_102 h⟩
private noncomputable def tree98 : TapeTree := .centered (candidateRows ibox98) (candidateRows (FixedTape.midBox ibox98))
attribute [irreducible] tree98
private theorem sign_98 : 2*denominator*(computed denominator (FixedTape.midBox ibox98)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox98).gradient k).lo.natAbs ((computed denominator ibox98).gradient k).hi.natAbs : Int)*((ibox98 k).hi-(ibox98 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox98
    (computed denominator ibox98) (computed denominator (FixedTape.midBox ibox98))
    (by decide +kernel)
private theorem midpoint_even_98 : ∀ k, 2 ∣ (ibox98 k).lo+(ibox98 k).hi := by decide +kernel
private theorem accepted_98 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox98) tree98 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox98 midpoint_even_98
  simp only [tree98,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox98,candidate_valid h (FixedTape.midBox ibox98),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox98 139 (FixedTape.rowsAux denominator ibox98 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox98) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_98
private noncomputable def tree97 : TapeTree := .face 2 false (candidateRows ibox97) tree98
attribute [irreducible] tree97
private theorem sign_97 : ((computed denominator ibox97).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_97 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox97) tree97 = true := by
  simp only [tree97,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox97,?_,accepted_98 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox97)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox97).gradient 2).hi) denominator_positive).1 sign_97
private noncomputable def tree96 : TapeTree := .centered (candidateRows ibox96) (candidateRows (FixedTape.midBox ibox96))
attribute [irreducible] tree96
private theorem sign_96 : 2*denominator*(computed denominator (FixedTape.midBox ibox96)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox96).gradient k).lo.natAbs ((computed denominator ibox96).gradient k).hi.natAbs : Int)*((ibox96 k).hi-(ibox96 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox96
    (computed denominator ibox96) (computed denominator (FixedTape.midBox ibox96))
    (by decide +kernel)
private theorem midpoint_even_96 : ∀ k, 2 ∣ (ibox96 k).lo+(ibox96 k).hi := by decide +kernel
private theorem accepted_96 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox96) tree96 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox96 midpoint_even_96
  simp only [tree96,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox96,candidate_valid h (FixedTape.midBox ibox96),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox96 139 (FixedTape.rowsAux denominator ibox96 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox96) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_96
private noncomputable def tree95 : TapeTree := .split 2 (((312224739622944559037837417113662300585060329034054015989204295125230057269615241092892773580800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree96 tree97
attribute [irreducible] tree95
private theorem accepted_95 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox95) tree95 = true := by
  simp only [tree95,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox95 2 (312224739622944559037837417113662300585060329034054015989204295125230057269615241092892773580800000000000000000000000 : Int) false,decode_split denominator ibox95 2 (312224739622944559037837417113662300585060329034054015989204295125230057269615241092892773580800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_96 h,accepted_97 h⟩
private noncomputable def tree94 : TapeTree := .face 3 false (candidateRows ibox94) tree95
attribute [irreducible] tree94
private theorem sign_94 : ((computed denominator ibox94).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_94 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox94) tree94 = true := by
  simp only [tree94,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox94,?_,accepted_95 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox94)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox94).gradient 3).hi) denominator_positive).1 sign_94
private noncomputable def tree93 : TapeTree := .split 2 (((336242027286247986656132603045482477553141892805904324911450779365632369367277951946192217702400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree94 tree99
attribute [irreducible] tree93
private theorem accepted_93 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox93) tree93 = true := by
  simp only [tree93,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox93 2 (336242027286247986656132603045482477553141892805904324911450779365632369367277951946192217702400000000000000000000000 : Int) false,decode_split denominator ibox93 2 (336242027286247986656132603045482477553141892805904324911450779365632369367277951946192217702400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_94 h,accepted_99 h⟩
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
private noncomputable def tree90 : TapeTree := .split 2 (((264190164296337703801247045250021946648897201490353398144711326644425433074289819386293885337600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree91 tree92
attribute [irreducible] tree90
private theorem accepted_90 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox90) tree90 = true := by
  simp only [tree90,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox90 2 (264190164296337703801247045250021946648897201490353398144711326644425433074289819386293885337600000000000000000000000 : Int) false,decode_split denominator ibox90 2 (264190164296337703801247045250021946648897201490353398144711326644425433074289819386293885337600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_91 h,accepted_92 h⟩
private noncomputable def tree89 : TapeTree := .centered (candidateRows ibox89) (candidateRows (FixedTape.midBox ibox89))
attribute [irreducible] tree89
private theorem sign_89 : 2*denominator*(computed denominator (FixedTape.midBox ibox89)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox89).gradient k).lo.natAbs ((computed denominator ibox89).gradient k).hi.natAbs : Int)*((ibox89 k).hi-(ibox89 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox89
    (computed denominator ibox89) (computed denominator (FixedTape.midBox ibox89))
    (by decide +kernel)
private theorem midpoint_even_89 : ∀ k, 2 ∣ (ibox89 k).lo+(ibox89 k).hi := by decide +kernel
private theorem accepted_89 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox89) tree89 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox89 midpoint_even_89
  simp only [tree89,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox89,candidate_valid h (FixedTape.midBox ibox89),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox89 139 (FixedTape.rowsAux denominator ibox89 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox89) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_89
private noncomputable def tree88 : TapeTree := .centered (candidateRows ibox88) (candidateRows (FixedTape.midBox ibox88))
attribute [irreducible] tree88
private theorem sign_88 : 2*denominator*(computed denominator (FixedTape.midBox ibox88)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox88).gradient k).lo.natAbs ((computed denominator ibox88).gradient k).hi.natAbs : Int)*((ibox88 k).hi-(ibox88 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox88
    (computed denominator ibox88) (computed denominator (FixedTape.midBox ibox88))
    (by decide +kernel)
private theorem midpoint_even_88 : ∀ k, 2 ∣ (ibox88 k).lo+(ibox88 k).hi := by decide +kernel
private theorem accepted_88 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox88) tree88 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox88 midpoint_even_88
  simp only [tree88,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox88,candidate_valid h (FixedTape.midBox ibox88),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox88 139 (FixedTape.rowsAux denominator ibox88 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox88) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_88
private noncomputable def tree87 : TapeTree := .split 2 (((216155588969730848564656673386381592712734073946652780300218358163620808878964397679694997094400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree88 tree89
attribute [irreducible] tree87
private theorem accepted_87 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox87) tree87 = true := by
  simp only [tree87,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox87 2 (216155588969730848564656673386381592712734073946652780300218358163620808878964397679694997094400000000000000000000000 : Int) false,decode_split denominator ibox87 2 (216155588969730848564656673386381592712734073946652780300218358163620808878964397679694997094400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_88 h,accepted_89 h⟩
private noncomputable def tree86 : TapeTree := .split 2 (((240172876633034276182951859318201769680815637718503089222464842404023120976627108532994441216000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree87 tree90
attribute [irreducible] tree86
private theorem accepted_86 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox86) tree86 = true := by
  simp only [tree86,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox86 2 (240172876633034276182951859318201769680815637718503089222464842404023120976627108532994441216000000000000000000000000 : Int) false,decode_split denominator ibox86 2 (240172876633034276182951859318201769680815637718503089222464842404023120976627108532994441216000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_87 h,accepted_90 h⟩
private noncomputable def tree85 : TapeTree := .face 3 false (candidateRows ibox85) tree86
attribute [irreducible] tree85
private theorem sign_85 : ((computed denominator ibox85).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_85 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox85) tree85 = true := by
  simp only [tree85,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox85,?_,accepted_86 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox85)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox85).gradient 3).hi) denominator_positive).1 sign_85
private noncomputable def tree84 : TapeTree := .split 2 (((288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree85 tree93
attribute [irreducible] tree84
private theorem accepted_84 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox84) tree84 = true := by
  simp only [tree84,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox84 2 (288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 : Int) false,decode_split denominator ibox84 2 (288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_85 h,accepted_93 h⟩
private noncomputable def tree83 : TapeTree := .direct (candidateRows ibox83)
attribute [irreducible] tree83
private theorem sign_83 : (computed denominator ibox83).value.hi ≤ 0 := by decide +kernel
private theorem accepted_83 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox83) tree83 = true := by
  simp only [tree83,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  refine ⟨root_in_range,candidate_valid h ibox83,?_⟩
  rw [candidate_root]
  simpa [FixedTape.decodeRow,FixedTape.decode] using (h.child_10.2.2.2.1 denominator (computed denominator ibox83).value.hi denominator_positive).1 sign_83
private noncomputable def tree82 : TapeTree := .face 2 false (candidateRows ibox82) tree83
attribute [irreducible] tree82
private theorem sign_82 : ((computed denominator ibox82).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_82 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox82) tree82 = true := by
  simp only [tree82,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox82,?_,accepted_83 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox82)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox82).gradient 2).hi) denominator_positive).1 sign_82
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
private noncomputable def tree80 : TapeTree := .face 2 false (candidateRows ibox80) tree81
attribute [irreducible] tree80
private theorem sign_80 : ((computed denominator ibox80).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_80 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox80) tree80 = true := by
  simp only [tree80,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox80,?_,accepted_81 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox80)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox80).gradient 2).hi) denominator_positive).1 sign_80
private noncomputable def tree79 : TapeTree := .split 2 (((360259314949551414274427788977302654521223456577754633833697263606034681464940662799491661824000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree80 tree82
attribute [irreducible] tree79
private theorem accepted_79 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox79) tree79 = true := by
  simp only [tree79,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox79 2 (360259314949551414274427788977302654521223456577754633833697263606034681464940662799491661824000000000000000000000000 : Int) false,decode_split denominator ibox79 2 (360259314949551414274427788977302654521223456577754633833697263606034681464940662799491661824000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_80 h,accepted_82 h⟩
private noncomputable def tree78 : TapeTree := .centered (candidateRows ibox78) (candidateRows (FixedTape.midBox ibox78))
attribute [irreducible] tree78
private theorem sign_78 : 2*denominator*(computed denominator (FixedTape.midBox ibox78)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox78).gradient k).lo.natAbs ((computed denominator ibox78).gradient k).hi.natAbs : Int)*((ibox78 k).hi-(ibox78 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox78
    (computed denominator ibox78) (computed denominator (FixedTape.midBox ibox78))
    (by decide +kernel)
private theorem midpoint_even_78 : ∀ k, 2 ∣ (ibox78 k).lo+(ibox78 k).hi := by decide +kernel
private theorem accepted_78 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox78) tree78 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox78 midpoint_even_78
  simp only [tree78,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox78,candidate_valid h (FixedTape.midBox ibox78),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox78 139 (FixedTape.rowsAux denominator ibox78 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox78) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_78
private noncomputable def tree77 : TapeTree := .face 2 false (candidateRows ibox77) tree78
attribute [irreducible] tree77
private theorem sign_77 : ((computed denominator ibox77).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_77 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox77) tree77 = true := by
  simp only [tree77,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox77,?_,accepted_78 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox77)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox77).gradient 2).hi) denominator_positive).1 sign_77
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
private noncomputable def tree75 : TapeTree := .face 2 false (candidateRows ibox75) tree76
attribute [irreducible] tree75
private theorem sign_75 : ((computed denominator ibox75).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_75 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox75) tree75 = true := by
  simp only [tree75,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox75,?_,accepted_76 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox75)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox75).gradient 2).hi) denominator_positive).1 sign_75
private noncomputable def tree74 : TapeTree := .split 2 (((312224739622944559037837417113662300585060329034054015989204295125230057269615241092892773580800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree75 tree77
attribute [irreducible] tree74
private theorem accepted_74 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox74) tree74 = true := by
  simp only [tree74,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox74 2 (312224739622944559037837417113662300585060329034054015989204295125230057269615241092892773580800000000000000000000000 : Int) false,decode_split denominator ibox74 2 (312224739622944559037837417113662300585060329034054015989204295125230057269615241092892773580800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_75 h,accepted_77 h⟩
private noncomputable def tree73 : TapeTree := .face 3 false (candidateRows ibox73) tree74
attribute [irreducible] tree73
private theorem sign_73 : ((computed denominator ibox73).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_73 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox73) tree73 = true := by
  simp only [tree73,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox73,?_,accepted_74 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox73)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox73).gradient 3).hi) denominator_positive).1 sign_73
private noncomputable def tree72 : TapeTree := .split 2 (((336242027286247986656132603045482477553141892805904324911450779365632369367277951946192217702400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree73 tree79
attribute [irreducible] tree72
private theorem accepted_72 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox72) tree72 = true := by
  simp only [tree72,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox72 2 (336242027286247986656132603045482477553141892805904324911450779365632369367277951946192217702400000000000000000000000 : Int) false,decode_split denominator ibox72 2 (336242027286247986656132603045482477553141892805904324911450779365632369367277951946192217702400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_73 h,accepted_79 h⟩
private noncomputable def tree71 : TapeTree := .centered (candidateRows ibox71) (candidateRows (FixedTape.midBox ibox71))
attribute [irreducible] tree71
private theorem sign_71 : 2*denominator*(computed denominator (FixedTape.midBox ibox71)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox71).gradient k).lo.natAbs ((computed denominator ibox71).gradient k).hi.natAbs : Int)*((ibox71 k).hi-(ibox71 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox71
    (computed denominator ibox71) (computed denominator (FixedTape.midBox ibox71))
    (by decide +kernel)
private theorem midpoint_even_71 : ∀ k, 2 ∣ (ibox71 k).lo+(ibox71 k).hi := by decide +kernel
private theorem accepted_71 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox71) tree71 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox71 midpoint_even_71
  simp only [tree71,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox71,candidate_valid h (FixedTape.midBox ibox71),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox71 139 (FixedTape.rowsAux denominator ibox71 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox71) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_71
private noncomputable def tree70 : TapeTree := .face 2 false (candidateRows ibox70) tree71
attribute [irreducible] tree70
private theorem sign_70 : ((computed denominator ibox70).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_70 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox70) tree70 = true := by
  simp only [tree70,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox70,?_,accepted_71 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox70)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox70).gradient 2).hi) denominator_positive).1 sign_70
private noncomputable def tree69 : TapeTree := .centered (candidateRows ibox69) (candidateRows (FixedTape.midBox ibox69))
attribute [irreducible] tree69
private theorem sign_69 : 2*denominator*(computed denominator (FixedTape.midBox ibox69)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox69).gradient k).lo.natAbs ((computed denominator ibox69).gradient k).hi.natAbs : Int)*((ibox69 k).hi-(ibox69 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox69
    (computed denominator ibox69) (computed denominator (FixedTape.midBox ibox69))
    (by decide +kernel)
private theorem midpoint_even_69 : ∀ k, 2 ∣ (ibox69 k).lo+(ibox69 k).hi := by decide +kernel
private theorem accepted_69 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox69) tree69 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox69 midpoint_even_69
  simp only [tree69,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox69,candidate_valid h (FixedTape.midBox ibox69),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox69 139 (FixedTape.rowsAux denominator ibox69 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox69) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_69
private noncomputable def tree68 : TapeTree := .centered (candidateRows ibox68) (candidateRows (FixedTape.midBox ibox68))
attribute [irreducible] tree68
private theorem sign_68 : 2*denominator*(computed denominator (FixedTape.midBox ibox68)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox68).gradient k).lo.natAbs ((computed denominator ibox68).gradient k).hi.natAbs : Int)*((ibox68 k).hi-(ibox68 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox68
    (computed denominator ibox68) (computed denominator (FixedTape.midBox ibox68))
    (by decide +kernel)
private theorem midpoint_even_68 : ∀ k, 2 ∣ (ibox68 k).lo+(ibox68 k).hi := by decide +kernel
private theorem accepted_68 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox68) tree68 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox68 midpoint_even_68
  simp only [tree68,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox68,candidate_valid h (FixedTape.midBox ibox68),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox68 139 (FixedTape.rowsAux denominator ibox68 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox68) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_68
private noncomputable def tree67 : TapeTree := .split 1 (((192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree68 tree69
attribute [irreducible] tree67
private theorem accepted_67 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox67) tree67 = true := by
  simp only [tree67,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox67 1 (192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 : Int) false,decode_split denominator ibox67 1 (192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_68 h,accepted_69 h⟩
private noncomputable def tree66 : TapeTree := .split 2 (((264190164296337703801247045250021946648897201490353398144711326644425433074289819386293885337600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree67 tree70
attribute [irreducible] tree66
private theorem accepted_66 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox66) tree66 = true := by
  simp only [tree66,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox66 2 (264190164296337703801247045250021946648897201490353398144711326644425433074289819386293885337600000000000000000000000 : Int) false,decode_split denominator ibox66 2 (264190164296337703801247045250021946648897201490353398144711326644425433074289819386293885337600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_67 h,accepted_70 h⟩
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
private noncomputable def tree64 : TapeTree := .centered (candidateRows ibox64) (candidateRows (FixedTape.midBox ibox64))
attribute [irreducible] tree64
private theorem sign_64 : 2*denominator*(computed denominator (FixedTape.midBox ibox64)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox64).gradient k).lo.natAbs ((computed denominator ibox64).gradient k).hi.natAbs : Int)*((ibox64 k).hi-(ibox64 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox64
    (computed denominator ibox64) (computed denominator (FixedTape.midBox ibox64))
    (by decide +kernel)
private theorem midpoint_even_64 : ∀ k, 2 ∣ (ibox64 k).lo+(ibox64 k).hi := by decide +kernel
private theorem accepted_64 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox64) tree64 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox64 midpoint_even_64
  simp only [tree64,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox64,candidate_valid h (FixedTape.midBox ibox64),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox64 139 (FixedTape.rowsAux denominator ibox64 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox64) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_64
private noncomputable def tree63 : TapeTree := .split 0 (((230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 : Int) : ℚ)/(denominator : ℚ)) tree64 tree65
attribute [irreducible] tree63
private theorem accepted_63 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox63) tree63 = true := by
  simp only [tree63,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox63 0 (230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 : Int) false,decode_split denominator ibox63 0 (230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_64 h,accepted_65 h⟩
private noncomputable def tree62 : TapeTree := .split 2 (((240172876633034276182951859318201769680815637718503089222464842404023120976627108532994441216000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree63 tree66
attribute [irreducible] tree62
private theorem accepted_62 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox62) tree62 = true := by
  simp only [tree62,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox62 2 (240172876633034276182951859318201769680815637718503089222464842404023120976627108532994441216000000000000000000000000 : Int) false,decode_split denominator ibox62 2 (240172876633034276182951859318201769680815637718503089222464842404023120976627108532994441216000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_63 h,accepted_66 h⟩
private noncomputable def tree61 : TapeTree := .face 3 false (candidateRows ibox61) tree62
attribute [irreducible] tree61
private theorem sign_61 : ((computed denominator ibox61).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_61 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox61) tree61 = true := by
  simp only [tree61,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox61,?_,accepted_62 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox61)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox61).gradient 3).hi) denominator_positive).1 sign_61
private noncomputable def tree60 : TapeTree := .split 2 (((288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree61 tree72
attribute [irreducible] tree60
private theorem accepted_60 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox60) tree60 = true := by
  simp only [tree60,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox60 2 (288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 : Int) false,decode_split denominator ibox60 2 (288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_61 h,accepted_72 h⟩
private noncomputable def tree59 : TapeTree := .split 3 (((192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree60 tree84
attribute [irreducible] tree59
private theorem accepted_59 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox59) tree59 = true := by
  simp only [tree59,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox59 3 (192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 : Int) false,decode_split denominator ibox59 3 (192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_60 h,accepted_84 h⟩
private noncomputable def tree58 : TapeTree := .centered (candidateRows ibox58) (candidateRows (FixedTape.midBox ibox58))
attribute [irreducible] tree58
private theorem sign_58 : 2*denominator*(computed denominator (FixedTape.midBox ibox58)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox58).gradient k).lo.natAbs ((computed denominator ibox58).gradient k).hi.natAbs : Int)*((ibox58 k).hi-(ibox58 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox58
    (computed denominator ibox58) (computed denominator (FixedTape.midBox ibox58))
    (by decide +kernel)
private theorem midpoint_even_58 : ∀ k, 2 ∣ (ibox58 k).lo+(ibox58 k).hi := by decide +kernel
private theorem accepted_58 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox58) tree58 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox58 midpoint_even_58
  simp only [tree58,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox58,candidate_valid h (FixedTape.midBox ibox58),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox58 139 (FixedTape.rowsAux denominator ibox58 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox58) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_58
private noncomputable def tree57 : TapeTree := .centered (candidateRows ibox57) (candidateRows (FixedTape.midBox ibox57))
attribute [irreducible] tree57
private theorem sign_57 : 2*denominator*(computed denominator (FixedTape.midBox ibox57)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox57).gradient k).lo.natAbs ((computed denominator ibox57).gradient k).hi.natAbs : Int)*((ibox57 k).hi-(ibox57 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox57
    (computed denominator ibox57) (computed denominator (FixedTape.midBox ibox57))
    (by decide +kernel)
private theorem midpoint_even_57 : ∀ k, 2 ∣ (ibox57 k).lo+(ibox57 k).hi := by decide +kernel
private theorem accepted_57 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox57) tree57 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox57 midpoint_even_57
  simp only [tree57,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox57,candidate_valid h (FixedTape.midBox ibox57),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox57 139 (FixedTape.rowsAux denominator ibox57 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox57) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_57
private noncomputable def tree56 : TapeTree := .split 1 (((192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree57 tree58
attribute [irreducible] tree56
private theorem accepted_56 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox56) tree56 = true := by
  simp only [tree56,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox56 1 (192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 : Int) false,decode_split denominator ibox56 1 (192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_57 h,accepted_58 h⟩
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
private noncomputable def tree54 : TapeTree := .split 0 (((230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 : Int) : ℚ)/(denominator : ℚ)) tree55 tree56
attribute [irreducible] tree54
private theorem accepted_54 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox54) tree54 = true := by
  simp only [tree54,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox54 0 (230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 : Int) false,decode_split denominator ibox54 0 (230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_55 h,accepted_56 h⟩
private noncomputable def tree53 : TapeTree := .centered (candidateRows ibox53) (candidateRows (FixedTape.midBox ibox53))
attribute [irreducible] tree53
private theorem sign_53 : 2*denominator*(computed denominator (FixedTape.midBox ibox53)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox53).gradient k).lo.natAbs ((computed denominator ibox53).gradient k).hi.natAbs : Int)*((ibox53 k).hi-(ibox53 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox53
    (computed denominator ibox53) (computed denominator (FixedTape.midBox ibox53))
    (by decide +kernel)
private theorem midpoint_even_53 : ∀ k, 2 ∣ (ibox53 k).lo+(ibox53 k).hi := by decide +kernel
private theorem accepted_53 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox53) tree53 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox53 midpoint_even_53
  simp only [tree53,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox53,candidate_valid h (FixedTape.midBox ibox53),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox53 139 (FixedTape.rowsAux denominator ibox53 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox53) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_53
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
private noncomputable def tree51 : TapeTree := .split 0 (((230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 : Int) : ℚ)/(denominator : ℚ)) tree52 tree53
attribute [irreducible] tree51
private theorem accepted_51 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox51) tree51 = true := by
  simp only [tree51,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox51 0 (230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 : Int) false,decode_split denominator ibox51 0 (230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_52 h,accepted_53 h⟩
private noncomputable def tree50 : TapeTree := .centered (candidateRows ibox50) (candidateRows (FixedTape.midBox ibox50))
attribute [irreducible] tree50
private theorem sign_50 : 2*denominator*(computed denominator (FixedTape.midBox ibox50)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox50).gradient k).lo.natAbs ((computed denominator ibox50).gradient k).hi.natAbs : Int)*((ibox50 k).hi-(ibox50 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox50
    (computed denominator ibox50) (computed denominator (FixedTape.midBox ibox50))
    (by decide +kernel)
private theorem midpoint_even_50 : ∀ k, 2 ∣ (ibox50 k).lo+(ibox50 k).hi := by decide +kernel
private theorem accepted_50 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox50) tree50 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox50 midpoint_even_50
  simp only [tree50,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox50,candidate_valid h (FixedTape.midBox ibox50),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox50 139 (FixedTape.rowsAux denominator ibox50 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox50) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_50
private noncomputable def tree49 : TapeTree := .centered (candidateRows ibox49) (candidateRows (FixedTape.midBox ibox49))
attribute [irreducible] tree49
private theorem sign_49 : 2*denominator*(computed denominator (FixedTape.midBox ibox49)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox49).gradient k).lo.natAbs ((computed denominator ibox49).gradient k).hi.natAbs : Int)*((ibox49 k).hi-(ibox49 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox49
    (computed denominator ibox49) (computed denominator (FixedTape.midBox ibox49))
    (by decide +kernel)
private theorem midpoint_even_49 : ∀ k, 2 ∣ (ibox49 k).lo+(ibox49 k).hi := by decide +kernel
private theorem accepted_49 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox49) tree49 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox49 midpoint_even_49
  simp only [tree49,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox49,candidate_valid h (FixedTape.midBox ibox49),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox49 139 (FixedTape.rowsAux denominator ibox49 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox49) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_49
private noncomputable def tree48 : TapeTree := .split 0 (((230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 : Int) : ℚ)/(denominator : ℚ)) tree49 tree50
attribute [irreducible] tree48
private theorem accepted_48 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox48) tree48 = true := by
  simp only [tree48,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox48 0 (230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 : Int) false,decode_split denominator ibox48 0 (230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_49 h,accepted_50 h⟩
private noncomputable def tree47 : TapeTree := .split 1 (((192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree48 tree51
attribute [irreducible] tree47
private theorem accepted_47 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox47) tree47 = true := by
  simp only [tree47,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox47 1 (192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 : Int) false,decode_split denominator ibox47 1 (192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_48 h,accepted_51 h⟩
private noncomputable def tree46 : TapeTree := .split 2 (((144103725979820565709771115590921061808489382631101853533478905442413872585976265119796664729600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree47 tree54
attribute [irreducible] tree46
private theorem accepted_46 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox46) tree46 = true := by
  simp only [tree46,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox46 2 (144103725979820565709771115590921061808489382631101853533478905442413872585976265119796664729600000000000000000000000 : Int) false,decode_split denominator ibox46 2 (144103725979820565709771115590921061808489382631101853533478905442413872585976265119796664729600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_47 h,accepted_54 h⟩
private noncomputable def tree45 : TapeTree := .centered (candidateRows ibox45) (candidateRows (FixedTape.midBox ibox45))
attribute [irreducible] tree45
private theorem sign_45 : 2*denominator*(computed denominator (FixedTape.midBox ibox45)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox45).gradient k).lo.natAbs ((computed denominator ibox45).gradient k).hi.natAbs : Int)*((ibox45 k).hi-(ibox45 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox45
    (computed denominator ibox45) (computed denominator (FixedTape.midBox ibox45))
    (by decide +kernel)
private theorem midpoint_even_45 : ∀ k, 2 ∣ (ibox45 k).lo+(ibox45 k).hi := by decide +kernel
private theorem accepted_45 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox45) tree45 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox45 midpoint_even_45
  simp only [tree45,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox45,candidate_valid h (FixedTape.midBox ibox45),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox45 139 (FixedTape.rowsAux denominator ibox45 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox45) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_45
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
private noncomputable def tree42 : TapeTree := .split 1 (((288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree43 tree44
attribute [irreducible] tree42
private theorem accepted_42 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox42) tree42 = true := by
  simp only [tree42,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox42 1 (288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 : Int) false,decode_split denominator ibox42 1 (288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_43 h,accepted_44 h⟩
private noncomputable def tree41 : TapeTree := .split 2 (((72051862989910282854885557795460530904244691315550926766739452721206936292988132559898332364800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree42 tree45
attribute [irreducible] tree41
private theorem accepted_41 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox41) tree41 = true := by
  simp only [tree41,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox41 2 (72051862989910282854885557795460530904244691315550926766739452721206936292988132559898332364800000000000000000000000 : Int) false,decode_split denominator ibox41 2 (72051862989910282854885557795460530904244691315550926766739452721206936292988132559898332364800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_42 h,accepted_45 h⟩
private noncomputable def tree40 : TapeTree := .centered (candidateRows ibox40) (candidateRows (FixedTape.midBox ibox40))
attribute [irreducible] tree40
private theorem sign_40 : 2*denominator*(computed denominator (FixedTape.midBox ibox40)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox40).gradient k).lo.natAbs ((computed denominator ibox40).gradient k).hi.natAbs : Int)*((ibox40 k).hi-(ibox40 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox40
    (computed denominator ibox40) (computed denominator (FixedTape.midBox ibox40))
    (by decide +kernel)
private theorem midpoint_even_40 : ∀ k, 2 ∣ (ibox40 k).lo+(ibox40 k).hi := by decide +kernel
private theorem accepted_40 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox40) tree40 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox40 midpoint_even_40
  simp only [tree40,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox40,candidate_valid h (FixedTape.midBox ibox40),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox40 139 (FixedTape.rowsAux denominator ibox40 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox40) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_40
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
private noncomputable def tree37 : TapeTree := .split 1 (((288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree38 tree39
attribute [irreducible] tree37
private theorem accepted_37 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox37) tree37 = true := by
  simp only [tree37,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox37 1 (288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 : Int) false,decode_split denominator ibox37 1 (288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_38 h,accepted_39 h⟩
private noncomputable def tree36 : TapeTree := .split 2 (((72051862989910282854885557795460530904244691315550926766739452721206936292988132559898332364800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree37 tree40
attribute [irreducible] tree36
private theorem accepted_36 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox36) tree36 = true := by
  simp only [tree36,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox36 2 (72051862989910282854885557795460530904244691315550926766739452721206936292988132559898332364800000000000000000000000 : Int) false,decode_split denominator ibox36 2 (72051862989910282854885557795460530904244691315550926766739452721206936292988132559898332364800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_37 h,accepted_40 h⟩
private noncomputable def tree35 : TapeTree := .split 0 (((230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 : Int) : ℚ)/(denominator : ℚ)) tree36 tree41
attribute [irreducible] tree35
private theorem accepted_35 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox35) tree35 = true := by
  simp only [tree35,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox35 0 (230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 : Int) false,decode_split denominator ibox35 0 (230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_36 h,accepted_41 h⟩
private noncomputable def tree34 : TapeTree := .centered (candidateRows ibox34) (candidateRows (FixedTape.midBox ibox34))
attribute [irreducible] tree34
private theorem sign_34 : 2*denominator*(computed denominator (FixedTape.midBox ibox34)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox34).gradient k).lo.natAbs ((computed denominator ibox34).gradient k).hi.natAbs : Int)*((ibox34 k).hi-(ibox34 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox34
    (computed denominator ibox34) (computed denominator (FixedTape.midBox ibox34))
    (by decide +kernel)
private theorem midpoint_even_34 : ∀ k, 2 ∣ (ibox34 k).lo+(ibox34 k).hi := by decide +kernel
private theorem accepted_34 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox34) tree34 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox34 midpoint_even_34
  simp only [tree34,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox34,candidate_valid h (FixedTape.midBox ibox34),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox34 139 (FixedTape.rowsAux denominator ibox34 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox34) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_34
private noncomputable def tree33 : TapeTree := .centered (candidateRows ibox33) (candidateRows (FixedTape.midBox ibox33))
attribute [irreducible] tree33
private theorem sign_33 : 2*denominator*(computed denominator (FixedTape.midBox ibox33)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox33).gradient k).lo.natAbs ((computed denominator ibox33).gradient k).hi.natAbs : Int)*((ibox33 k).hi-(ibox33 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox33
    (computed denominator ibox33) (computed denominator (FixedTape.midBox ibox33))
    (by decide +kernel)
private theorem midpoint_even_33 : ∀ k, 2 ∣ (ibox33 k).lo+(ibox33 k).hi := by decide +kernel
private theorem accepted_33 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox33) tree33 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox33 midpoint_even_33
  simp only [tree33,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox33,candidate_valid h (FixedTape.midBox ibox33),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox33 139 (FixedTape.rowsAux denominator ibox33 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox33) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_33
private noncomputable def tree32 : TapeTree := .split 0 (((230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 : Int) : ℚ)/(denominator : ℚ)) tree33 tree34
attribute [irreducible] tree32
private theorem accepted_32 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox32) tree32 = true := by
  simp only [tree32,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox32 0 (230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 : Int) false,decode_split denominator ibox32 0 (230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_33 h,accepted_34 h⟩
private noncomputable def tree31 : TapeTree := .split 1 (((192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree32 tree35
attribute [irreducible] tree31
private theorem accepted_31 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox31) tree31 = true := by
  simp only [tree31,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox31 1 (192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 : Int) false,decode_split denominator ibox31 1 (192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_32 h,accepted_35 h⟩
private noncomputable def tree30 : TapeTree := .centered (candidateRows ibox30) (candidateRows (FixedTape.midBox ibox30))
attribute [irreducible] tree30
private theorem sign_30 : 2*denominator*(computed denominator (FixedTape.midBox ibox30)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox30).gradient k).lo.natAbs ((computed denominator ibox30).gradient k).hi.natAbs : Int)*((ibox30 k).hi-(ibox30 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox30
    (computed denominator ibox30) (computed denominator (FixedTape.midBox ibox30))
    (by decide +kernel)
private theorem midpoint_even_30 : ∀ k, 2 ∣ (ibox30 k).lo+(ibox30 k).hi := by decide +kernel
private theorem accepted_30 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox30) tree30 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox30 midpoint_even_30
  simp only [tree30,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox30,candidate_valid h (FixedTape.midBox ibox30),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox30 139 (FixedTape.rowsAux denominator ibox30 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox30) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_30
private noncomputable def tree29 : TapeTree := .centered (candidateRows ibox29) (candidateRows (FixedTape.midBox ibox29))
attribute [irreducible] tree29
private theorem sign_29 : 2*denominator*(computed denominator (FixedTape.midBox ibox29)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox29).gradient k).lo.natAbs ((computed denominator ibox29).gradient k).hi.natAbs : Int)*((ibox29 k).hi-(ibox29 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox29
    (computed denominator ibox29) (computed denominator (FixedTape.midBox ibox29))
    (by decide +kernel)
private theorem midpoint_even_29 : ∀ k, 2 ∣ (ibox29 k).lo+(ibox29 k).hi := by decide +kernel
private theorem accepted_29 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox29) tree29 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox29 midpoint_even_29
  simp only [tree29,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox29,candidate_valid h (FixedTape.midBox ibox29),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox29 139 (FixedTape.rowsAux denominator ibox29 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox29) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_29
private noncomputable def tree28 : TapeTree := .centered (candidateRows ibox28) (candidateRows (FixedTape.midBox ibox28))
attribute [irreducible] tree28
private theorem sign_28 : 2*denominator*(computed denominator (FixedTape.midBox ibox28)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox28).gradient k).lo.natAbs ((computed denominator ibox28).gradient k).hi.natAbs : Int)*((ibox28 k).hi-(ibox28 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox28
    (computed denominator ibox28) (computed denominator (FixedTape.midBox ibox28))
    (by decide +kernel)
private theorem midpoint_even_28 : ∀ k, 2 ∣ (ibox28 k).lo+(ibox28 k).hi := by decide +kernel
private theorem accepted_28 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox28) tree28 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox28 midpoint_even_28
  simp only [tree28,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox28,candidate_valid h (FixedTape.midBox ibox28),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox28 139 (FixedTape.rowsAux denominator ibox28 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox28) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_28
private noncomputable def tree27 : TapeTree := .split 1 (((336242027286247986656132603045482477553141892805904324911450779365632369367277951946192217702400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree28 tree29
attribute [irreducible] tree27
private theorem accepted_27 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox27) tree27 = true := by
  simp only [tree27,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox27 1 (336242027286247986656132603045482477553141892805904324911450779365632369367277951946192217702400000000000000000000000 : Int) false,decode_split denominator ibox27 1 (336242027286247986656132603045482477553141892805904324911450779365632369367277951946192217702400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_28 h,accepted_29 h⟩
private noncomputable def tree26 : TapeTree := .split 2 (((24017287663303427618295185931820176968081563771850308922246484240402312097662710853299444121600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree27 tree30
attribute [irreducible] tree26
private theorem accepted_26 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox26) tree26 = true := by
  simp only [tree26,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox26 2 (24017287663303427618295185931820176968081563771850308922246484240402312097662710853299444121600000000000000000000000 : Int) false,decode_split denominator ibox26 2 (24017287663303427618295185931820176968081563771850308922246484240402312097662710853299444121600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_27 h,accepted_30 h⟩
private noncomputable def tree25 : TapeTree := .centered (candidateRows ibox25) (candidateRows (FixedTape.midBox ibox25))
attribute [irreducible] tree25
private theorem sign_25 : 2*denominator*(computed denominator (FixedTape.midBox ibox25)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox25).gradient k).lo.natAbs ((computed denominator ibox25).gradient k).hi.natAbs : Int)*((ibox25 k).hi-(ibox25 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox25
    (computed denominator ibox25) (computed denominator (FixedTape.midBox ibox25))
    (by decide +kernel)
private theorem midpoint_even_25 : ∀ k, 2 ∣ (ibox25 k).lo+(ibox25 k).hi := by decide +kernel
private theorem accepted_25 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox25) tree25 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox25 midpoint_even_25
  simp only [tree25,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox25,candidate_valid h (FixedTape.midBox ibox25),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox25 139 (FixedTape.rowsAux denominator ibox25 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox25) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_25
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
private noncomputable def tree23 : TapeTree := .split 2 (((24017287663303427618295185931820176968081563771850308922246484240402312097662710853299444121600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree24 tree25
attribute [irreducible] tree23
private theorem accepted_23 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox23) tree23 = true := by
  simp only [tree23,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox23 2 (24017287663303427618295185931820176968081563771850308922246484240402312097662710853299444121600000000000000000000000 : Int) false,decode_split denominator ibox23 2 (24017287663303427618295185931820176968081563771850308922246484240402312097662710853299444121600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_24 h,accepted_25 h⟩
private noncomputable def tree22 : TapeTree := .split 1 (((288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree23 tree26
attribute [irreducible] tree22
private theorem accepted_22 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox22) tree22 = true := by
  simp only [tree22,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox22 1 (288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 : Int) false,decode_split denominator ibox22 1 (288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_23 h,accepted_26 h⟩
private noncomputable def tree21 : TapeTree := .centered (candidateRows ibox21) (candidateRows (FixedTape.midBox ibox21))
attribute [irreducible] tree21
private theorem sign_21 : 2*denominator*(computed denominator (FixedTape.midBox ibox21)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox21).gradient k).lo.natAbs ((computed denominator ibox21).gradient k).hi.natAbs : Int)*((ibox21 k).hi-(ibox21 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox21
    (computed denominator ibox21) (computed denominator (FixedTape.midBox ibox21))
    (by decide +kernel)
private theorem midpoint_even_21 : ∀ k, 2 ∣ (ibox21 k).lo+(ibox21 k).hi := by decide +kernel
private theorem accepted_21 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox21) tree21 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox21 midpoint_even_21
  simp only [tree21,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox21,candidate_valid h (FixedTape.midBox ibox21),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox21 139 (FixedTape.rowsAux denominator ibox21 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox21) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_21
private noncomputable def tree20 : TapeTree := .centered (candidateRows ibox20) (candidateRows (FixedTape.midBox ibox20))
attribute [irreducible] tree20
private theorem sign_20 : 2*denominator*(computed denominator (FixedTape.midBox ibox20)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox20).gradient k).lo.natAbs ((computed denominator ibox20).gradient k).hi.natAbs : Int)*((ibox20 k).hi-(ibox20 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox20
    (computed denominator ibox20) (computed denominator (FixedTape.midBox ibox20))
    (by decide +kernel)
private theorem midpoint_even_20 : ∀ k, 2 ∣ (ibox20 k).lo+(ibox20 k).hi := by decide +kernel
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox20 midpoint_even_20
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox20,candidate_valid h (FixedTape.midBox ibox20),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox20 139 (FixedTape.rowsAux denominator ibox20 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox20) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_20
private noncomputable def tree19 : TapeTree := .split 1 (((288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree20 tree21
attribute [irreducible] tree19
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox19 1 (288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 : Int) false,decode_split denominator ibox19 1 (288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_20 h,accepted_21 h⟩
private noncomputable def tree18 : TapeTree := .centered (candidateRows ibox18) (candidateRows (FixedTape.midBox ibox18))
attribute [irreducible] tree18
private theorem sign_18 : 2*denominator*(computed denominator (FixedTape.midBox ibox18)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox18).gradient k).lo.natAbs ((computed denominator ibox18).gradient k).hi.natAbs : Int)*((ibox18 k).hi-(ibox18 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox18
    (computed denominator ibox18) (computed denominator (FixedTape.midBox ibox18))
    (by decide +kernel)
private theorem midpoint_even_18 : ∀ k, 2 ∣ (ibox18 k).lo+(ibox18 k).hi := by decide +kernel
private theorem accepted_18 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox18) tree18 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox18 midpoint_even_18
  simp only [tree18,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox18,candidate_valid h (FixedTape.midBox ibox18),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox18 139 (FixedTape.rowsAux denominator ibox18 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox18) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_18
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
private noncomputable def tree16 : TapeTree := .split 1 (((336242027286247986656132603045482477553141892805904324911450779365632369367277951946192217702400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree17 tree18
attribute [irreducible] tree16
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox16 1 (336242027286247986656132603045482477553141892805904324911450779365632369367277951946192217702400000000000000000000000 : Int) false,decode_split denominator ibox16 1 (336242027286247986656132603045482477553141892805904324911450779365632369367277951946192217702400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_17 h,accepted_18 h⟩
private noncomputable def tree15 : TapeTree := .centered (candidateRows ibox15) (candidateRows (FixedTape.midBox ibox15))
attribute [irreducible] tree15
private theorem sign_15 : 2*denominator*(computed denominator (FixedTape.midBox ibox15)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox15).gradient k).lo.natAbs ((computed denominator ibox15).gradient k).hi.natAbs : Int)*((ibox15 k).hi-(ibox15 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox15
    (computed denominator ibox15) (computed denominator (FixedTape.midBox ibox15))
    (by decide +kernel)
private theorem midpoint_even_15 : ∀ k, 2 ∣ (ibox15 k).lo+(ibox15 k).hi := by decide +kernel
private theorem accepted_15 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox15) tree15 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox15 midpoint_even_15
  simp only [tree15,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox15,candidate_valid h (FixedTape.midBox ibox15),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox15 139 (FixedTape.rowsAux denominator ibox15 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox15) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_15
private noncomputable def tree14 : TapeTree := .split 1 (((288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree15 tree16
attribute [irreducible] tree14
private theorem accepted_14 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox14) tree14 = true := by
  simp only [tree14,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox14 1 (288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 : Int) false,decode_split denominator ibox14 1 (288207451959641131419542231181842123616978765262203707066957810884827745171952530239593329459200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_15 h,accepted_16 h⟩
private noncomputable def tree13 : TapeTree := .split 2 (((24017287663303427618295185931820176968081563771850308922246484240402312097662710853299444121600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree14 tree19
attribute [irreducible] tree13
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox13 2 (24017287663303427618295185931820176968081563771850308922246484240402312097662710853299444121600000000000000000000000 : Int) false,decode_split denominator ibox13 2 (24017287663303427618295185931820176968081563771850308922246484240402312097662710853299444121600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_14 h,accepted_19 h⟩
private noncomputable def tree12 : TapeTree := .split 0 (((230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 : Int) : ℚ)/(denominator : ℚ)) tree13 tree22
attribute [irreducible] tree12
private theorem accepted_12 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox12) tree12 = true := by
  simp only [tree12,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox12 0 (230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 : Int) false,decode_split denominator ibox12 0 (230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_13 h,accepted_22 h⟩
private noncomputable def tree11 : TapeTree := .centered (candidateRows ibox11) (candidateRows (FixedTape.midBox ibox11))
attribute [irreducible] tree11
private theorem sign_11 : 2*denominator*(computed denominator (FixedTape.midBox ibox11)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox11).gradient k).lo.natAbs ((computed denominator ibox11).gradient k).hi.natAbs : Int)*((ibox11 k).hi-(ibox11 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox11
    (computed denominator ibox11) (computed denominator (FixedTape.midBox ibox11))
    (by decide +kernel)
private theorem midpoint_even_11 : ∀ k, 2 ∣ (ibox11 k).lo+(ibox11 k).hi := by decide +kernel
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox11 midpoint_even_11
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox11,candidate_valid h (FixedTape.midBox ibox11),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox11 139 (FixedTape.rowsAux denominator ibox11 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox11) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_11
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
private noncomputable def tree9 : TapeTree := .split 1 (((96069150653213710473180743727280707872326255087401235688985936961609248390650843413197776486400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree10 tree11
attribute [irreducible] tree9
private theorem accepted_9 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox9) tree9 = true := by
  simp only [tree9,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox9 1 (96069150653213710473180743727280707872326255087401235688985936961609248390650843413197776486400000000000000000000000 : Int) false,decode_split denominator ibox9 1 (96069150653213710473180743727280707872326255087401235688985936961609248390650843413197776486400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_10 h,accepted_11 h⟩
private noncomputable def tree8 : TapeTree := .centered (candidateRows ibox8) (candidateRows (FixedTape.midBox ibox8))
attribute [irreducible] tree8
private theorem sign_8 : 2*denominator*(computed denominator (FixedTape.midBox ibox8)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox8).gradient k).lo.natAbs ((computed denominator ibox8).gradient k).hi.natAbs : Int)*((ibox8 k).hi-(ibox8 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox8
    (computed denominator ibox8) (computed denominator (FixedTape.midBox ibox8))
    (by decide +kernel)
private theorem midpoint_even_8 : ∀ k, 2 ∣ (ibox8 k).lo+(ibox8 k).hi := by decide +kernel
private theorem accepted_8 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox8) tree8 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox8 midpoint_even_8
  simp only [tree8,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox8,candidate_valid h (FixedTape.midBox ibox8),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox8 139 (FixedTape.rowsAux denominator ibox8 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox8) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_8
private noncomputable def tree7 : TapeTree := .centered (candidateRows ibox7) (candidateRows (FixedTape.midBox ibox7))
attribute [irreducible] tree7
private theorem sign_7 : 2*denominator*(computed denominator (FixedTape.midBox ibox7)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox7).gradient k).lo.natAbs ((computed denominator ibox7).gradient k).hi.natAbs : Int)*((ibox7 k).hi-(ibox7 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox7
    (computed denominator ibox7) (computed denominator (FixedTape.midBox ibox7))
    (by decide +kernel)
private theorem midpoint_even_7 : ∀ k, 2 ∣ (ibox7 k).lo+(ibox7 k).hi := by decide +kernel
private theorem accepted_7 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox7) tree7 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox7 midpoint_even_7
  simp only [tree7,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox7,candidate_valid h (FixedTape.midBox ibox7),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox7 139 (FixedTape.rowsAux denominator ibox7 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox7) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_7
private noncomputable def tree6 : TapeTree := .split 1 (((96069150653213710473180743727280707872326255087401235688985936961609248390650843413197776486400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree7 tree8
attribute [irreducible] tree6
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox6 1 (96069150653213710473180743727280707872326255087401235688985936961609248390650843413197776486400000000000000000000000 : Int) false,decode_split denominator ibox6 1 (96069150653213710473180743727280707872326255087401235688985936961609248390650843413197776486400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_7 h,accepted_8 h⟩
private noncomputable def tree5 : TapeTree := .split 0 (((230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 : Int) : ℚ)/(denominator : ℚ)) tree6 tree9
attribute [irreducible] tree5
private theorem accepted_5 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox5) tree5 = true := by
  simp only [tree5,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox5 0 (230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 : Int) false,decode_split denominator ibox5 0 (230165673439991168532775444751448632853349155842804410861361462317024065737809384129553220745220878240296468480000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_6 h,accepted_9 h⟩
private noncomputable def tree4 : TapeTree := .split 1 (((192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree5 tree12
attribute [irreducible] tree4
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox4 1 (192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 : Int) false,decode_split denominator ibox4 1 (192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_5 h,accepted_12 h⟩
private noncomputable def tree3 : TapeTree := .split 2 (((48034575326606855236590371863640353936163127543700617844492968480804624195325421706598888243200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree31
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 2 (48034575326606855236590371863640353936163127543700617844492968480804624195325421706598888243200000000000000000000000 : Int) false,decode_split denominator ibox3 2 (48034575326606855236590371863640353936163127543700617844492968480804624195325421706598888243200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_31 h⟩
private noncomputable def tree2 : TapeTree := .split 2 (((96069150653213710473180743727280707872326255087401235688985936961609248390650843413197776486400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree46
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 2 (96069150653213710473180743727280707872326255087401235688985936961609248390650843413197776486400000000000000000000000 : Int) false,decode_split denominator ibox2 2 (96069150653213710473180743727280707872326255087401235688985936961609248390650843413197776486400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_3 h,accepted_46 h⟩
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
private noncomputable def tree0 : TapeTree := .split 2 (((192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree1 tree59
attribute [irreducible] tree0
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox0 2 (192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 : Int) false,decode_split denominator ibox0 2 (192138301306427420946361487454561415744652510174802471377971873923218496781301686826395552972800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_1 h,accepted_59 h⟩
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (19/32 : ℚ) (3020833333333333/5000000000000000 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 139 = e144 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (19/32 : ℚ) (3020833333333333/5000000000000000 : ℚ)) x → eval e144 x ≤ 0 := by
  have hb := h.child_4 tape 139 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell82_high_internal_top

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell82_high_internal_top
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((19/32 : ℚ) : ℝ) < p ∧ p ≤ ((3020833333333333/5000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 82 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 82 p)
    (hkb : ((3020833333333333/5000000000000000 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((19/32 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r)
    (hcase : bStar < a), internalResidual (0 : Fin 9) a p A r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell82_high_internal_top.cell_bound h.child_8 h.child_9 (Cell82_high_internal_top.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell82_high_internal_top
