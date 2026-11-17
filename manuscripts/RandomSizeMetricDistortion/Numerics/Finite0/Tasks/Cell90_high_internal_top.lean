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
namespace Cell90_high_internal_top
private noncomputable def qValues : Fin 4 → ℚ := ![(7561059334030734048730308975568168568/8242985148892576697193953337171505287 : ℚ),(9422352191074354292075000000000000000/8242985148892576697193953337171505287 : ℚ),(28351259775094450317121001657998573373/9009058626300321467676649316462484717 : ℚ),(-21462397941076195389010000000000000000/9009058626300321467676649316462484717 : ℚ)]
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
    priceLambda 90 p = ((7561059334030734048730308975568168568/8242985148892576697193953337171505287 : ℝ)+(9422352191074354292075000000000000000/8242985148892576697193953337171505287 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell90,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 90 p = (((28351259775094450317121001657998573373/9009058626300321467676649316462484717 : ℝ)+(-21462397941076195389010000000000000000/9009058626300321467676649316462484717 : ℝ)*p)-(145513/100000 : ℝ)*(1/1 : ℝ))/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell90,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e144 x = (x 0*(1-x 0))*(aPoint x+priceLambda 90 (x 0)*(HStar (yPoint x)-HStar (aPoint x)-HStar (capPoint x))+priceTau 90 (x 0)*psiStar (rPoint x)+(cStar-aPoint x-eta (0 : Fin 9)*psiStar (aPoint x))-(cStar-capPoint x-eta (0 : Fin 9)*psiStar (capPoint x))) := by
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
    (hL : lambdaStar (x 0) = priceLambda 90 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 90 (x 0)) :
    (1)*eval e144 x = (x 0*(1-x 0))*(internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_neg (not_le.mpr ha),if_neg (not_le.mpr hA),hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (3385416666666667/5000000000000000 : ℚ) (11/16 : ℚ)) x → eval e144 x ≤ 0)
    (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((3385416666666667/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((11/16 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 90 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 90 p)
    (hkb : ((11/16 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((3385416666666667/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r)
    (hcase : bStar < a) :
    internalResidual (0 : Fin 9) a p A r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxA,hxr⟩ := h7 (3385416666666667/5000000000000000 : ℚ) (11/16 : ℚ) bStar p a A r hpcell hkb hr.2 hap hcase hpA hAr
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,capPoint] using hxa
  have hAx : capPoint x = A := by simpa only [aPoint,rPoint,capPoint] using hxA
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,capPoint] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 90 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 90 (x 0) := by simpa only [hxp] using hT
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
.const (7561059334030734048730308975568168568/8242985148892576697193953337171505287 : ℚ),
.const (9422352191074354292075000000000000000/8242985148892576697193953337171505287 : ℚ),
.mul 108 1,
.add 107 109,
.const (28351259775094450317121001657998573373/9009058626300321467676649316462484717 : ℚ),
.const (-21462397941076195389010000000000000000/9009058626300321467676649316462484717 : ℚ),
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
private noncomputable def ssaQVals : Fin 18 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(-2840189/5000000 : ℚ),(113609/200000 : ℚ),(1085/4818 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ),(4818/3733 : ℚ),(145513/100000 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(7561059334030734048730308975568168568/8242985148892576697193953337171505287 : ℚ),(9422352191074354292075000000000000000/8242985148892576697193953337171505287 : ℚ),(28351259775094450317121001657998573373/9009058626300321467676649316462484717 : ℚ),(-21462397941076195389010000000000000000/9009058626300321467676649316462484717 : ℚ),(-145513/100000 : ℚ)]
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
private noncomputable def denominator : Int := 1391607218157102478724176890549751170938960491131049458355872827594134990938198837931619332915200000000000000000000000
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
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨942234053960538229409975980116559270268380535853392800025821635753492790505927302791866652541255862107955527680000000,956729962483007954122871612252953930020535337652596502619662568970967806270011701077988291379200000000000000000000000⟩,⟨0,1391607218157102478724176890549751170938960491131049458355872827594134990938198837931619332915200000000000000000000000⟩,⟨0,1391607218157102478724176890549751170938960491131049458355872827594134990938198837931619332915200000000000000000000000⟩,⟨0,1391607218157102478724176890549751170938960491131049458355872827594134990938198837931619332915200000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := splitI ibox0 2 695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 false
private noncomputable def ibox2 : Fin 4 → FixedTape.I := faceI ibox1 3 false
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 2 347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 1 695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox4 1 347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 false
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox5 2 173950902269637809840522111318718896367370061391381182294484103449266873867274854741452416614400000000000000000000000 false
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox5 2 173950902269637809840522111318718896367370061391381182294484103449266873867274854741452416614400000000000000000000000 true
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox4 1 347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 true
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox8 2 173950902269637809840522111318718896367370061391381182294484103449266873867274854741452416614400000000000000000000000 false
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox8 2 173950902269637809840522111318718896367370061391381182294484103449266873867274854741452416614400000000000000000000000 true
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox3 1 695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 true
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox11 1 1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 false
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox12 2 173950902269637809840522111318718896367370061391381182294484103449266873867274854741452416614400000000000000000000000 false
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox13 1 869754511348189049202610556593594481836850306956905911472420517246334369336374273707262083072000000000000000000000000 false
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox13 1 869754511348189049202610556593594481836850306956905911472420517246334369336374273707262083072000000000000000000000000 true
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox12 2 173950902269637809840522111318718896367370061391381182294484103449266873867274854741452416614400000000000000000000000 true
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox16 1 869754511348189049202610556593594481836850306956905911472420517246334369336374273707262083072000000000000000000000000 false
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox16 1 869754511348189049202610556593594481836850306956905911472420517246334369336374273707262083072000000000000000000000000 true
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox11 1 1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 true
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox19 2 173950902269637809840522111318718896367370061391381182294484103449266873867274854741452416614400000000000000000000000 false
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox20 1 1217656315887464668883654779231032274571590429739668276061388724144868117070923983190166916300800000000000000000000000 false
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox21 2 86975451134818904920261055659359448183685030695690591147242051724633436933637427370726208307200000000000000000000000 false
private noncomputable def ibox23 : Fin 4 → FixedTape.I := splitI ibox21 2 86975451134818904920261055659359448183685030695690591147242051724633436933637427370726208307200000000000000000000000 true
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox20 1 1217656315887464668883654779231032274571590429739668276061388724144868117070923983190166916300800000000000000000000000 true
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox24 2 86975451134818904920261055659359448183685030695690591147242051724633436933637427370726208307200000000000000000000000 false
private noncomputable def ibox26 : Fin 4 → FixedTape.I := faceI ibox25 1 true
private noncomputable def ibox27 : Fin 4 → FixedTape.I := splitI ibox26 0 949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 false
private noncomputable def ibox28 : Fin 4 → FixedTape.I := splitI ibox26 0 949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 true
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox24 2 86975451134818904920261055659359448183685030695690591147242051724633436933637427370726208307200000000000000000000000 true
private noncomputable def ibox30 : Fin 4 → FixedTape.I := splitI ibox29 1 1304631767022283573803915834890391722755275460435358867208630775869501554004561410560893124608000000000000000000000000 false
private noncomputable def ibox31 : Fin 4 → FixedTape.I := splitI ibox29 1 1304631767022283573803915834890391722755275460435358867208630775869501554004561410560893124608000000000000000000000000 true
private noncomputable def ibox32 : Fin 4 → FixedTape.I := faceI ibox31 1 true
private noncomputable def ibox33 : Fin 4 → FixedTape.I := splitI ibox32 2 130463176702228357380391583489039172275527546043535886720863077586950155400456141056089312460800000000000000000000000 false
private noncomputable def ibox34 : Fin 4 → FixedTape.I := splitI ibox32 2 130463176702228357380391583489039172275527546043535886720863077586950155400456141056089312460800000000000000000000000 true
private noncomputable def ibox35 : Fin 4 → FixedTape.I := splitI ibox19 2 173950902269637809840522111318718896367370061391381182294484103449266873867274854741452416614400000000000000000000000 true
private noncomputable def ibox36 : Fin 4 → FixedTape.I := splitI ibox35 1 1217656315887464668883654779231032274571590429739668276061388724144868117070923983190166916300800000000000000000000000 false
private noncomputable def ibox37 : Fin 4 → FixedTape.I := splitI ibox36 2 260926353404456714760783166978078344551055092087071773441726155173900310800912282112178624921600000000000000000000000 false
private noncomputable def ibox38 : Fin 4 → FixedTape.I := splitI ibox36 2 260926353404456714760783166978078344551055092087071773441726155173900310800912282112178624921600000000000000000000000 true
private noncomputable def ibox39 : Fin 4 → FixedTape.I := splitI ibox35 1 1217656315887464668883654779231032274571590429739668276061388724144868117070923983190166916300800000000000000000000000 true
private noncomputable def ibox40 : Fin 4 → FixedTape.I := splitI ibox39 2 260926353404456714760783166978078344551055092087071773441726155173900310800912282112178624921600000000000000000000000 false
private noncomputable def ibox41 : Fin 4 → FixedTape.I := splitI ibox40 1 1304631767022283573803915834890391722755275460435358867208630775869501554004561410560893124608000000000000000000000000 false
private noncomputable def ibox42 : Fin 4 → FixedTape.I := splitI ibox40 1 1304631767022283573803915834890391722755275460435358867208630775869501554004561410560893124608000000000000000000000000 true
private noncomputable def ibox43 : Fin 4 → FixedTape.I := splitI ibox42 0 949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 false
private noncomputable def ibox44 : Fin 4 → FixedTape.I := splitI ibox42 0 949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 true
private noncomputable def ibox45 : Fin 4 → FixedTape.I := splitI ibox39 2 260926353404456714760783166978078344551055092087071773441726155173900310800912282112178624921600000000000000000000000 true
private noncomputable def ibox46 : Fin 4 → FixedTape.I := splitI ibox45 0 949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 false
private noncomputable def ibox47 : Fin 4 → FixedTape.I := splitI ibox45 0 949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 true
private noncomputable def ibox48 : Fin 4 → FixedTape.I := splitI ibox2 2 347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 true
private noncomputable def ibox49 : Fin 4 → FixedTape.I := splitI ibox48 1 695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 false
private noncomputable def ibox50 : Fin 4 → FixedTape.I := splitI ibox49 2 521852706808913429521566333956156689102110184174143546883452310347800621601824564224357249843200000000000000000000000 false
private noncomputable def ibox51 : Fin 4 → FixedTape.I := splitI ibox50 1 347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 false
private noncomputable def ibox52 : Fin 4 → FixedTape.I := splitI ibox50 1 347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 true
private noncomputable def ibox53 : Fin 4 → FixedTape.I := splitI ibox49 2 521852706808913429521566333956156689102110184174143546883452310347800621601824564224357249843200000000000000000000000 true
private noncomputable def ibox54 : Fin 4 → FixedTape.I := splitI ibox53 1 347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 false
private noncomputable def ibox55 : Fin 4 → FixedTape.I := splitI ibox53 1 347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 true
private noncomputable def ibox56 : Fin 4 → FixedTape.I := splitI ibox55 0 949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 false
private noncomputable def ibox57 : Fin 4 → FixedTape.I := splitI ibox55 0 949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 true
private noncomputable def ibox58 : Fin 4 → FixedTape.I := splitI ibox48 1 695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 true
private noncomputable def ibox59 : Fin 4 → FixedTape.I := splitI ibox58 2 521852706808913429521566333956156689102110184174143546883452310347800621601824564224357249843200000000000000000000000 false
private noncomputable def ibox60 : Fin 4 → FixedTape.I := splitI ibox59 1 1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 false
private noncomputable def ibox61 : Fin 4 → FixedTape.I := splitI ibox60 1 869754511348189049202610556593594481836850306956905911472420517246334369336374273707262083072000000000000000000000000 false
private noncomputable def ibox62 : Fin 4 → FixedTape.I := splitI ibox60 1 869754511348189049202610556593594481836850306956905911472420517246334369336374273707262083072000000000000000000000000 true
private noncomputable def ibox63 : Fin 4 → FixedTape.I := splitI ibox59 1 1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 true
private noncomputable def ibox64 : Fin 4 → FixedTape.I := splitI ibox63 1 1217656315887464668883654779231032274571590429739668276061388724144868117070923983190166916300800000000000000000000000 false
private noncomputable def ibox65 : Fin 4 → FixedTape.I := splitI ibox64 2 434877255674094524601305278296797240918425153478452955736210258623167184668187136853631041536000000000000000000000000 false
private noncomputable def ibox66 : Fin 4 → FixedTape.I := splitI ibox64 2 434877255674094524601305278296797240918425153478452955736210258623167184668187136853631041536000000000000000000000000 true
private noncomputable def ibox67 : Fin 4 → FixedTape.I := splitI ibox63 1 1217656315887464668883654779231032274571590429739668276061388724144868117070923983190166916300800000000000000000000000 true
private noncomputable def ibox68 : Fin 4 → FixedTape.I := splitI ibox67 2 434877255674094524601305278296797240918425153478452955736210258623167184668187136853631041536000000000000000000000000 false
private noncomputable def ibox69 : Fin 4 → FixedTape.I := splitI ibox68 0 949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 false
private noncomputable def ibox70 : Fin 4 → FixedTape.I := splitI ibox68 0 949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 true
private noncomputable def ibox71 : Fin 4 → FixedTape.I := splitI ibox67 2 434877255674094524601305278296797240918425153478452955736210258623167184668187136853631041536000000000000000000000000 true
private noncomputable def ibox72 : Fin 4 → FixedTape.I := splitI ibox58 2 521852706808913429521566333956156689102110184174143546883452310347800621601824564224357249843200000000000000000000000 true
private noncomputable def ibox73 : Fin 4 → FixedTape.I := splitI ibox72 1 1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 false
private noncomputable def ibox74 : Fin 4 → FixedTape.I := splitI ibox73 0 949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 false
private noncomputable def ibox75 : Fin 4 → FixedTape.I := splitI ibox73 0 949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 true
private noncomputable def ibox76 : Fin 4 → FixedTape.I := splitI ibox72 1 1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 true
private noncomputable def ibox77 : Fin 4 → FixedTape.I := splitI ibox76 2 608828157943732334441827389615516137285795214869834138030694362072434058535461991595083458150400000000000000000000000 false
private noncomputable def ibox78 : Fin 4 → FixedTape.I := splitI ibox77 1 1217656315887464668883654779231032274571590429739668276061388724144868117070923983190166916300800000000000000000000000 false
private noncomputable def ibox79 : Fin 4 → FixedTape.I := splitI ibox77 1 1217656315887464668883654779231032274571590429739668276061388724144868117070923983190166916300800000000000000000000000 true
private noncomputable def ibox80 : Fin 4 → FixedTape.I := splitI ibox76 2 608828157943732334441827389615516137285795214869834138030694362072434058535461991595083458150400000000000000000000000 true
private noncomputable def ibox81 : Fin 4 → FixedTape.I := splitI ibox80 0 949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 false
private noncomputable def ibox82 : Fin 4 → FixedTape.I := splitI ibox80 0 949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 true
private noncomputable def ibox83 : Fin 4 → FixedTape.I := splitI ibox0 2 695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 true
private noncomputable def ibox84 : Fin 4 → FixedTape.I := splitI ibox83 2 1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 false
private noncomputable def ibox85 : Fin 4 → FixedTape.I := faceI ibox84 3 false
private noncomputable def ibox86 : Fin 4 → FixedTape.I := splitI ibox85 2 869754511348189049202610556593594481836850306956905911472420517246334369336374273707262083072000000000000000000000000 false
private noncomputable def ibox87 : Fin 4 → FixedTape.I := splitI ibox86 1 695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 false
private noncomputable def ibox88 : Fin 4 → FixedTape.I := splitI ibox87 1 347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 false
private noncomputable def ibox89 : Fin 4 → FixedTape.I := splitI ibox88 2 782779060213370144282349500934235033653165276261215320325178465521700932402736846336535874764800000000000000000000000 false
private noncomputable def ibox90 : Fin 4 → FixedTape.I := splitI ibox88 2 782779060213370144282349500934235033653165276261215320325178465521700932402736846336535874764800000000000000000000000 true
private noncomputable def ibox91 : Fin 4 → FixedTape.I := splitI ibox87 1 347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 true
private noncomputable def ibox92 : Fin 4 → FixedTape.I := splitI ibox91 2 782779060213370144282349500934235033653165276261215320325178465521700932402736846336535874764800000000000000000000000 false
private noncomputable def ibox93 : Fin 4 → FixedTape.I := splitI ibox91 2 782779060213370144282349500934235033653165276261215320325178465521700932402736846336535874764800000000000000000000000 true
private noncomputable def ibox94 : Fin 4 → FixedTape.I := splitI ibox86 1 695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 true
private noncomputable def ibox95 : Fin 4 → FixedTape.I := splitI ibox94 1 1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 false
private noncomputable def ibox96 : Fin 4 → FixedTape.I := splitI ibox95 2 782779060213370144282349500934235033653165276261215320325178465521700932402736846336535874764800000000000000000000000 false
private noncomputable def ibox97 : Fin 4 → FixedTape.I := splitI ibox95 2 782779060213370144282349500934235033653165276261215320325178465521700932402736846336535874764800000000000000000000000 true
private noncomputable def ibox98 : Fin 4 → FixedTape.I := splitI ibox94 1 1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 true
private noncomputable def ibox99 : Fin 4 → FixedTape.I := splitI ibox98 2 782779060213370144282349500934235033653165276261215320325178465521700932402736846336535874764800000000000000000000000 false
private noncomputable def ibox100 : Fin 4 → FixedTape.I := splitI ibox98 2 782779060213370144282349500934235033653165276261215320325178465521700932402736846336535874764800000000000000000000000 true
private noncomputable def ibox101 : Fin 4 → FixedTape.I := splitI ibox85 2 869754511348189049202610556593594481836850306956905911472420517246334369336374273707262083072000000000000000000000000 true
private noncomputable def ibox102 : Fin 4 → FixedTape.I := splitI ibox101 1 695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 false
private noncomputable def ibox103 : Fin 4 → FixedTape.I := splitI ibox102 2 956729962483007954122871612252953930020535337652596502619662568970967806270011701077988291379200000000000000000000000 false
private noncomputable def ibox104 : Fin 4 → FixedTape.I := splitI ibox103 1 347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 false
private noncomputable def ibox105 : Fin 4 → FixedTape.I := splitI ibox104 2 913242236915598501662741084423274205928692822304751207046041543108651087803192987392625187225600000000000000000000000 false
private noncomputable def ibox106 : Fin 4 → FixedTape.I := splitI ibox104 2 913242236915598501662741084423274205928692822304751207046041543108651087803192987392625187225600000000000000000000000 true
private noncomputable def ibox107 : Fin 4 → FixedTape.I := splitI ibox103 1 347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 true
private noncomputable def ibox108 : Fin 4 → FixedTape.I := splitI ibox102 2 956729962483007954122871612252953930020535337652596502619662568970967806270011701077988291379200000000000000000000000 true
private noncomputable def ibox109 : Fin 4 → FixedTape.I := splitI ibox108 1 347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 false
private noncomputable def ibox110 : Fin 4 → FixedTape.I := splitI ibox109 2 1000217688050417406583002140082633654112377853000441798193283594833284524736830414763351395532800000000000000000000000 false
private noncomputable def ibox111 : Fin 4 → FixedTape.I := splitI ibox109 2 1000217688050417406583002140082633654112377853000441798193283594833284524736830414763351395532800000000000000000000000 true
private noncomputable def ibox112 : Fin 4 → FixedTape.I := splitI ibox108 1 347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 true
private noncomputable def ibox113 : Fin 4 → FixedTape.I := splitI ibox112 2 1000217688050417406583002140082633654112377853000441798193283594833284524736830414763351395532800000000000000000000000 false
private noncomputable def ibox114 : Fin 4 → FixedTape.I := splitI ibox112 2 1000217688050417406583002140082633654112377853000441798193283594833284524736830414763351395532800000000000000000000000 true
private noncomputable def ibox115 : Fin 4 → FixedTape.I := splitI ibox101 1 695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 true
private noncomputable def ibox116 : Fin 4 → FixedTape.I := splitI ibox115 2 956729962483007954122871612252953930020535337652596502619662568970967806270011701077988291379200000000000000000000000 false
private noncomputable def ibox117 : Fin 4 → FixedTape.I := splitI ibox116 1 1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 false
private noncomputable def ibox118 : Fin 4 → FixedTape.I := splitI ibox116 1 1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 true
private noncomputable def ibox119 : Fin 4 → FixedTape.I := splitI ibox115 2 956729962483007954122871612252953930020535337652596502619662568970967806270011701077988291379200000000000000000000000 true
private noncomputable def ibox120 : Fin 4 → FixedTape.I := splitI ibox119 1 1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 false
private noncomputable def ibox121 : Fin 4 → FixedTape.I := splitI ibox119 1 1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 true
private noncomputable def ibox122 : Fin 4 → FixedTape.I := splitI ibox83 2 1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 true
private noncomputable def ibox123 : Fin 4 → FixedTape.I := splitI ibox122 2 1217656315887464668883654779231032274571590429739668276061388724144868117070923983190166916300800000000000000000000000 false
private noncomputable def ibox124 : Fin 4 → FixedTape.I := faceI ibox123 3 false
private noncomputable def ibox125 : Fin 4 → FixedTape.I := splitI ibox124 2 1130680864752645763963393723571672826387905399043977684914146672420234680137286555819440707993600000000000000000000000 false
private noncomputable def ibox126 : Fin 4 → FixedTape.I := splitI ibox125 1 695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 false
private noncomputable def ibox127 : Fin 4 → FixedTape.I := splitI ibox126 2 1087193139185236311503263195741993102296062883696132389340525646557917961670467842134077603840000000000000000000000000 false
private noncomputable def ibox128 : Fin 4 → FixedTape.I := faceI ibox127 2 false
private noncomputable def ibox129 : Fin 4 → FixedTape.I := splitI ibox126 2 1087193139185236311503263195741993102296062883696132389340525646557917961670467842134077603840000000000000000000000000 true
private noncomputable def ibox130 : Fin 4 → FixedTape.I := splitI ibox125 1 695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 true
private noncomputable def ibox131 : Fin 4 → FixedTape.I := faceI ibox130 2 false
private noncomputable def ibox132 : Fin 4 → FixedTape.I := splitI ibox124 2 1130680864752645763963393723571672826387905399043977684914146672420234680137286555819440707993600000000000000000000000 true
private noncomputable def ibox133 : Fin 4 → FixedTape.I := faceI ibox132 2 false
private noncomputable def ibox134 : Fin 4 → FixedTape.I := splitI ibox133 1 695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 false
private noncomputable def ibox135 : Fin 4 → FixedTape.I := splitI ibox133 1 695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 true
private noncomputable def ibox136 : Fin 4 → FixedTape.I := splitI ibox122 2 1217656315887464668883654779231032274571590429739668276061388724144868117070923983190166916300800000000000000000000000 true
private noncomputable def ibox137 : Fin 4 → FixedTape.I := splitI ibox136 2 1304631767022283573803915834890391722755275460435358867208630775869501554004561410560893124608000000000000000000000000 false
private noncomputable def ibox138 : Fin 4 → FixedTape.I := faceI ibox137 2 false
private noncomputable def ibox139 : Fin 4 → FixedTape.I := faceI ibox138 3 false
private noncomputable def ibox140 : Fin 4 → FixedTape.I := splitI ibox139 1 695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 false
private noncomputable def ibox141 : Fin 4 → FixedTape.I := splitI ibox139 1 695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 true
private noncomputable def ibox142 : Fin 4 → FixedTape.I := splitI ibox136 2 1304631767022283573803915834890391722755275460435358867208630775869501554004561410560893124608000000000000000000000000 true
private noncomputable def ibox143 : Fin 4 → FixedTape.I := faceI ibox142 2 false
private noncomputable def ibox144 : Fin 4 → FixedTape.I := faceI ibox143 3 false
private noncomputable def ibox145 : Fin 4 → FixedTape.I := splitI ibox144 1 695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 false
private noncomputable def ibox146 : Fin 4 → FixedTape.I := splitI ibox144 1 695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 true
private noncomputable def tree146 : TapeTree := .centered (candidateRows ibox146) (candidateRows (FixedTape.midBox ibox146))
attribute [irreducible] tree146
private theorem sign_146 : 2*denominator*(computed denominator (FixedTape.midBox ibox146)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox146).gradient k).lo.natAbs ((computed denominator ibox146).gradient k).hi.natAbs : Int)*((ibox146 k).hi-(ibox146 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox146
    (computed denominator ibox146) (computed denominator (FixedTape.midBox ibox146))
    (by decide +kernel)
private theorem midpoint_even_146 : ∀ k, 2 ∣ (ibox146 k).lo+(ibox146 k).hi := by decide +kernel
private theorem accepted_146 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox146) tree146 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox146 midpoint_even_146
  simp only [tree146,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox146,candidate_valid h (FixedTape.midBox ibox146),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox146 139 (FixedTape.rowsAux denominator ibox146 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox146) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_146
private noncomputable def tree145 : TapeTree := .centered (candidateRows ibox145) (candidateRows (FixedTape.midBox ibox145))
attribute [irreducible] tree145
private theorem sign_145 : 2*denominator*(computed denominator (FixedTape.midBox ibox145)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox145).gradient k).lo.natAbs ((computed denominator ibox145).gradient k).hi.natAbs : Int)*((ibox145 k).hi-(ibox145 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox145
    (computed denominator ibox145) (computed denominator (FixedTape.midBox ibox145))
    (by decide +kernel)
private theorem midpoint_even_145 : ∀ k, 2 ∣ (ibox145 k).lo+(ibox145 k).hi := by decide +kernel
private theorem accepted_145 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox145) tree145 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox145 midpoint_even_145
  simp only [tree145,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox145,candidate_valid h (FixedTape.midBox ibox145),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox145 139 (FixedTape.rowsAux denominator ibox145 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox145) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_145
private noncomputable def tree144 : TapeTree := .split 1 (((695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree145 tree146
attribute [irreducible] tree144
private theorem accepted_144 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox144) tree144 = true := by
  simp only [tree144,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox144 1 (695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) false,decode_split denominator ibox144 1 (695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_145 h,accepted_146 h⟩
private noncomputable def tree143 : TapeTree := .face 3 false (candidateRows ibox143) tree144
attribute [irreducible] tree143
private theorem sign_143 : ((computed denominator ibox143).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_143 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox143) tree143 = true := by
  simp only [tree143,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox143,?_,accepted_144 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox143)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox143).gradient 3).hi) denominator_positive).1 sign_143
private noncomputable def tree142 : TapeTree := .face 2 false (candidateRows ibox142) tree143
attribute [irreducible] tree142
private theorem sign_142 : ((computed denominator ibox142).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_142 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox142) tree142 = true := by
  simp only [tree142,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox142,?_,accepted_143 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox142)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox142).gradient 2).hi) denominator_positive).1 sign_142
private noncomputable def tree141 : TapeTree := .centered (candidateRows ibox141) (candidateRows (FixedTape.midBox ibox141))
attribute [irreducible] tree141
private theorem sign_141 : 2*denominator*(computed denominator (FixedTape.midBox ibox141)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox141).gradient k).lo.natAbs ((computed denominator ibox141).gradient k).hi.natAbs : Int)*((ibox141 k).hi-(ibox141 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox141
    (computed denominator ibox141) (computed denominator (FixedTape.midBox ibox141))
    (by decide +kernel)
private theorem midpoint_even_141 : ∀ k, 2 ∣ (ibox141 k).lo+(ibox141 k).hi := by decide +kernel
private theorem accepted_141 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox141) tree141 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox141 midpoint_even_141
  simp only [tree141,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox141,candidate_valid h (FixedTape.midBox ibox141),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox141 139 (FixedTape.rowsAux denominator ibox141 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox141) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_141
private noncomputable def tree140 : TapeTree := .centered (candidateRows ibox140) (candidateRows (FixedTape.midBox ibox140))
attribute [irreducible] tree140
private theorem sign_140 : 2*denominator*(computed denominator (FixedTape.midBox ibox140)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox140).gradient k).lo.natAbs ((computed denominator ibox140).gradient k).hi.natAbs : Int)*((ibox140 k).hi-(ibox140 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox140
    (computed denominator ibox140) (computed denominator (FixedTape.midBox ibox140))
    (by decide +kernel)
private theorem midpoint_even_140 : ∀ k, 2 ∣ (ibox140 k).lo+(ibox140 k).hi := by decide +kernel
private theorem accepted_140 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox140) tree140 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox140 midpoint_even_140
  simp only [tree140,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox140,candidate_valid h (FixedTape.midBox ibox140),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox140 139 (FixedTape.rowsAux denominator ibox140 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox140) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_140
private noncomputable def tree139 : TapeTree := .split 1 (((695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree140 tree141
attribute [irreducible] tree139
private theorem accepted_139 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox139) tree139 = true := by
  simp only [tree139,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox139 1 (695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) false,decode_split denominator ibox139 1 (695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_140 h,accepted_141 h⟩
private noncomputable def tree138 : TapeTree := .face 3 false (candidateRows ibox138) tree139
attribute [irreducible] tree138
private theorem sign_138 : ((computed denominator ibox138).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_138 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox138) tree138 = true := by
  simp only [tree138,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox138,?_,accepted_139 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox138)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox138).gradient 3).hi) denominator_positive).1 sign_138
private noncomputable def tree137 : TapeTree := .face 2 false (candidateRows ibox137) tree138
attribute [irreducible] tree137
private theorem sign_137 : ((computed denominator ibox137).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_137 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox137) tree137 = true := by
  simp only [tree137,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox137,?_,accepted_138 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox137)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox137).gradient 2).hi) denominator_positive).1 sign_137
private noncomputable def tree136 : TapeTree := .split 2 (((1304631767022283573803915834890391722755275460435358867208630775869501554004561410560893124608000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree137 tree142
attribute [irreducible] tree136
private theorem accepted_136 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox136) tree136 = true := by
  simp only [tree136,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox136 2 (1304631767022283573803915834890391722755275460435358867208630775869501554004561410560893124608000000000000000000000000 : Int) false,decode_split denominator ibox136 2 (1304631767022283573803915834890391722755275460435358867208630775869501554004561410560893124608000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_137 h,accepted_142 h⟩
private noncomputable def tree135 : TapeTree := .centered (candidateRows ibox135) (candidateRows (FixedTape.midBox ibox135))
attribute [irreducible] tree135
private theorem sign_135 : 2*denominator*(computed denominator (FixedTape.midBox ibox135)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox135).gradient k).lo.natAbs ((computed denominator ibox135).gradient k).hi.natAbs : Int)*((ibox135 k).hi-(ibox135 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox135
    (computed denominator ibox135) (computed denominator (FixedTape.midBox ibox135))
    (by decide +kernel)
private theorem midpoint_even_135 : ∀ k, 2 ∣ (ibox135 k).lo+(ibox135 k).hi := by decide +kernel
private theorem accepted_135 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox135) tree135 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox135 midpoint_even_135
  simp only [tree135,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox135,candidate_valid h (FixedTape.midBox ibox135),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox135 139 (FixedTape.rowsAux denominator ibox135 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox135) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_135
private noncomputable def tree134 : TapeTree := .centered (candidateRows ibox134) (candidateRows (FixedTape.midBox ibox134))
attribute [irreducible] tree134
private theorem sign_134 : 2*denominator*(computed denominator (FixedTape.midBox ibox134)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox134).gradient k).lo.natAbs ((computed denominator ibox134).gradient k).hi.natAbs : Int)*((ibox134 k).hi-(ibox134 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox134
    (computed denominator ibox134) (computed denominator (FixedTape.midBox ibox134))
    (by decide +kernel)
private theorem midpoint_even_134 : ∀ k, 2 ∣ (ibox134 k).lo+(ibox134 k).hi := by decide +kernel
private theorem accepted_134 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox134) tree134 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox134 midpoint_even_134
  simp only [tree134,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox134,candidate_valid h (FixedTape.midBox ibox134),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox134 139 (FixedTape.rowsAux denominator ibox134 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox134) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_134
private noncomputable def tree133 : TapeTree := .split 1 (((695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree134 tree135
attribute [irreducible] tree133
private theorem accepted_133 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox133) tree133 = true := by
  simp only [tree133,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox133 1 (695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) false,decode_split denominator ibox133 1 (695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_134 h,accepted_135 h⟩
private noncomputable def tree132 : TapeTree := .face 2 false (candidateRows ibox132) tree133
attribute [irreducible] tree132
private theorem sign_132 : ((computed denominator ibox132).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_132 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox132) tree132 = true := by
  simp only [tree132,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox132,?_,accepted_133 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox132)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox132).gradient 2).hi) denominator_positive).1 sign_132
private noncomputable def tree131 : TapeTree := .centered (candidateRows ibox131) (candidateRows (FixedTape.midBox ibox131))
attribute [irreducible] tree131
private theorem sign_131 : 2*denominator*(computed denominator (FixedTape.midBox ibox131)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox131).gradient k).lo.natAbs ((computed denominator ibox131).gradient k).hi.natAbs : Int)*((ibox131 k).hi-(ibox131 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox131
    (computed denominator ibox131) (computed denominator (FixedTape.midBox ibox131))
    (by decide +kernel)
private theorem midpoint_even_131 : ∀ k, 2 ∣ (ibox131 k).lo+(ibox131 k).hi := by decide +kernel
private theorem accepted_131 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox131) tree131 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox131 midpoint_even_131
  simp only [tree131,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox131,candidate_valid h (FixedTape.midBox ibox131),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox131 139 (FixedTape.rowsAux denominator ibox131 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox131) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_131
private noncomputable def tree130 : TapeTree := .face 2 false (candidateRows ibox130) tree131
attribute [irreducible] tree130
private theorem sign_130 : ((computed denominator ibox130).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_130 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox130) tree130 = true := by
  simp only [tree130,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox130,?_,accepted_131 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox130)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox130).gradient 2).hi) denominator_positive).1 sign_130
private noncomputable def tree129 : TapeTree := .centered (candidateRows ibox129) (candidateRows (FixedTape.midBox ibox129))
attribute [irreducible] tree129
private theorem sign_129 : 2*denominator*(computed denominator (FixedTape.midBox ibox129)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox129).gradient k).lo.natAbs ((computed denominator ibox129).gradient k).hi.natAbs : Int)*((ibox129 k).hi-(ibox129 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox129
    (computed denominator ibox129) (computed denominator (FixedTape.midBox ibox129))
    (by decide +kernel)
private theorem midpoint_even_129 : ∀ k, 2 ∣ (ibox129 k).lo+(ibox129 k).hi := by decide +kernel
private theorem accepted_129 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox129) tree129 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox129 midpoint_even_129
  simp only [tree129,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox129,candidate_valid h (FixedTape.midBox ibox129),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox129 139 (FixedTape.rowsAux denominator ibox129 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox129) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_129
private noncomputable def tree128 : TapeTree := .centered (candidateRows ibox128) (candidateRows (FixedTape.midBox ibox128))
attribute [irreducible] tree128
private theorem sign_128 : 2*denominator*(computed denominator (FixedTape.midBox ibox128)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox128).gradient k).lo.natAbs ((computed denominator ibox128).gradient k).hi.natAbs : Int)*((ibox128 k).hi-(ibox128 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox128
    (computed denominator ibox128) (computed denominator (FixedTape.midBox ibox128))
    (by decide +kernel)
private theorem midpoint_even_128 : ∀ k, 2 ∣ (ibox128 k).lo+(ibox128 k).hi := by decide +kernel
private theorem accepted_128 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox128) tree128 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox128 midpoint_even_128
  simp only [tree128,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox128,candidate_valid h (FixedTape.midBox ibox128),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox128 139 (FixedTape.rowsAux denominator ibox128 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox128) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_128
private noncomputable def tree127 : TapeTree := .face 2 false (candidateRows ibox127) tree128
attribute [irreducible] tree127
private theorem sign_127 : ((computed denominator ibox127).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_127 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox127) tree127 = true := by
  simp only [tree127,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox127,?_,accepted_128 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox127)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox127).gradient 2).hi) denominator_positive).1 sign_127
private noncomputable def tree126 : TapeTree := .split 2 (((1087193139185236311503263195741993102296062883696132389340525646557917961670467842134077603840000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree127 tree129
attribute [irreducible] tree126
private theorem accepted_126 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox126) tree126 = true := by
  simp only [tree126,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox126 2 (1087193139185236311503263195741993102296062883696132389340525646557917961670467842134077603840000000000000000000000000 : Int) false,decode_split denominator ibox126 2 (1087193139185236311503263195741993102296062883696132389340525646557917961670467842134077603840000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_127 h,accepted_129 h⟩
private noncomputable def tree125 : TapeTree := .split 1 (((695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree126 tree130
attribute [irreducible] tree125
private theorem accepted_125 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox125) tree125 = true := by
  simp only [tree125,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox125 1 (695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) false,decode_split denominator ibox125 1 (695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_126 h,accepted_130 h⟩
private noncomputable def tree124 : TapeTree := .split 2 (((1130680864752645763963393723571672826387905399043977684914146672420234680137286555819440707993600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree125 tree132
attribute [irreducible] tree124
private theorem accepted_124 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox124) tree124 = true := by
  simp only [tree124,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox124 2 (1130680864752645763963393723571672826387905399043977684914146672420234680137286555819440707993600000000000000000000000 : Int) false,decode_split denominator ibox124 2 (1130680864752645763963393723571672826387905399043977684914146672420234680137286555819440707993600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_125 h,accepted_132 h⟩
private noncomputable def tree123 : TapeTree := .face 3 false (candidateRows ibox123) tree124
attribute [irreducible] tree123
private theorem sign_123 : ((computed denominator ibox123).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_123 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox123) tree123 = true := by
  simp only [tree123,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox123,?_,accepted_124 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox123)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox123).gradient 3).hi) denominator_positive).1 sign_123
private noncomputable def tree122 : TapeTree := .split 2 (((1217656315887464668883654779231032274571590429739668276061388724144868117070923983190166916300800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree123 tree136
attribute [irreducible] tree122
private theorem accepted_122 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox122) tree122 = true := by
  simp only [tree122,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox122 2 (1217656315887464668883654779231032274571590429739668276061388724144868117070923983190166916300800000000000000000000000 : Int) false,decode_split denominator ibox122 2 (1217656315887464668883654779231032274571590429739668276061388724144868117070923983190166916300800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_123 h,accepted_136 h⟩
private noncomputable def tree121 : TapeTree := .centered (candidateRows ibox121) (candidateRows (FixedTape.midBox ibox121))
attribute [irreducible] tree121
private theorem sign_121 : 2*denominator*(computed denominator (FixedTape.midBox ibox121)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox121).gradient k).lo.natAbs ((computed denominator ibox121).gradient k).hi.natAbs : Int)*((ibox121 k).hi-(ibox121 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox121
    (computed denominator ibox121) (computed denominator (FixedTape.midBox ibox121))
    (by decide +kernel)
private theorem midpoint_even_121 : ∀ k, 2 ∣ (ibox121 k).lo+(ibox121 k).hi := by decide +kernel
private theorem accepted_121 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox121) tree121 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox121 midpoint_even_121
  simp only [tree121,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox121,candidate_valid h (FixedTape.midBox ibox121),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox121 139 (FixedTape.rowsAux denominator ibox121 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox121) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_121
private noncomputable def tree120 : TapeTree := .centered (candidateRows ibox120) (candidateRows (FixedTape.midBox ibox120))
attribute [irreducible] tree120
private theorem sign_120 : 2*denominator*(computed denominator (FixedTape.midBox ibox120)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox120).gradient k).lo.natAbs ((computed denominator ibox120).gradient k).hi.natAbs : Int)*((ibox120 k).hi-(ibox120 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox120
    (computed denominator ibox120) (computed denominator (FixedTape.midBox ibox120))
    (by decide +kernel)
private theorem midpoint_even_120 : ∀ k, 2 ∣ (ibox120 k).lo+(ibox120 k).hi := by decide +kernel
private theorem accepted_120 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox120) tree120 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox120 midpoint_even_120
  simp only [tree120,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox120,candidate_valid h (FixedTape.midBox ibox120),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox120 139 (FixedTape.rowsAux denominator ibox120 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox120) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_120
private noncomputable def tree119 : TapeTree := .split 1 (((1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree120 tree121
attribute [irreducible] tree119
private theorem accepted_119 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox119) tree119 = true := by
  simp only [tree119,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox119 1 (1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 : Int) false,decode_split denominator ibox119 1 (1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_120 h,accepted_121 h⟩
private noncomputable def tree118 : TapeTree := .centered (candidateRows ibox118) (candidateRows (FixedTape.midBox ibox118))
attribute [irreducible] tree118
private theorem sign_118 : 2*denominator*(computed denominator (FixedTape.midBox ibox118)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox118).gradient k).lo.natAbs ((computed denominator ibox118).gradient k).hi.natAbs : Int)*((ibox118 k).hi-(ibox118 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox118
    (computed denominator ibox118) (computed denominator (FixedTape.midBox ibox118))
    (by decide +kernel)
private theorem midpoint_even_118 : ∀ k, 2 ∣ (ibox118 k).lo+(ibox118 k).hi := by decide +kernel
private theorem accepted_118 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox118) tree118 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox118 midpoint_even_118
  simp only [tree118,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox118,candidate_valid h (FixedTape.midBox ibox118),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox118 139 (FixedTape.rowsAux denominator ibox118 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox118) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_118
private noncomputable def tree117 : TapeTree := .centered (candidateRows ibox117) (candidateRows (FixedTape.midBox ibox117))
attribute [irreducible] tree117
private theorem sign_117 : 2*denominator*(computed denominator (FixedTape.midBox ibox117)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox117).gradient k).lo.natAbs ((computed denominator ibox117).gradient k).hi.natAbs : Int)*((ibox117 k).hi-(ibox117 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox117
    (computed denominator ibox117) (computed denominator (FixedTape.midBox ibox117))
    (by decide +kernel)
private theorem midpoint_even_117 : ∀ k, 2 ∣ (ibox117 k).lo+(ibox117 k).hi := by decide +kernel
private theorem accepted_117 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox117) tree117 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox117 midpoint_even_117
  simp only [tree117,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox117,candidate_valid h (FixedTape.midBox ibox117),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox117 139 (FixedTape.rowsAux denominator ibox117 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox117) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_117
private noncomputable def tree116 : TapeTree := .split 1 (((1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree117 tree118
attribute [irreducible] tree116
private theorem accepted_116 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox116) tree116 = true := by
  simp only [tree116,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox116 1 (1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 : Int) false,decode_split denominator ibox116 1 (1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_117 h,accepted_118 h⟩
private noncomputable def tree115 : TapeTree := .split 2 (((956729962483007954122871612252953930020535337652596502619662568970967806270011701077988291379200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree116 tree119
attribute [irreducible] tree115
private theorem accepted_115 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox115) tree115 = true := by
  simp only [tree115,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox115 2 (956729962483007954122871612252953930020535337652596502619662568970967806270011701077988291379200000000000000000000000 : Int) false,decode_split denominator ibox115 2 (956729962483007954122871612252953930020535337652596502619662568970967806270011701077988291379200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_116 h,accepted_119 h⟩
private noncomputable def tree114 : TapeTree := .centered (candidateRows ibox114) (candidateRows (FixedTape.midBox ibox114))
attribute [irreducible] tree114
private theorem sign_114 : 2*denominator*(computed denominator (FixedTape.midBox ibox114)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox114).gradient k).lo.natAbs ((computed denominator ibox114).gradient k).hi.natAbs : Int)*((ibox114 k).hi-(ibox114 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox114
    (computed denominator ibox114) (computed denominator (FixedTape.midBox ibox114))
    (by decide +kernel)
private theorem midpoint_even_114 : ∀ k, 2 ∣ (ibox114 k).lo+(ibox114 k).hi := by decide +kernel
private theorem accepted_114 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox114) tree114 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox114 midpoint_even_114
  simp only [tree114,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox114,candidate_valid h (FixedTape.midBox ibox114),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox114 139 (FixedTape.rowsAux denominator ibox114 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox114) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_114
private noncomputable def tree113 : TapeTree := .centered (candidateRows ibox113) (candidateRows (FixedTape.midBox ibox113))
attribute [irreducible] tree113
private theorem sign_113 : 2*denominator*(computed denominator (FixedTape.midBox ibox113)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox113).gradient k).lo.natAbs ((computed denominator ibox113).gradient k).hi.natAbs : Int)*((ibox113 k).hi-(ibox113 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox113
    (computed denominator ibox113) (computed denominator (FixedTape.midBox ibox113))
    (by decide +kernel)
private theorem midpoint_even_113 : ∀ k, 2 ∣ (ibox113 k).lo+(ibox113 k).hi := by decide +kernel
private theorem accepted_113 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox113) tree113 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox113 midpoint_even_113
  simp only [tree113,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox113,candidate_valid h (FixedTape.midBox ibox113),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox113 139 (FixedTape.rowsAux denominator ibox113 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox113) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_113
private noncomputable def tree112 : TapeTree := .split 2 (((1000217688050417406583002140082633654112377853000441798193283594833284524736830414763351395532800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree113 tree114
attribute [irreducible] tree112
private theorem accepted_112 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox112) tree112 = true := by
  simp only [tree112,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox112 2 (1000217688050417406583002140082633654112377853000441798193283594833284524736830414763351395532800000000000000000000000 : Int) false,decode_split denominator ibox112 2 (1000217688050417406583002140082633654112377853000441798193283594833284524736830414763351395532800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_113 h,accepted_114 h⟩
private noncomputable def tree111 : TapeTree := .centered (candidateRows ibox111) (candidateRows (FixedTape.midBox ibox111))
attribute [irreducible] tree111
private theorem sign_111 : 2*denominator*(computed denominator (FixedTape.midBox ibox111)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox111).gradient k).lo.natAbs ((computed denominator ibox111).gradient k).hi.natAbs : Int)*((ibox111 k).hi-(ibox111 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox111
    (computed denominator ibox111) (computed denominator (FixedTape.midBox ibox111))
    (by decide +kernel)
private theorem midpoint_even_111 : ∀ k, 2 ∣ (ibox111 k).lo+(ibox111 k).hi := by decide +kernel
private theorem accepted_111 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox111) tree111 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox111 midpoint_even_111
  simp only [tree111,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox111,candidate_valid h (FixedTape.midBox ibox111),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox111 139 (FixedTape.rowsAux denominator ibox111 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox111) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_111
private noncomputable def tree110 : TapeTree := .centered (candidateRows ibox110) (candidateRows (FixedTape.midBox ibox110))
attribute [irreducible] tree110
private theorem sign_110 : 2*denominator*(computed denominator (FixedTape.midBox ibox110)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox110).gradient k).lo.natAbs ((computed denominator ibox110).gradient k).hi.natAbs : Int)*((ibox110 k).hi-(ibox110 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox110
    (computed denominator ibox110) (computed denominator (FixedTape.midBox ibox110))
    (by decide +kernel)
private theorem midpoint_even_110 : ∀ k, 2 ∣ (ibox110 k).lo+(ibox110 k).hi := by decide +kernel
private theorem accepted_110 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox110) tree110 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox110 midpoint_even_110
  simp only [tree110,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox110,candidate_valid h (FixedTape.midBox ibox110),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox110 139 (FixedTape.rowsAux denominator ibox110 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox110) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_110
private noncomputable def tree109 : TapeTree := .split 2 (((1000217688050417406583002140082633654112377853000441798193283594833284524736830414763351395532800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree110 tree111
attribute [irreducible] tree109
private theorem accepted_109 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox109) tree109 = true := by
  simp only [tree109,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox109 2 (1000217688050417406583002140082633654112377853000441798193283594833284524736830414763351395532800000000000000000000000 : Int) false,decode_split denominator ibox109 2 (1000217688050417406583002140082633654112377853000441798193283594833284524736830414763351395532800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_110 h,accepted_111 h⟩
private noncomputable def tree108 : TapeTree := .split 1 (((347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree109 tree112
attribute [irreducible] tree108
private theorem accepted_108 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox108) tree108 = true := by
  simp only [tree108,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox108 1 (347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 : Int) false,decode_split denominator ibox108 1 (347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_109 h,accepted_112 h⟩
private noncomputable def tree107 : TapeTree := .centered (candidateRows ibox107) (candidateRows (FixedTape.midBox ibox107))
attribute [irreducible] tree107
private theorem sign_107 : 2*denominator*(computed denominator (FixedTape.midBox ibox107)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox107).gradient k).lo.natAbs ((computed denominator ibox107).gradient k).hi.natAbs : Int)*((ibox107 k).hi-(ibox107 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox107
    (computed denominator ibox107) (computed denominator (FixedTape.midBox ibox107))
    (by decide +kernel)
private theorem midpoint_even_107 : ∀ k, 2 ∣ (ibox107 k).lo+(ibox107 k).hi := by decide +kernel
private theorem accepted_107 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox107) tree107 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox107 midpoint_even_107
  simp only [tree107,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox107,candidate_valid h (FixedTape.midBox ibox107),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox107 139 (FixedTape.rowsAux denominator ibox107 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox107) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_107
private noncomputable def tree106 : TapeTree := .centered (candidateRows ibox106) (candidateRows (FixedTape.midBox ibox106))
attribute [irreducible] tree106
private theorem sign_106 : 2*denominator*(computed denominator (FixedTape.midBox ibox106)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox106).gradient k).lo.natAbs ((computed denominator ibox106).gradient k).hi.natAbs : Int)*((ibox106 k).hi-(ibox106 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox106
    (computed denominator ibox106) (computed denominator (FixedTape.midBox ibox106))
    (by decide +kernel)
private theorem midpoint_even_106 : ∀ k, 2 ∣ (ibox106 k).lo+(ibox106 k).hi := by decide +kernel
private theorem accepted_106 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox106) tree106 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox106 midpoint_even_106
  simp only [tree106,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox106,candidate_valid h (FixedTape.midBox ibox106),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox106 139 (FixedTape.rowsAux denominator ibox106 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox106) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_106
private noncomputable def tree105 : TapeTree := .centered (candidateRows ibox105) (candidateRows (FixedTape.midBox ibox105))
attribute [irreducible] tree105
private theorem sign_105 : 2*denominator*(computed denominator (FixedTape.midBox ibox105)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox105).gradient k).lo.natAbs ((computed denominator ibox105).gradient k).hi.natAbs : Int)*((ibox105 k).hi-(ibox105 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox105
    (computed denominator ibox105) (computed denominator (FixedTape.midBox ibox105))
    (by decide +kernel)
private theorem midpoint_even_105 : ∀ k, 2 ∣ (ibox105 k).lo+(ibox105 k).hi := by decide +kernel
private theorem accepted_105 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox105) tree105 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox105 midpoint_even_105
  simp only [tree105,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox105,candidate_valid h (FixedTape.midBox ibox105),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox105 139 (FixedTape.rowsAux denominator ibox105 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox105) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_105
private noncomputable def tree104 : TapeTree := .split 2 (((913242236915598501662741084423274205928692822304751207046041543108651087803192987392625187225600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree105 tree106
attribute [irreducible] tree104
private theorem accepted_104 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox104) tree104 = true := by
  simp only [tree104,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox104 2 (913242236915598501662741084423274205928692822304751207046041543108651087803192987392625187225600000000000000000000000 : Int) false,decode_split denominator ibox104 2 (913242236915598501662741084423274205928692822304751207046041543108651087803192987392625187225600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_105 h,accepted_106 h⟩
private noncomputable def tree103 : TapeTree := .split 1 (((347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree104 tree107
attribute [irreducible] tree103
private theorem accepted_103 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox103) tree103 = true := by
  simp only [tree103,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox103 1 (347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 : Int) false,decode_split denominator ibox103 1 (347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_104 h,accepted_107 h⟩
private noncomputable def tree102 : TapeTree := .split 2 (((956729962483007954122871612252953930020535337652596502619662568970967806270011701077988291379200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree103 tree108
attribute [irreducible] tree102
private theorem accepted_102 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox102) tree102 = true := by
  simp only [tree102,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox102 2 (956729962483007954122871612252953930020535337652596502619662568970967806270011701077988291379200000000000000000000000 : Int) false,decode_split denominator ibox102 2 (956729962483007954122871612252953930020535337652596502619662568970967806270011701077988291379200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_103 h,accepted_108 h⟩
private noncomputable def tree101 : TapeTree := .split 1 (((695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree102 tree115
attribute [irreducible] tree101
private theorem accepted_101 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox101) tree101 = true := by
  simp only [tree101,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox101 1 (695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) false,decode_split denominator ibox101 1 (695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_102 h,accepted_115 h⟩
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
private noncomputable def tree98 : TapeTree := .split 2 (((782779060213370144282349500934235033653165276261215320325178465521700932402736846336535874764800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree99 tree100
attribute [irreducible] tree98
private theorem accepted_98 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox98) tree98 = true := by
  simp only [tree98,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox98 2 (782779060213370144282349500934235033653165276261215320325178465521700932402736846336535874764800000000000000000000000 : Int) false,decode_split denominator ibox98 2 (782779060213370144282349500934235033653165276261215320325178465521700932402736846336535874764800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_99 h,accepted_100 h⟩
private noncomputable def tree97 : TapeTree := .centered (candidateRows ibox97) (candidateRows (FixedTape.midBox ibox97))
attribute [irreducible] tree97
private theorem sign_97 : 2*denominator*(computed denominator (FixedTape.midBox ibox97)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox97).gradient k).lo.natAbs ((computed denominator ibox97).gradient k).hi.natAbs : Int)*((ibox97 k).hi-(ibox97 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox97
    (computed denominator ibox97) (computed denominator (FixedTape.midBox ibox97))
    (by decide +kernel)
private theorem midpoint_even_97 : ∀ k, 2 ∣ (ibox97 k).lo+(ibox97 k).hi := by decide +kernel
private theorem accepted_97 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox97) tree97 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox97 midpoint_even_97
  simp only [tree97,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox97,candidate_valid h (FixedTape.midBox ibox97),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox97 139 (FixedTape.rowsAux denominator ibox97 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox97) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_97
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
private noncomputable def tree95 : TapeTree := .split 2 (((782779060213370144282349500934235033653165276261215320325178465521700932402736846336535874764800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree96 tree97
attribute [irreducible] tree95
private theorem accepted_95 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox95) tree95 = true := by
  simp only [tree95,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox95 2 (782779060213370144282349500934235033653165276261215320325178465521700932402736846336535874764800000000000000000000000 : Int) false,decode_split denominator ibox95 2 (782779060213370144282349500934235033653165276261215320325178465521700932402736846336535874764800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_96 h,accepted_97 h⟩
private noncomputable def tree94 : TapeTree := .split 1 (((1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree95 tree98
attribute [irreducible] tree94
private theorem accepted_94 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox94) tree94 = true := by
  simp only [tree94,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox94 1 (1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 : Int) false,decode_split denominator ibox94 1 (1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_95 h,accepted_98 h⟩
private noncomputable def tree93 : TapeTree := .centered (candidateRows ibox93) (candidateRows (FixedTape.midBox ibox93))
attribute [irreducible] tree93
private theorem sign_93 : 2*denominator*(computed denominator (FixedTape.midBox ibox93)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox93).gradient k).lo.natAbs ((computed denominator ibox93).gradient k).hi.natAbs : Int)*((ibox93 k).hi-(ibox93 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox93
    (computed denominator ibox93) (computed denominator (FixedTape.midBox ibox93))
    (by decide +kernel)
private theorem midpoint_even_93 : ∀ k, 2 ∣ (ibox93 k).lo+(ibox93 k).hi := by decide +kernel
private theorem accepted_93 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox93) tree93 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox93 midpoint_even_93
  simp only [tree93,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox93,candidate_valid h (FixedTape.midBox ibox93),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox93 139 (FixedTape.rowsAux denominator ibox93 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox93) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_93
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
private noncomputable def tree91 : TapeTree := .split 2 (((782779060213370144282349500934235033653165276261215320325178465521700932402736846336535874764800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree92 tree93
attribute [irreducible] tree91
private theorem accepted_91 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox91) tree91 = true := by
  simp only [tree91,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox91 2 (782779060213370144282349500934235033653165276261215320325178465521700932402736846336535874764800000000000000000000000 : Int) false,decode_split denominator ibox91 2 (782779060213370144282349500934235033653165276261215320325178465521700932402736846336535874764800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_92 h,accepted_93 h⟩
private noncomputable def tree90 : TapeTree := .centered (candidateRows ibox90) (candidateRows (FixedTape.midBox ibox90))
attribute [irreducible] tree90
private theorem sign_90 : 2*denominator*(computed denominator (FixedTape.midBox ibox90)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox90).gradient k).lo.natAbs ((computed denominator ibox90).gradient k).hi.natAbs : Int)*((ibox90 k).hi-(ibox90 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox90
    (computed denominator ibox90) (computed denominator (FixedTape.midBox ibox90))
    (by decide +kernel)
private theorem midpoint_even_90 : ∀ k, 2 ∣ (ibox90 k).lo+(ibox90 k).hi := by decide +kernel
private theorem accepted_90 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox90) tree90 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox90 midpoint_even_90
  simp only [tree90,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox90,candidate_valid h (FixedTape.midBox ibox90),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox90 139 (FixedTape.rowsAux denominator ibox90 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox90) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_90
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
private noncomputable def tree88 : TapeTree := .split 2 (((782779060213370144282349500934235033653165276261215320325178465521700932402736846336535874764800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree89 tree90
attribute [irreducible] tree88
private theorem accepted_88 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox88) tree88 = true := by
  simp only [tree88,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox88 2 (782779060213370144282349500934235033653165276261215320325178465521700932402736846336535874764800000000000000000000000 : Int) false,decode_split denominator ibox88 2 (782779060213370144282349500934235033653165276261215320325178465521700932402736846336535874764800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_89 h,accepted_90 h⟩
private noncomputable def tree87 : TapeTree := .split 1 (((347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree88 tree91
attribute [irreducible] tree87
private theorem accepted_87 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox87) tree87 = true := by
  simp only [tree87,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox87 1 (347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 : Int) false,decode_split denominator ibox87 1 (347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_88 h,accepted_91 h⟩
private noncomputable def tree86 : TapeTree := .split 1 (((695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree87 tree94
attribute [irreducible] tree86
private theorem accepted_86 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox86) tree86 = true := by
  simp only [tree86,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox86 1 (695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) false,decode_split denominator ibox86 1 (695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_87 h,accepted_94 h⟩
private noncomputable def tree85 : TapeTree := .split 2 (((869754511348189049202610556593594481836850306956905911472420517246334369336374273707262083072000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree86 tree101
attribute [irreducible] tree85
private theorem accepted_85 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox85) tree85 = true := by
  simp only [tree85,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox85 2 (869754511348189049202610556593594481836850306956905911472420517246334369336374273707262083072000000000000000000000000 : Int) false,decode_split denominator ibox85 2 (869754511348189049202610556593594481836850306956905911472420517246334369336374273707262083072000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_86 h,accepted_101 h⟩
private noncomputable def tree84 : TapeTree := .face 3 false (candidateRows ibox84) tree85
attribute [irreducible] tree84
private theorem sign_84 : ((computed denominator ibox84).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_84 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox84) tree84 = true := by
  simp only [tree84,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox84,?_,accepted_85 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox84)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox84).gradient 3).hi) denominator_positive).1 sign_84
private noncomputable def tree83 : TapeTree := .split 2 (((1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree84 tree122
attribute [irreducible] tree83
private theorem accepted_83 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox83) tree83 = true := by
  simp only [tree83,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox83 2 (1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 : Int) false,decode_split denominator ibox83 2 (1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_84 h,accepted_122 h⟩
private noncomputable def tree82 : TapeTree := .centered (candidateRows ibox82) (candidateRows (FixedTape.midBox ibox82))
attribute [irreducible] tree82
private theorem sign_82 : 2*denominator*(computed denominator (FixedTape.midBox ibox82)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox82).gradient k).lo.natAbs ((computed denominator ibox82).gradient k).hi.natAbs : Int)*((ibox82 k).hi-(ibox82 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox82
    (computed denominator ibox82) (computed denominator (FixedTape.midBox ibox82))
    (by decide +kernel)
private theorem midpoint_even_82 : ∀ k, 2 ∣ (ibox82 k).lo+(ibox82 k).hi := by decide +kernel
private theorem accepted_82 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox82) tree82 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox82 midpoint_even_82
  simp only [tree82,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox82,candidate_valid h (FixedTape.midBox ibox82),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox82 139 (FixedTape.rowsAux denominator ibox82 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox82) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_82
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
private noncomputable def tree80 : TapeTree := .split 0 (((949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 : Int) : ℚ)/(denominator : ℚ)) tree81 tree82
attribute [irreducible] tree80
private theorem accepted_80 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox80) tree80 = true := by
  simp only [tree80,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox80 0 (949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 : Int) false,decode_split denominator ibox80 0 (949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_81 h,accepted_82 h⟩
private noncomputable def tree79 : TapeTree := .centered (candidateRows ibox79) (candidateRows (FixedTape.midBox ibox79))
attribute [irreducible] tree79
private theorem sign_79 : 2*denominator*(computed denominator (FixedTape.midBox ibox79)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox79).gradient k).lo.natAbs ((computed denominator ibox79).gradient k).hi.natAbs : Int)*((ibox79 k).hi-(ibox79 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox79
    (computed denominator ibox79) (computed denominator (FixedTape.midBox ibox79))
    (by decide +kernel)
private theorem midpoint_even_79 : ∀ k, 2 ∣ (ibox79 k).lo+(ibox79 k).hi := by decide +kernel
private theorem accepted_79 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox79) tree79 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox79 midpoint_even_79
  simp only [tree79,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox79,candidate_valid h (FixedTape.midBox ibox79),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox79 139 (FixedTape.rowsAux denominator ibox79 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox79) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_79
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
private noncomputable def tree77 : TapeTree := .split 1 (((1217656315887464668883654779231032274571590429739668276061388724144868117070923983190166916300800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree78 tree79
attribute [irreducible] tree77
private theorem accepted_77 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox77) tree77 = true := by
  simp only [tree77,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox77 1 (1217656315887464668883654779231032274571590429739668276061388724144868117070923983190166916300800000000000000000000000 : Int) false,decode_split denominator ibox77 1 (1217656315887464668883654779231032274571590429739668276061388724144868117070923983190166916300800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_78 h,accepted_79 h⟩
private noncomputable def tree76 : TapeTree := .split 2 (((608828157943732334441827389615516137285795214869834138030694362072434058535461991595083458150400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree77 tree80
attribute [irreducible] tree76
private theorem accepted_76 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox76) tree76 = true := by
  simp only [tree76,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox76 2 (608828157943732334441827389615516137285795214869834138030694362072434058535461991595083458150400000000000000000000000 : Int) false,decode_split denominator ibox76 2 (608828157943732334441827389615516137285795214869834138030694362072434058535461991595083458150400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_77 h,accepted_80 h⟩
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
private noncomputable def tree74 : TapeTree := .centered (candidateRows ibox74) (candidateRows (FixedTape.midBox ibox74))
attribute [irreducible] tree74
private theorem sign_74 : 2*denominator*(computed denominator (FixedTape.midBox ibox74)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox74).gradient k).lo.natAbs ((computed denominator ibox74).gradient k).hi.natAbs : Int)*((ibox74 k).hi-(ibox74 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox74
    (computed denominator ibox74) (computed denominator (FixedTape.midBox ibox74))
    (by decide +kernel)
private theorem midpoint_even_74 : ∀ k, 2 ∣ (ibox74 k).lo+(ibox74 k).hi := by decide +kernel
private theorem accepted_74 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox74) tree74 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox74 midpoint_even_74
  simp only [tree74,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox74,candidate_valid h (FixedTape.midBox ibox74),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox74 139 (FixedTape.rowsAux denominator ibox74 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox74) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_74
private noncomputable def tree73 : TapeTree := .split 0 (((949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 : Int) : ℚ)/(denominator : ℚ)) tree74 tree75
attribute [irreducible] tree73
private theorem accepted_73 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox73) tree73 = true := by
  simp only [tree73,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox73 0 (949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 : Int) false,decode_split denominator ibox73 0 (949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_74 h,accepted_75 h⟩
private noncomputable def tree72 : TapeTree := .split 1 (((1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree73 tree76
attribute [irreducible] tree72
private theorem accepted_72 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox72) tree72 = true := by
  simp only [tree72,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox72 1 (1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 : Int) false,decode_split denominator ibox72 1 (1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_73 h,accepted_76 h⟩
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
private noncomputable def tree70 : TapeTree := .centered (candidateRows ibox70) (candidateRows (FixedTape.midBox ibox70))
attribute [irreducible] tree70
private theorem sign_70 : 2*denominator*(computed denominator (FixedTape.midBox ibox70)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox70).gradient k).lo.natAbs ((computed denominator ibox70).gradient k).hi.natAbs : Int)*((ibox70 k).hi-(ibox70 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox70
    (computed denominator ibox70) (computed denominator (FixedTape.midBox ibox70))
    (by decide +kernel)
private theorem midpoint_even_70 : ∀ k, 2 ∣ (ibox70 k).lo+(ibox70 k).hi := by decide +kernel
private theorem accepted_70 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox70) tree70 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox70 midpoint_even_70
  simp only [tree70,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox70,candidate_valid h (FixedTape.midBox ibox70),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox70 139 (FixedTape.rowsAux denominator ibox70 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox70) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_70
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
private noncomputable def tree68 : TapeTree := .split 0 (((949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 : Int) : ℚ)/(denominator : ℚ)) tree69 tree70
attribute [irreducible] tree68
private theorem accepted_68 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox68) tree68 = true := by
  simp only [tree68,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox68 0 (949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 : Int) false,decode_split denominator ibox68 0 (949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_69 h,accepted_70 h⟩
private noncomputable def tree67 : TapeTree := .split 2 (((434877255674094524601305278296797240918425153478452955736210258623167184668187136853631041536000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree68 tree71
attribute [irreducible] tree67
private theorem accepted_67 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox67) tree67 = true := by
  simp only [tree67,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox67 2 (434877255674094524601305278296797240918425153478452955736210258623167184668187136853631041536000000000000000000000000 : Int) false,decode_split denominator ibox67 2 (434877255674094524601305278296797240918425153478452955736210258623167184668187136853631041536000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_68 h,accepted_71 h⟩
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
private noncomputable def tree64 : TapeTree := .split 2 (((434877255674094524601305278296797240918425153478452955736210258623167184668187136853631041536000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree65 tree66
attribute [irreducible] tree64
private theorem accepted_64 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox64) tree64 = true := by
  simp only [tree64,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox64 2 (434877255674094524601305278296797240918425153478452955736210258623167184668187136853631041536000000000000000000000000 : Int) false,decode_split denominator ibox64 2 (434877255674094524601305278296797240918425153478452955736210258623167184668187136853631041536000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_65 h,accepted_66 h⟩
private noncomputable def tree63 : TapeTree := .split 1 (((1217656315887464668883654779231032274571590429739668276061388724144868117070923983190166916300800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree64 tree67
attribute [irreducible] tree63
private theorem accepted_63 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox63) tree63 = true := by
  simp only [tree63,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox63 1 (1217656315887464668883654779231032274571590429739668276061388724144868117070923983190166916300800000000000000000000000 : Int) false,decode_split denominator ibox63 1 (1217656315887464668883654779231032274571590429739668276061388724144868117070923983190166916300800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_64 h,accepted_67 h⟩
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
private noncomputable def tree61 : TapeTree := .centered (candidateRows ibox61) (candidateRows (FixedTape.midBox ibox61))
attribute [irreducible] tree61
private theorem sign_61 : 2*denominator*(computed denominator (FixedTape.midBox ibox61)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox61).gradient k).lo.natAbs ((computed denominator ibox61).gradient k).hi.natAbs : Int)*((ibox61 k).hi-(ibox61 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox61
    (computed denominator ibox61) (computed denominator (FixedTape.midBox ibox61))
    (by decide +kernel)
private theorem midpoint_even_61 : ∀ k, 2 ∣ (ibox61 k).lo+(ibox61 k).hi := by decide +kernel
private theorem accepted_61 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox61) tree61 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox61 midpoint_even_61
  simp only [tree61,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox61,candidate_valid h (FixedTape.midBox ibox61),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox61 139 (FixedTape.rowsAux denominator ibox61 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox61) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_61
private noncomputable def tree60 : TapeTree := .split 1 (((869754511348189049202610556593594481836850306956905911472420517246334369336374273707262083072000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree61 tree62
attribute [irreducible] tree60
private theorem accepted_60 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox60) tree60 = true := by
  simp only [tree60,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox60 1 (869754511348189049202610556593594481836850306956905911472420517246334369336374273707262083072000000000000000000000000 : Int) false,decode_split denominator ibox60 1 (869754511348189049202610556593594481836850306956905911472420517246334369336374273707262083072000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_61 h,accepted_62 h⟩
private noncomputable def tree59 : TapeTree := .split 1 (((1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree60 tree63
attribute [irreducible] tree59
private theorem accepted_59 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox59) tree59 = true := by
  simp only [tree59,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox59 1 (1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 : Int) false,decode_split denominator ibox59 1 (1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_60 h,accepted_63 h⟩
private noncomputable def tree58 : TapeTree := .split 2 (((521852706808913429521566333956156689102110184174143546883452310347800621601824564224357249843200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree59 tree72
attribute [irreducible] tree58
private theorem accepted_58 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox58) tree58 = true := by
  simp only [tree58,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox58 2 (521852706808913429521566333956156689102110184174143546883452310347800621601824564224357249843200000000000000000000000 : Int) false,decode_split denominator ibox58 2 (521852706808913429521566333956156689102110184174143546883452310347800621601824564224357249843200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_59 h,accepted_72 h⟩
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
private noncomputable def tree56 : TapeTree := .centered (candidateRows ibox56) (candidateRows (FixedTape.midBox ibox56))
attribute [irreducible] tree56
private theorem sign_56 : 2*denominator*(computed denominator (FixedTape.midBox ibox56)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox56).gradient k).lo.natAbs ((computed denominator ibox56).gradient k).hi.natAbs : Int)*((ibox56 k).hi-(ibox56 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox56
    (computed denominator ibox56) (computed denominator (FixedTape.midBox ibox56))
    (by decide +kernel)
private theorem midpoint_even_56 : ∀ k, 2 ∣ (ibox56 k).lo+(ibox56 k).hi := by decide +kernel
private theorem accepted_56 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox56) tree56 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox56 midpoint_even_56
  simp only [tree56,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox56,candidate_valid h (FixedTape.midBox ibox56),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox56 139 (FixedTape.rowsAux denominator ibox56 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox56) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_56
private noncomputable def tree55 : TapeTree := .split 0 (((949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 : Int) : ℚ)/(denominator : ℚ)) tree56 tree57
attribute [irreducible] tree55
private theorem accepted_55 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox55) tree55 = true := by
  simp only [tree55,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox55 0 (949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 : Int) false,decode_split denominator ibox55 0 (949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_56 h,accepted_57 h⟩
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
private noncomputable def tree53 : TapeTree := .split 1 (((347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree54 tree55
attribute [irreducible] tree53
private theorem accepted_53 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox53) tree53 = true := by
  simp only [tree53,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox53 1 (347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 : Int) false,decode_split denominator ibox53 1 (347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 : Int) true]
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
private noncomputable def tree50 : TapeTree := .split 1 (((347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree51 tree52
attribute [irreducible] tree50
private theorem accepted_50 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox50) tree50 = true := by
  simp only [tree50,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox50 1 (347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 : Int) false,decode_split denominator ibox50 1 (347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_51 h,accepted_52 h⟩
private noncomputable def tree49 : TapeTree := .split 2 (((521852706808913429521566333956156689102110184174143546883452310347800621601824564224357249843200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree50 tree53
attribute [irreducible] tree49
private theorem accepted_49 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox49) tree49 = true := by
  simp only [tree49,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox49 2 (521852706808913429521566333956156689102110184174143546883452310347800621601824564224357249843200000000000000000000000 : Int) false,decode_split denominator ibox49 2 (521852706808913429521566333956156689102110184174143546883452310347800621601824564224357249843200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_50 h,accepted_53 h⟩
private noncomputable def tree48 : TapeTree := .split 1 (((695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree49 tree58
attribute [irreducible] tree48
private theorem accepted_48 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox48) tree48 = true := by
  simp only [tree48,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox48 1 (695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) false,decode_split denominator ibox48 1 (695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_49 h,accepted_58 h⟩
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
private noncomputable def tree46 : TapeTree := .centered (candidateRows ibox46) (candidateRows (FixedTape.midBox ibox46))
attribute [irreducible] tree46
private theorem sign_46 : 2*denominator*(computed denominator (FixedTape.midBox ibox46)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox46).gradient k).lo.natAbs ((computed denominator ibox46).gradient k).hi.natAbs : Int)*((ibox46 k).hi-(ibox46 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox46
    (computed denominator ibox46) (computed denominator (FixedTape.midBox ibox46))
    (by decide +kernel)
private theorem midpoint_even_46 : ∀ k, 2 ∣ (ibox46 k).lo+(ibox46 k).hi := by decide +kernel
private theorem accepted_46 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox46) tree46 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox46 midpoint_even_46
  simp only [tree46,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox46,candidate_valid h (FixedTape.midBox ibox46),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox46 139 (FixedTape.rowsAux denominator ibox46 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox46) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_46
private noncomputable def tree45 : TapeTree := .split 0 (((949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 : Int) : ℚ)/(denominator : ℚ)) tree46 tree47
attribute [irreducible] tree45
private theorem accepted_45 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox45) tree45 = true := by
  simp only [tree45,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox45 0 (949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 : Int) false,decode_split denominator ibox45 0 (949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_46 h,accepted_47 h⟩
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
private noncomputable def tree42 : TapeTree := .split 0 (((949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 : Int) : ℚ)/(denominator : ℚ)) tree43 tree44
attribute [irreducible] tree42
private theorem accepted_42 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox42) tree42 = true := by
  simp only [tree42,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox42 0 (949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 : Int) false,decode_split denominator ibox42 0 (949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_43 h,accepted_44 h⟩
private noncomputable def tree41 : TapeTree := .centered (candidateRows ibox41) (candidateRows (FixedTape.midBox ibox41))
attribute [irreducible] tree41
private theorem sign_41 : 2*denominator*(computed denominator (FixedTape.midBox ibox41)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox41).gradient k).lo.natAbs ((computed denominator ibox41).gradient k).hi.natAbs : Int)*((ibox41 k).hi-(ibox41 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox41
    (computed denominator ibox41) (computed denominator (FixedTape.midBox ibox41))
    (by decide +kernel)
private theorem midpoint_even_41 : ∀ k, 2 ∣ (ibox41 k).lo+(ibox41 k).hi := by decide +kernel
private theorem accepted_41 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox41) tree41 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox41 midpoint_even_41
  simp only [tree41,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox41,candidate_valid h (FixedTape.midBox ibox41),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox41 139 (FixedTape.rowsAux denominator ibox41 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox41) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_41
private noncomputable def tree40 : TapeTree := .split 1 (((1304631767022283573803915834890391722755275460435358867208630775869501554004561410560893124608000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree41 tree42
attribute [irreducible] tree40
private theorem accepted_40 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox40) tree40 = true := by
  simp only [tree40,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox40 1 (1304631767022283573803915834890391722755275460435358867208630775869501554004561410560893124608000000000000000000000000 : Int) false,decode_split denominator ibox40 1 (1304631767022283573803915834890391722755275460435358867208630775869501554004561410560893124608000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_41 h,accepted_42 h⟩
private noncomputable def tree39 : TapeTree := .split 2 (((260926353404456714760783166978078344551055092087071773441726155173900310800912282112178624921600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree40 tree45
attribute [irreducible] tree39
private theorem accepted_39 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox39) tree39 = true := by
  simp only [tree39,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox39 2 (260926353404456714760783166978078344551055092087071773441726155173900310800912282112178624921600000000000000000000000 : Int) false,decode_split denominator ibox39 2 (260926353404456714760783166978078344551055092087071773441726155173900310800912282112178624921600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_40 h,accepted_45 h⟩
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
private noncomputable def tree37 : TapeTree := .centered (candidateRows ibox37) (candidateRows (FixedTape.midBox ibox37))
attribute [irreducible] tree37
private theorem sign_37 : 2*denominator*(computed denominator (FixedTape.midBox ibox37)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox37).gradient k).lo.natAbs ((computed denominator ibox37).gradient k).hi.natAbs : Int)*((ibox37 k).hi-(ibox37 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox37
    (computed denominator ibox37) (computed denominator (FixedTape.midBox ibox37))
    (by decide +kernel)
private theorem midpoint_even_37 : ∀ k, 2 ∣ (ibox37 k).lo+(ibox37 k).hi := by decide +kernel
private theorem accepted_37 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox37) tree37 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox37 midpoint_even_37
  simp only [tree37,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox37,candidate_valid h (FixedTape.midBox ibox37),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox37 139 (FixedTape.rowsAux denominator ibox37 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox37) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_37
private noncomputable def tree36 : TapeTree := .split 2 (((260926353404456714760783166978078344551055092087071773441726155173900310800912282112178624921600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree37 tree38
attribute [irreducible] tree36
private theorem accepted_36 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox36) tree36 = true := by
  simp only [tree36,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox36 2 (260926353404456714760783166978078344551055092087071773441726155173900310800912282112178624921600000000000000000000000 : Int) false,decode_split denominator ibox36 2 (260926353404456714760783166978078344551055092087071773441726155173900310800912282112178624921600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_37 h,accepted_38 h⟩
private noncomputable def tree35 : TapeTree := .split 1 (((1217656315887464668883654779231032274571590429739668276061388724144868117070923983190166916300800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree36 tree39
attribute [irreducible] tree35
private theorem accepted_35 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox35) tree35 = true := by
  simp only [tree35,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox35 1 (1217656315887464668883654779231032274571590429739668276061388724144868117070923983190166916300800000000000000000000000 : Int) false,decode_split denominator ibox35 1 (1217656315887464668883654779231032274571590429739668276061388724144868117070923983190166916300800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_36 h,accepted_39 h⟩
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
private noncomputable def tree32 : TapeTree := .split 2 (((130463176702228357380391583489039172275527546043535886720863077586950155400456141056089312460800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree33 tree34
attribute [irreducible] tree32
private theorem accepted_32 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox32) tree32 = true := by
  simp only [tree32,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox32 2 (130463176702228357380391583489039172275527546043535886720863077586950155400456141056089312460800000000000000000000000 : Int) false,decode_split denominator ibox32 2 (130463176702228357380391583489039172275527546043535886720863077586950155400456141056089312460800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_33 h,accepted_34 h⟩
private noncomputable def tree31 : TapeTree := .face 1 true (candidateRows ibox31) tree32
attribute [irreducible] tree31
private theorem sign_31 : 0 ≤ ((computed denominator ibox31).gradient 1).lo := by decide +kernel
private theorem accepted_31 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox31) tree31 = true := by
  simp only [tree31,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox31,?_,accepted_32 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox31)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox31).gradient 1).lo) denominator_positive).2 sign_31
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
private noncomputable def tree29 : TapeTree := .split 1 (((1304631767022283573803915834890391722755275460435358867208630775869501554004561410560893124608000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree30 tree31
attribute [irreducible] tree29
private theorem accepted_29 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox29) tree29 = true := by
  simp only [tree29,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox29 1 (1304631767022283573803915834890391722755275460435358867208630775869501554004561410560893124608000000000000000000000000 : Int) false,decode_split denominator ibox29 1 (1304631767022283573803915834890391722755275460435358867208630775869501554004561410560893124608000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_30 h,accepted_31 h⟩
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
private noncomputable def tree26 : TapeTree := .split 0 (((949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 : Int) : ℚ)/(denominator : ℚ)) tree27 tree28
attribute [irreducible] tree26
private theorem accepted_26 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox26) tree26 = true := by
  simp only [tree26,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox26 0 (949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 : Int) false,decode_split denominator ibox26 0 (949482008221773091766423796184756600144457936752994651322742102362230298387969501934927471960227931053977763840000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_27 h,accepted_28 h⟩
private noncomputable def tree25 : TapeTree := .face 1 true (candidateRows ibox25) tree26
attribute [irreducible] tree25
private theorem sign_25 : 0 ≤ ((computed denominator ibox25).gradient 1).lo := by decide +kernel
private theorem accepted_25 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox25) tree25 = true := by
  simp only [tree25,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox25,?_,accepted_26 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox25)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox25).gradient 1).lo) denominator_positive).2 sign_25
private noncomputable def tree24 : TapeTree := .split 2 (((86975451134818904920261055659359448183685030695690591147242051724633436933637427370726208307200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree25 tree29
attribute [irreducible] tree24
private theorem accepted_24 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox24) tree24 = true := by
  simp only [tree24,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox24 2 (86975451134818904920261055659359448183685030695690591147242051724633436933637427370726208307200000000000000000000000 : Int) false,decode_split denominator ibox24 2 (86975451134818904920261055659359448183685030695690591147242051724633436933637427370726208307200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_25 h,accepted_29 h⟩
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
private noncomputable def tree22 : TapeTree := .centered (candidateRows ibox22) (candidateRows (FixedTape.midBox ibox22))
attribute [irreducible] tree22
private theorem sign_22 : 2*denominator*(computed denominator (FixedTape.midBox ibox22)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox22).gradient k).lo.natAbs ((computed denominator ibox22).gradient k).hi.natAbs : Int)*((ibox22 k).hi-(ibox22 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox22
    (computed denominator ibox22) (computed denominator (FixedTape.midBox ibox22))
    (by decide +kernel)
private theorem midpoint_even_22 : ∀ k, 2 ∣ (ibox22 k).lo+(ibox22 k).hi := by decide +kernel
private theorem accepted_22 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox22) tree22 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox22 midpoint_even_22
  simp only [tree22,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox22,candidate_valid h (FixedTape.midBox ibox22),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox22 139 (FixedTape.rowsAux denominator ibox22 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox22) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_22
private noncomputable def tree21 : TapeTree := .split 2 (((86975451134818904920261055659359448183685030695690591147242051724633436933637427370726208307200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree22 tree23
attribute [irreducible] tree21
private theorem accepted_21 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox21) tree21 = true := by
  simp only [tree21,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox21 2 (86975451134818904920261055659359448183685030695690591147242051724633436933637427370726208307200000000000000000000000 : Int) false,decode_split denominator ibox21 2 (86975451134818904920261055659359448183685030695690591147242051724633436933637427370726208307200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_22 h,accepted_23 h⟩
private noncomputable def tree20 : TapeTree := .split 1 (((1217656315887464668883654779231032274571590429739668276061388724144868117070923983190166916300800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree21 tree24
attribute [irreducible] tree20
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox20 1 (1217656315887464668883654779231032274571590429739668276061388724144868117070923983190166916300800000000000000000000000 : Int) false,decode_split denominator ibox20 1 (1217656315887464668883654779231032274571590429739668276061388724144868117070923983190166916300800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_21 h,accepted_24 h⟩
private noncomputable def tree19 : TapeTree := .split 2 (((173950902269637809840522111318718896367370061391381182294484103449266873867274854741452416614400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree20 tree35
attribute [irreducible] tree19
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox19 2 (173950902269637809840522111318718896367370061391381182294484103449266873867274854741452416614400000000000000000000000 : Int) false,decode_split denominator ibox19 2 (173950902269637809840522111318718896367370061391381182294484103449266873867274854741452416614400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_20 h,accepted_35 h⟩
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
private noncomputable def tree16 : TapeTree := .split 1 (((869754511348189049202610556593594481836850306956905911472420517246334369336374273707262083072000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree17 tree18
attribute [irreducible] tree16
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox16 1 (869754511348189049202610556593594481836850306956905911472420517246334369336374273707262083072000000000000000000000000 : Int) false,decode_split denominator ibox16 1 (869754511348189049202610556593594481836850306956905911472420517246334369336374273707262083072000000000000000000000000 : Int) true]
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
private noncomputable def tree14 : TapeTree := .centered (candidateRows ibox14) (candidateRows (FixedTape.midBox ibox14))
attribute [irreducible] tree14
private theorem sign_14 : 2*denominator*(computed denominator (FixedTape.midBox ibox14)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox14).gradient k).lo.natAbs ((computed denominator ibox14).gradient k).hi.natAbs : Int)*((ibox14 k).hi-(ibox14 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox14
    (computed denominator ibox14) (computed denominator (FixedTape.midBox ibox14))
    (by decide +kernel)
private theorem midpoint_even_14 : ∀ k, 2 ∣ (ibox14 k).lo+(ibox14 k).hi := by decide +kernel
private theorem accepted_14 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox14) tree14 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox14 midpoint_even_14
  simp only [tree14,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox14,candidate_valid h (FixedTape.midBox ibox14),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox14 139 (FixedTape.rowsAux denominator ibox14 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox14) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_14
private noncomputable def tree13 : TapeTree := .split 1 (((869754511348189049202610556593594481836850306956905911472420517246334369336374273707262083072000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree14 tree15
attribute [irreducible] tree13
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox13 1 (869754511348189049202610556593594481836850306956905911472420517246334369336374273707262083072000000000000000000000000 : Int) false,decode_split denominator ibox13 1 (869754511348189049202610556593594481836850306956905911472420517246334369336374273707262083072000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_14 h,accepted_15 h⟩
private noncomputable def tree12 : TapeTree := .split 2 (((173950902269637809840522111318718896367370061391381182294484103449266873867274854741452416614400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree13 tree16
attribute [irreducible] tree12
private theorem accepted_12 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox12) tree12 = true := by
  simp only [tree12,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox12 2 (173950902269637809840522111318718896367370061391381182294484103449266873867274854741452416614400000000000000000000000 : Int) false,decode_split denominator ibox12 2 (173950902269637809840522111318718896367370061391381182294484103449266873867274854741452416614400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_13 h,accepted_16 h⟩
private noncomputable def tree11 : TapeTree := .split 1 (((1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree12 tree19
attribute [irreducible] tree11
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox11 1 (1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 : Int) false,decode_split denominator ibox11 1 (1043705413617826859043132667912313378204220368348287093766904620695601243203649128448714499686400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_12 h,accepted_19 h⟩
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
private noncomputable def tree8 : TapeTree := .split 2 (((173950902269637809840522111318718896367370061391381182294484103449266873867274854741452416614400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree9 tree10
attribute [irreducible] tree8
private theorem accepted_8 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox8) tree8 = true := by
  simp only [tree8,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox8 2 (173950902269637809840522111318718896367370061391381182294484103449266873867274854741452416614400000000000000000000000 : Int) false,decode_split denominator ibox8 2 (173950902269637809840522111318718896367370061391381182294484103449266873867274854741452416614400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_9 h,accepted_10 h⟩
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
private noncomputable def tree6 : TapeTree := .centered (candidateRows ibox6) (candidateRows (FixedTape.midBox ibox6))
attribute [irreducible] tree6
private theorem sign_6 : 2*denominator*(computed denominator (FixedTape.midBox ibox6)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox6).gradient k).lo.natAbs ((computed denominator ibox6).gradient k).hi.natAbs : Int)*((ibox6 k).hi-(ibox6 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox6
    (computed denominator ibox6) (computed denominator (FixedTape.midBox ibox6))
    (by decide +kernel)
private theorem midpoint_even_6 : ∀ k, 2 ∣ (ibox6 k).lo+(ibox6 k).hi := by decide +kernel
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox6 midpoint_even_6
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox6,candidate_valid h (FixedTape.midBox ibox6),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox6 139 (FixedTape.rowsAux denominator ibox6 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox6) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_6
private noncomputable def tree5 : TapeTree := .split 2 (((173950902269637809840522111318718896367370061391381182294484103449266873867274854741452416614400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree6 tree7
attribute [irreducible] tree5
private theorem accepted_5 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox5) tree5 = true := by
  simp only [tree5,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox5 2 (173950902269637809840522111318718896367370061391381182294484103449266873867274854741452416614400000000000000000000000 : Int) false,decode_split denominator ibox5 2 (173950902269637809840522111318718896367370061391381182294484103449266873867274854741452416614400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_6 h,accepted_7 h⟩
private noncomputable def tree4 : TapeTree := .split 1 (((347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree5 tree8
attribute [irreducible] tree4
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox4 1 (347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 : Int) false,decode_split denominator ibox4 1 (347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_5 h,accepted_8 h⟩
private noncomputable def tree3 : TapeTree := .split 1 (((695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree11
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 1 (695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) false,decode_split denominator ibox3 1 (695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_11 h⟩
private noncomputable def tree2 : TapeTree := .split 2 (((347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree48
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 2 (347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 : Int) false,decode_split denominator ibox2 2 (347901804539275619681044222637437792734740122782762364588968206898533747734549709482904833228800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_3 h,accepted_48 h⟩
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
private noncomputable def tree0 : TapeTree := .split 2 (((695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree1 tree83
attribute [irreducible] tree0
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox0 2 (695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) false,decode_split denominator ibox0 2 (695803609078551239362088445274875585469480245565524729177936413797067495469099418965809666457600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_1 h,accepted_83 h⟩
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (3385416666666667/5000000000000000 : ℚ) (11/16 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 139 = e144 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (3385416666666667/5000000000000000 : ℚ) (11/16 : ℚ)) x → eval e144 x ≤ 0 := by
  have hb := h.child_4 tape 139 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell90_high_internal_top

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell90_high_internal_top
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((3385416666666667/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((11/16 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 90 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 90 p)
    (hkb : ((11/16 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((3385416666666667/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r)
    (hcase : bStar < a), internalResidual (0 : Fin 9) a p A r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell90_high_internal_top.cell_bound h.child_8 h.child_9 (Cell90_high_internal_top.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell90_high_internal_top
