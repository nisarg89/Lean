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
namespace Cell93_high_internal_top
private noncomputable def qValues : Fin 4 → ℚ := ![(582070126602111655878924509640090244/536941545064636268130413669639224173 : ℚ),(15049202284521599102502500000000000000/16645187897003724312042823758815949363 : ℚ),(4026743507663013663168798658727/2492456773765609048276647900000 : ℚ),(-5563754886309050000000000/24924567737656090482766479 : ℚ)]
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
    priceLambda 93 p = ((582070126602111655878924509640090244/536941545064636268130413669639224173 : ℝ)+(15049202284521599102502500000000000000/16645187897003724312042823758815949363 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell93,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 93 p = (((4026743507663013663168798658727/2492456773765609048276647900000 : ℝ)+(-5563754886309050000000000/24924567737656090482766479 : ℝ)*p)-(145513/100000 : ℝ)*(1/1 : ℝ))/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell93,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e144 x = (x 0*(1-x 0))*(aPoint x+priceLambda 93 (x 0)*(HStar (yPoint x)-HStar (aPoint x)-HStar (capPoint x))+priceTau 93 (x 0)*psiStar (rPoint x)+(cStar-aPoint x-eta (0 : Fin 9)*psiStar (aPoint x))-(cStar-capPoint x-eta (0 : Fin 9)*psiStar (capPoint x))) := by
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
    (hL : lambdaStar (x 0) = priceLambda 93 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 93 (x 0)) :
    (1)*eval e144 x = (x 0*(1-x 0))*(internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_neg (not_le.mpr ha),if_neg (not_le.mpr hA),hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (3541666666666667/5000000000000000 : ℚ) (23/32 : ℚ)) x → eval e144 x ≤ 0)
    (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((3541666666666667/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((23/32 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 93 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 93 p)
    (hkb : ((23/32 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((3541666666666667/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r)
    (hcase : bStar < a) :
    internalResidual (0 : Fin 9) a p A r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxA,hxr⟩ := h7 (3541666666666667/5000000000000000 : ℚ) (23/32 : ℚ) bStar p a A r hpcell hkb hr.2 hap hcase hpA hAr
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,capPoint] using hxa
  have hAx : capPoint x = A := by simpa only [aPoint,rPoint,capPoint] using hxA
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,capPoint] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 93 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 93 (x 0) := by simpa only [hxp] using hT
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
.const (582070126602111655878924509640090244/536941545064636268130413669639224173 : ℚ),
.const (15049202284521599102502500000000000000/16645187897003724312042823758815949363 : ℚ),
.mul 108 1,
.add 107 109,
.const (4026743507663013663168798658727/2492456773765609048276647900000 : ℚ),
.const (-5563754886309050000000000/24924567737656090482766479 : ℚ),
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
private noncomputable def ssaQVals : Fin 18 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(-2840189/5000000 : ℚ),(113609/200000 : ℚ),(1085/4818 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ),(4818/3733 : ℚ),(145513/100000 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(582070126602111655878924509640090244/536941545064636268130413669639224173 : ℚ),(15049202284521599102502500000000000000/16645187897003724312042823758815949363 : ℚ),(4026743507663013663168798658727/2492456773765609048276647900000 : ℚ),(-5563754886309050000000000/24924567737656090482766479 : ℚ),(-145513/100000 : ℚ)]
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
private noncomputable def denominator : Int := 34396004358586112513280376532925475216755014905960978913144291256211550183024177971200000000000000000000000
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
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨24363836420665165323307223949896379163893237753420707847144866703881775589261543143703345534945198080000000,24722128132733768368920270633040185312042666963659453593822459340402051694048627916800000000000000000000000⟩,⟨0,34396004358586112513280376532925475216755014905960978913144291256211550183024177971200000000000000000000000⟩,⟨0,34396004358586112513280376532925475216755014905960978913144291256211550183024177971200000000000000000000000⟩,⟨0,34396004358586112513280376532925475216755014905960978913144291256211550183024177971200000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := splitI ibox0 2 17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 false
private noncomputable def ibox2 : Fin 4 → FixedTape.I := faceI ibox1 3 false
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 1 17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 2 8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox4 1 8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 false
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox5 2 4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 false
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox5 2 4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 true
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox4 1 8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 true
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox8 2 4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 false
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox8 2 4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 true
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox3 2 8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 true
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox11 2 12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 false
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox12 1 8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 false
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox12 1 8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 true
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox14 1 12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 false
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox14 1 12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 true
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox11 2 12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 true
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox17 1 8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 false
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox18 2 15048251906881424224560164733154895407330319021357928274500627424592553205073077862400000000000000000000000 false
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox18 2 15048251906881424224560164733154895407330319021357928274500627424592553205073077862400000000000000000000000 true
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox17 1 8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 true
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox21 1 12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 false
private noncomputable def ibox23 : Fin 4 → FixedTape.I := splitI ibox21 1 12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 true
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox2 1 17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 true
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox24 2 8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 false
private noncomputable def ibox26 : Fin 4 → FixedTape.I := splitI ibox25 1 25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 false
private noncomputable def ibox27 : Fin 4 → FixedTape.I := splitI ibox26 2 4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 false
private noncomputable def ibox28 : Fin 4 → FixedTape.I := splitI ibox27 1 21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 false
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox27 1 21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 true
private noncomputable def ibox30 : Fin 4 → FixedTape.I := splitI ibox26 2 4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 true
private noncomputable def ibox31 : Fin 4 → FixedTape.I := splitI ibox30 1 21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 false
private noncomputable def ibox32 : Fin 4 → FixedTape.I := splitI ibox30 1 21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 true
private noncomputable def ibox33 : Fin 4 → FixedTape.I := splitI ibox32 2 6449250817234896096240070599923526603141565294867683546214554610539665659317033369600000000000000000000000 false
private noncomputable def ibox34 : Fin 4 → FixedTape.I := splitI ibox32 2 6449250817234896096240070599923526603141565294867683546214554610539665659317033369600000000000000000000000 true
private noncomputable def ibox35 : Fin 4 → FixedTape.I := splitI ibox25 1 25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 true
private noncomputable def ibox36 : Fin 4 → FixedTape.I := splitI ibox35 2 4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 false
private noncomputable def ibox37 : Fin 4 → FixedTape.I := splitI ibox36 1 30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 false
private noncomputable def ibox38 : Fin 4 → FixedTape.I := faceI ibox37 1 true
private noncomputable def ibox39 : Fin 4 → FixedTape.I := splitI ibox36 1 30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 true
private noncomputable def ibox40 : Fin 4 → FixedTape.I := faceI ibox39 1 true
private noncomputable def ibox41 : Fin 4 → FixedTape.I := splitI ibox40 2 2149750272411632032080023533307842201047188431622561182071518203513221886439011123200000000000000000000000 false
private noncomputable def ibox42 : Fin 4 → FixedTape.I := splitI ibox41 2 1074875136205816016040011766653921100523594215811280591035759101756610943219505561600000000000000000000000 false
private noncomputable def ibox43 : Fin 4 → FixedTape.I := splitI ibox42 0 24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 false
private noncomputable def ibox44 : Fin 4 → FixedTape.I := splitI ibox43 2 537437568102908008020005883326960550261797107905640295517879550878305471609752780800000000000000000000000 false
private noncomputable def ibox45 : Fin 4 → FixedTape.I := splitI ibox44 0 24453409348682316084710485620682330700930595055980394283814264863011844615458314336977509151208898560000000 false
private noncomputable def ibox46 : Fin 4 → FixedTape.I := splitI ibox44 0 24453409348682316084710485620682330700930595055980394283814264863011844615458314336977509151208898560000000 true
private noncomputable def ibox47 : Fin 4 → FixedTape.I := splitI ibox43 2 537437568102908008020005883326960550261797107905640295517879550878305471609752780800000000000000000000000 true
private noncomputable def ibox48 : Fin 4 → FixedTape.I := splitI ibox47 0 24453409348682316084710485620682330700930595055980394283814264863011844615458314336977509151208898560000000 false
private noncomputable def ibox49 : Fin 4 → FixedTape.I := splitI ibox47 0 24453409348682316084710485620682330700930595055980394283814264863011844615458314336977509151208898560000000 true
private noncomputable def ibox50 : Fin 4 → FixedTape.I := splitI ibox42 0 24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 true
private noncomputable def ibox51 : Fin 4 → FixedTape.I := splitI ibox50 2 537437568102908008020005883326960550261797107905640295517879550878305471609752780800000000000000000000000 false
private noncomputable def ibox52 : Fin 4 → FixedTape.I := splitI ibox51 0 24632555204716617607517008962254233775005309661099767157153061181271982667851856723525836383736299520000000 false
private noncomputable def ibox53 : Fin 4 → FixedTape.I := faceI ibox52 2 false
private noncomputable def ibox54 : Fin 4 → FixedTape.I := splitI ibox51 0 24632555204716617607517008962254233775005309661099767157153061181271982667851856723525836383736299520000000 true
private noncomputable def ibox55 : Fin 4 → FixedTape.I := faceI ibox54 2 false
private noncomputable def ibox56 : Fin 4 → FixedTape.I := splitI ibox50 2 537437568102908008020005883326960550261797107905640295517879550878305471609752780800000000000000000000000 true
private noncomputable def ibox57 : Fin 4 → FixedTape.I := splitI ibox56 0 24632555204716617607517008962254233775005309661099767157153061181271982667851856723525836383736299520000000 false
private noncomputable def ibox58 : Fin 4 → FixedTape.I := splitI ibox56 0 24632555204716617607517008962254233775005309661099767157153061181271982667851856723525836383736299520000000 true
private noncomputable def ibox59 : Fin 4 → FixedTape.I := splitI ibox41 2 1074875136205816016040011766653921100523594215811280591035759101756610943219505561600000000000000000000000 true
private noncomputable def ibox60 : Fin 4 → FixedTape.I := splitI ibox59 0 24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 false
private noncomputable def ibox61 : Fin 4 → FixedTape.I := splitI ibox60 2 1612312704308724024060017649980881650785391323716920886553638652634916414829258342400000000000000000000000 false
private noncomputable def ibox62 : Fin 4 → FixedTape.I := splitI ibox60 2 1612312704308724024060017649980881650785391323716920886553638652634916414829258342400000000000000000000000 true
private noncomputable def ibox63 : Fin 4 → FixedTape.I := splitI ibox59 0 24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 true
private noncomputable def ibox64 : Fin 4 → FixedTape.I := splitI ibox63 2 1612312704308724024060017649980881650785391323716920886553638652634916414829258342400000000000000000000000 false
private noncomputable def ibox65 : Fin 4 → FixedTape.I := splitI ibox63 2 1612312704308724024060017649980881650785391323716920886553638652634916414829258342400000000000000000000000 true
private noncomputable def ibox66 : Fin 4 → FixedTape.I := splitI ibox40 2 2149750272411632032080023533307842201047188431622561182071518203513221886439011123200000000000000000000000 true
private noncomputable def ibox67 : Fin 4 → FixedTape.I := splitI ibox66 2 3224625408617448048120035299961763301570782647433841773107277305269832829658516684800000000000000000000000 false
private noncomputable def ibox68 : Fin 4 → FixedTape.I := splitI ibox67 0 24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 false
private noncomputable def ibox69 : Fin 4 → FixedTape.I := splitI ibox67 0 24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 true
private noncomputable def ibox70 : Fin 4 → FixedTape.I := splitI ibox66 2 3224625408617448048120035299961763301570782647433841773107277305269832829658516684800000000000000000000000 true
private noncomputable def ibox71 : Fin 4 → FixedTape.I := splitI ibox70 0 24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 false
private noncomputable def ibox72 : Fin 4 → FixedTape.I := splitI ibox70 0 24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 true
private noncomputable def ibox73 : Fin 4 → FixedTape.I := splitI ibox35 2 4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 true
private noncomputable def ibox74 : Fin 4 → FixedTape.I := splitI ibox73 1 30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 false
private noncomputable def ibox75 : Fin 4 → FixedTape.I := splitI ibox74 1 27946753541351216417040305933001948613613449611093295366929736645671884523707144601600000000000000000000000 false
private noncomputable def ibox76 : Fin 4 → FixedTape.I := splitI ibox74 1 27946753541351216417040305933001948613613449611093295366929736645671884523707144601600000000000000000000000 true
private noncomputable def ibox77 : Fin 4 → FixedTape.I := splitI ibox76 2 6449250817234896096240070599923526603141565294867683546214554610539665659317033369600000000000000000000000 false
private noncomputable def ibox78 : Fin 4 → FixedTape.I := splitI ibox76 2 6449250817234896096240070599923526603141565294867683546214554610539665659317033369600000000000000000000000 true
private noncomputable def ibox79 : Fin 4 → FixedTape.I := splitI ibox73 1 30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 true
private noncomputable def ibox80 : Fin 4 → FixedTape.I := splitI ibox79 2 6449250817234896096240070599923526603141565294867683546214554610539665659317033369600000000000000000000000 false
private noncomputable def ibox81 : Fin 4 → FixedTape.I := splitI ibox80 1 32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 false
private noncomputable def ibox82 : Fin 4 → FixedTape.I := splitI ibox81 0 24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 false
private noncomputable def ibox83 : Fin 4 → FixedTape.I := splitI ibox81 0 24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 true
private noncomputable def ibox84 : Fin 4 → FixedTape.I := splitI ibox80 1 32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 true
private noncomputable def ibox85 : Fin 4 → FixedTape.I := splitI ibox84 0 24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 false
private noncomputable def ibox86 : Fin 4 → FixedTape.I := faceI ibox85 1 true
private noncomputable def ibox87 : Fin 4 → FixedTape.I := splitI ibox84 0 24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 true
private noncomputable def ibox88 : Fin 4 → FixedTape.I := faceI ibox87 1 true
private noncomputable def ibox89 : Fin 4 → FixedTape.I := splitI ibox79 2 6449250817234896096240070599923526603141565294867683546214554610539665659317033369600000000000000000000000 true
private noncomputable def ibox90 : Fin 4 → FixedTape.I := splitI ibox89 1 32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 false
private noncomputable def ibox91 : Fin 4 → FixedTape.I := splitI ibox90 0 24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 false
private noncomputable def ibox92 : Fin 4 → FixedTape.I := splitI ibox90 0 24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 true
private noncomputable def ibox93 : Fin 4 → FixedTape.I := splitI ibox89 1 32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 true
private noncomputable def ibox94 : Fin 4 → FixedTape.I := splitI ibox93 0 24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 false
private noncomputable def ibox95 : Fin 4 → FixedTape.I := splitI ibox93 0 24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 true
private noncomputable def ibox96 : Fin 4 → FixedTape.I := faceI ibox95 1 true
private noncomputable def ibox97 : Fin 4 → FixedTape.I := splitI ibox24 2 8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 true
private noncomputable def ibox98 : Fin 4 → FixedTape.I := splitI ibox97 1 25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 false
private noncomputable def ibox99 : Fin 4 → FixedTape.I := splitI ibox98 2 12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 false
private noncomputable def ibox100 : Fin 4 → FixedTape.I := splitI ibox99 1 21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 false
private noncomputable def ibox101 : Fin 4 → FixedTape.I := splitI ibox99 1 21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 true
private noncomputable def ibox102 : Fin 4 → FixedTape.I := splitI ibox101 2 10748751362058160160400117666539211005235942158112805910357591017566109432195055616000000000000000000000000 false
private noncomputable def ibox103 : Fin 4 → FixedTape.I := splitI ibox101 2 10748751362058160160400117666539211005235942158112805910357591017566109432195055616000000000000000000000000 true
private noncomputable def ibox104 : Fin 4 → FixedTape.I := splitI ibox98 2 12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 true
private noncomputable def ibox105 : Fin 4 → FixedTape.I := splitI ibox104 1 21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 false
private noncomputable def ibox106 : Fin 4 → FixedTape.I := splitI ibox104 1 21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 true
private noncomputable def ibox107 : Fin 4 → FixedTape.I := splitI ibox106 2 15048251906881424224560164733154895407330319021357928274500627424592553205073077862400000000000000000000000 false
private noncomputable def ibox108 : Fin 4 → FixedTape.I := splitI ibox106 2 15048251906881424224560164733154895407330319021357928274500627424592553205073077862400000000000000000000000 true
private noncomputable def ibox109 : Fin 4 → FixedTape.I := splitI ibox97 1 25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 true
private noncomputable def ibox110 : Fin 4 → FixedTape.I := splitI ibox109 2 12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 false
private noncomputable def ibox111 : Fin 4 → FixedTape.I := splitI ibox110 1 30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 false
private noncomputable def ibox112 : Fin 4 → FixedTape.I := splitI ibox111 2 10748751362058160160400117666539211005235942158112805910357591017566109432195055616000000000000000000000000 false
private noncomputable def ibox113 : Fin 4 → FixedTape.I := splitI ibox112 1 27946753541351216417040305933001948613613449611093295366929736645671884523707144601600000000000000000000000 false
private noncomputable def ibox114 : Fin 4 → FixedTape.I := splitI ibox112 1 27946753541351216417040305933001948613613449611093295366929736645671884523707144601600000000000000000000000 true
private noncomputable def ibox115 : Fin 4 → FixedTape.I := splitI ibox111 2 10748751362058160160400117666539211005235942158112805910357591017566109432195055616000000000000000000000000 true
private noncomputable def ibox116 : Fin 4 → FixedTape.I := splitI ibox110 1 30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 true
private noncomputable def ibox117 : Fin 4 → FixedTape.I := splitI ibox116 2 10748751362058160160400117666539211005235942158112805910357591017566109432195055616000000000000000000000000 false
private noncomputable def ibox118 : Fin 4 → FixedTape.I := splitI ibox117 1 32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 false
private noncomputable def ibox119 : Fin 4 → FixedTape.I := splitI ibox117 1 32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 true
private noncomputable def ibox120 : Fin 4 → FixedTape.I := splitI ibox119 0 24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 false
private noncomputable def ibox121 : Fin 4 → FixedTape.I := splitI ibox119 0 24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 true
private noncomputable def ibox122 : Fin 4 → FixedTape.I := splitI ibox116 2 10748751362058160160400117666539211005235942158112805910357591017566109432195055616000000000000000000000000 true
private noncomputable def ibox123 : Fin 4 → FixedTape.I := splitI ibox122 1 32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 false
private noncomputable def ibox124 : Fin 4 → FixedTape.I := splitI ibox122 1 32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 true
private noncomputable def ibox125 : Fin 4 → FixedTape.I := splitI ibox124 0 24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 false
private noncomputable def ibox126 : Fin 4 → FixedTape.I := splitI ibox124 0 24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 true
private noncomputable def ibox127 : Fin 4 → FixedTape.I := splitI ibox109 2 12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 true
private noncomputable def ibox128 : Fin 4 → FixedTape.I := splitI ibox127 2 15048251906881424224560164733154895407330319021357928274500627424592553205073077862400000000000000000000000 false
private noncomputable def ibox129 : Fin 4 → FixedTape.I := splitI ibox128 1 30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 false
private noncomputable def ibox130 : Fin 4 → FixedTape.I := splitI ibox128 1 30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 true
private noncomputable def ibox131 : Fin 4 → FixedTape.I := splitI ibox130 0 24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 false
private noncomputable def ibox132 : Fin 4 → FixedTape.I := splitI ibox130 0 24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 true
private noncomputable def ibox133 : Fin 4 → FixedTape.I := splitI ibox127 2 15048251906881424224560164733154895407330319021357928274500627424592553205073077862400000000000000000000000 true
private noncomputable def ibox134 : Fin 4 → FixedTape.I := splitI ibox133 1 30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 false
private noncomputable def ibox135 : Fin 4 → FixedTape.I := splitI ibox133 1 30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 true
private noncomputable def ibox136 : Fin 4 → FixedTape.I := splitI ibox135 0 24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 false
private noncomputable def ibox137 : Fin 4 → FixedTape.I := splitI ibox135 0 24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 true
private noncomputable def ibox138 : Fin 4 → FixedTape.I := splitI ibox0 2 17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 true
private noncomputable def ibox139 : Fin 4 → FixedTape.I := splitI ibox138 2 25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 false
private noncomputable def ibox140 : Fin 4 → FixedTape.I := faceI ibox139 3 false
private noncomputable def ibox141 : Fin 4 → FixedTape.I := splitI ibox140 2 21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 false
private noncomputable def ibox142 : Fin 4 → FixedTape.I := splitI ibox141 1 17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 false
private noncomputable def ibox143 : Fin 4 → FixedTape.I := splitI ibox142 1 8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 false
private noncomputable def ibox144 : Fin 4 → FixedTape.I := splitI ibox143 2 19347752451704688288720211799770579809424695884603050638643663831618996977951100108800000000000000000000000 false
private noncomputable def ibox145 : Fin 4 → FixedTape.I := splitI ibox143 2 19347752451704688288720211799770579809424695884603050638643663831618996977951100108800000000000000000000000 true
private noncomputable def ibox146 : Fin 4 → FixedTape.I := splitI ibox145 1 4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 false
private noncomputable def ibox147 : Fin 4 → FixedTape.I := splitI ibox145 1 4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 true
private noncomputable def ibox148 : Fin 4 → FixedTape.I := splitI ibox142 1 8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 true
private noncomputable def ibox149 : Fin 4 → FixedTape.I := splitI ibox148 2 19347752451704688288720211799770579809424695884603050638643663831618996977951100108800000000000000000000000 false
private noncomputable def ibox150 : Fin 4 → FixedTape.I := splitI ibox148 2 19347752451704688288720211799770579809424695884603050638643663831618996977951100108800000000000000000000000 true
private noncomputable def ibox151 : Fin 4 → FixedTape.I := splitI ibox150 1 12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 false
private noncomputable def ibox152 : Fin 4 → FixedTape.I := splitI ibox150 1 12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 true
private noncomputable def ibox153 : Fin 4 → FixedTape.I := splitI ibox141 1 17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 true
private noncomputable def ibox154 : Fin 4 → FixedTape.I := splitI ibox153 1 25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 false
private noncomputable def ibox155 : Fin 4 → FixedTape.I := splitI ibox154 2 19347752451704688288720211799770579809424695884603050638643663831618996977951100108800000000000000000000000 false
private noncomputable def ibox156 : Fin 4 → FixedTape.I := splitI ibox155 1 21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 false
private noncomputable def ibox157 : Fin 4 → FixedTape.I := splitI ibox155 1 21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 true
private noncomputable def ibox158 : Fin 4 → FixedTape.I := splitI ibox154 2 19347752451704688288720211799770579809424695884603050638643663831618996977951100108800000000000000000000000 true
private noncomputable def ibox159 : Fin 4 → FixedTape.I := splitI ibox158 1 21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 false
private noncomputable def ibox160 : Fin 4 → FixedTape.I := splitI ibox158 1 21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 true
private noncomputable def ibox161 : Fin 4 → FixedTape.I := splitI ibox153 1 25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 true
private noncomputable def ibox162 : Fin 4 → FixedTape.I := splitI ibox161 2 19347752451704688288720211799770579809424695884603050638643663831618996977951100108800000000000000000000000 false
private noncomputable def ibox163 : Fin 4 → FixedTape.I := splitI ibox162 1 30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 false
private noncomputable def ibox164 : Fin 4 → FixedTape.I := splitI ibox162 1 30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 true
private noncomputable def ibox165 : Fin 4 → FixedTape.I := splitI ibox161 2 19347752451704688288720211799770579809424695884603050638643663831618996977951100108800000000000000000000000 true
private noncomputable def ibox166 : Fin 4 → FixedTape.I := splitI ibox165 1 30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 false
private noncomputable def ibox167 : Fin 4 → FixedTape.I := splitI ibox165 1 30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 true
private noncomputable def ibox168 : Fin 4 → FixedTape.I := splitI ibox140 2 21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 true
private noncomputable def ibox169 : Fin 4 → FixedTape.I := splitI ibox168 1 17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 false
private noncomputable def ibox170 : Fin 4 → FixedTape.I := splitI ibox169 2 23647252996527952352880258866386264211519072747848173002786700238645440750829122355200000000000000000000000 false
private noncomputable def ibox171 : Fin 4 → FixedTape.I := splitI ibox170 1 8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 false
private noncomputable def ibox172 : Fin 4 → FixedTape.I := splitI ibox171 1 4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 false
private noncomputable def ibox173 : Fin 4 → FixedTape.I := splitI ibox171 1 4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 true
private noncomputable def ibox174 : Fin 4 → FixedTape.I := splitI ibox170 1 8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 true
private noncomputable def ibox175 : Fin 4 → FixedTape.I := splitI ibox174 2 22572377860322136336840247099732343110995478532036892411750941136888829807609616793600000000000000000000000 false
private noncomputable def ibox176 : Fin 4 → FixedTape.I := splitI ibox174 2 22572377860322136336840247099732343110995478532036892411750941136888829807609616793600000000000000000000000 true
private noncomputable def ibox177 : Fin 4 → FixedTape.I := splitI ibox169 2 23647252996527952352880258866386264211519072747848173002786700238645440750829122355200000000000000000000000 true
private noncomputable def ibox178 : Fin 4 → FixedTape.I := splitI ibox177 1 8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 false
private noncomputable def ibox179 : Fin 4 → FixedTape.I := splitI ibox178 2 24722128132733768368920270633040185312042666963659453593822459340402051694048627916800000000000000000000000 false
private noncomputable def ibox180 : Fin 4 → FixedTape.I := splitI ibox178 2 24722128132733768368920270633040185312042666963659453593822459340402051694048627916800000000000000000000000 true
private noncomputable def ibox181 : Fin 4 → FixedTape.I := splitI ibox177 1 8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 true
private noncomputable def ibox182 : Fin 4 → FixedTape.I := splitI ibox181 2 24722128132733768368920270633040185312042666963659453593822459340402051694048627916800000000000000000000000 false
private noncomputable def ibox183 : Fin 4 → FixedTape.I := splitI ibox181 2 24722128132733768368920270633040185312042666963659453593822459340402051694048627916800000000000000000000000 true
private noncomputable def ibox184 : Fin 4 → FixedTape.I := splitI ibox168 1 17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 true
private noncomputable def ibox185 : Fin 4 → FixedTape.I := splitI ibox184 2 23647252996527952352880258866386264211519072747848173002786700238645440750829122355200000000000000000000000 false
private noncomputable def ibox186 : Fin 4 → FixedTape.I := splitI ibox185 1 25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 false
private noncomputable def ibox187 : Fin 4 → FixedTape.I := splitI ibox186 2 22572377860322136336840247099732343110995478532036892411750941136888829807609616793600000000000000000000000 false
private noncomputable def ibox188 : Fin 4 → FixedTape.I := splitI ibox186 2 22572377860322136336840247099732343110995478532036892411750941136888829807609616793600000000000000000000000 true
private noncomputable def ibox189 : Fin 4 → FixedTape.I := splitI ibox185 1 25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 true
private noncomputable def ibox190 : Fin 4 → FixedTape.I := splitI ibox189 1 30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 false
private noncomputable def ibox191 : Fin 4 → FixedTape.I := splitI ibox189 1 30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 true
private noncomputable def ibox192 : Fin 4 → FixedTape.I := splitI ibox184 2 23647252996527952352880258866386264211519072747848173002786700238645440750829122355200000000000000000000000 true
private noncomputable def ibox193 : Fin 4 → FixedTape.I := splitI ibox192 1 25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 false
private noncomputable def ibox194 : Fin 4 → FixedTape.I := splitI ibox193 2 24722128132733768368920270633040185312042666963659453593822459340402051694048627916800000000000000000000000 false
private noncomputable def ibox195 : Fin 4 → FixedTape.I := splitI ibox193 2 24722128132733768368920270633040185312042666963659453593822459340402051694048627916800000000000000000000000 true
private noncomputable def ibox196 : Fin 4 → FixedTape.I := splitI ibox192 1 25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 true
private noncomputable def ibox197 : Fin 4 → FixedTape.I := splitI ibox196 2 24722128132733768368920270633040185312042666963659453593822459340402051694048627916800000000000000000000000 false
private noncomputable def ibox198 : Fin 4 → FixedTape.I := splitI ibox196 2 24722128132733768368920270633040185312042666963659453593822459340402051694048627916800000000000000000000000 true
private noncomputable def ibox199 : Fin 4 → FixedTape.I := splitI ibox138 2 25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 true
private noncomputable def ibox200 : Fin 4 → FixedTape.I := splitI ibox199 2 30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 false
private noncomputable def ibox201 : Fin 4 → FixedTape.I := faceI ibox200 3 false
private noncomputable def ibox202 : Fin 4 → FixedTape.I := splitI ibox201 1 17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 false
private noncomputable def ibox203 : Fin 4 → FixedTape.I := splitI ibox202 2 27946753541351216417040305933001948613613449611093295366929736645671884523707144601600000000000000000000000 false
private noncomputable def ibox204 : Fin 4 → FixedTape.I := splitI ibox203 2 26871878405145400401000294166348027513089855395282014775893977543915273580487639040000000000000000000000000 false
private noncomputable def ibox205 : Fin 4 → FixedTape.I := splitI ibox204 1 8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 false
private noncomputable def ibox206 : Fin 4 → FixedTape.I := splitI ibox204 1 8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 true
private noncomputable def ibox207 : Fin 4 → FixedTape.I := splitI ibox203 2 26871878405145400401000294166348027513089855395282014775893977543915273580487639040000000000000000000000000 true
private noncomputable def ibox208 : Fin 4 → FixedTape.I := faceI ibox207 2 false
private noncomputable def ibox209 : Fin 4 → FixedTape.I := splitI ibox202 2 27946753541351216417040305933001948613613449611093295366929736645671884523707144601600000000000000000000000 true
private noncomputable def ibox210 : Fin 4 → FixedTape.I := faceI ibox209 2 false
private noncomputable def ibox211 : Fin 4 → FixedTape.I := splitI ibox201 1 17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 true
private noncomputable def ibox212 : Fin 4 → FixedTape.I := splitI ibox211 2 27946753541351216417040305933001948613613449611093295366929736645671884523707144601600000000000000000000000 false
private noncomputable def ibox213 : Fin 4 → FixedTape.I := splitI ibox212 1 25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 false
private noncomputable def ibox214 : Fin 4 → FixedTape.I := splitI ibox213 2 26871878405145400401000294166348027513089855395282014775893977543915273580487639040000000000000000000000000 false
private noncomputable def ibox215 : Fin 4 → FixedTape.I := splitI ibox213 2 26871878405145400401000294166348027513089855395282014775893977543915273580487639040000000000000000000000000 true
private noncomputable def ibox216 : Fin 4 → FixedTape.I := splitI ibox212 1 25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 true
private noncomputable def ibox217 : Fin 4 → FixedTape.I := faceI ibox216 2 false
private noncomputable def ibox218 : Fin 4 → FixedTape.I := splitI ibox211 2 27946753541351216417040305933001948613613449611093295366929736645671884523707144601600000000000000000000000 true
private noncomputable def ibox219 : Fin 4 → FixedTape.I := faceI ibox218 2 false
private noncomputable def ibox220 : Fin 4 → FixedTape.I := splitI ibox199 2 30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 true
private noncomputable def ibox221 : Fin 4 → FixedTape.I := splitI ibox220 1 17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 false
private noncomputable def ibox222 : Fin 4 → FixedTape.I := splitI ibox221 2 32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 false
private noncomputable def ibox223 : Fin 4 → FixedTape.I := faceI ibox222 2 false
private noncomputable def ibox224 : Fin 4 → FixedTape.I := splitI ibox221 2 32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 true
private noncomputable def ibox225 : Fin 4 → FixedTape.I := splitI ibox220 1 17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 true
private noncomputable def ibox226 : Fin 4 → FixedTape.I := splitI ibox225 2 32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 false
private noncomputable def ibox227 : Fin 4 → FixedTape.I := faceI ibox226 2 false
private noncomputable def ibox228 : Fin 4 → FixedTape.I := splitI ibox225 2 32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 true
private noncomputable def ibox229 : Fin 4 → FixedTape.I := faceI ibox228 2 false
private noncomputable def tree229 : TapeTree := .centered (candidateRows ibox229) (candidateRows (FixedTape.midBox ibox229))
attribute [irreducible] tree229
private theorem sign_229 : 2*denominator*(computed denominator (FixedTape.midBox ibox229)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox229).gradient k).lo.natAbs ((computed denominator ibox229).gradient k).hi.natAbs : Int)*((ibox229 k).hi-(ibox229 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox229
    (computed denominator ibox229) (computed denominator (FixedTape.midBox ibox229))
    (by decide +kernel)
private theorem midpoint_even_229 : ∀ k, 2 ∣ (ibox229 k).lo+(ibox229 k).hi := by decide +kernel
private theorem accepted_229 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox229) tree229 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox229 midpoint_even_229
  simp only [tree229,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox229,candidate_valid h (FixedTape.midBox ibox229),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox229 139 (FixedTape.rowsAux denominator ibox229 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox229) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_229
private noncomputable def tree228 : TapeTree := .face 2 false (candidateRows ibox228) tree229
attribute [irreducible] tree228
private theorem sign_228 : ((computed denominator ibox228).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_228 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox228) tree228 = true := by
  simp only [tree228,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox228,?_,accepted_229 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox228)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox228).gradient 2).hi) denominator_positive).1 sign_228
private noncomputable def tree227 : TapeTree := .centered (candidateRows ibox227) (candidateRows (FixedTape.midBox ibox227))
attribute [irreducible] tree227
private theorem sign_227 : 2*denominator*(computed denominator (FixedTape.midBox ibox227)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox227).gradient k).lo.natAbs ((computed denominator ibox227).gradient k).hi.natAbs : Int)*((ibox227 k).hi-(ibox227 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox227
    (computed denominator ibox227) (computed denominator (FixedTape.midBox ibox227))
    (by decide +kernel)
private theorem midpoint_even_227 : ∀ k, 2 ∣ (ibox227 k).lo+(ibox227 k).hi := by decide +kernel
private theorem accepted_227 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox227) tree227 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox227 midpoint_even_227
  simp only [tree227,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox227,candidate_valid h (FixedTape.midBox ibox227),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox227 139 (FixedTape.rowsAux denominator ibox227 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox227) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_227
private noncomputable def tree226 : TapeTree := .face 2 false (candidateRows ibox226) tree227
attribute [irreducible] tree226
private theorem sign_226 : ((computed denominator ibox226).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_226 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox226) tree226 = true := by
  simp only [tree226,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox226,?_,accepted_227 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox226)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox226).gradient 2).hi) denominator_positive).1 sign_226
private noncomputable def tree225 : TapeTree := .split 2 (((32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree226 tree228
attribute [irreducible] tree225
private theorem accepted_225 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox225) tree225 = true := by
  simp only [tree225,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox225 2 (32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 : Int) false,decode_split denominator ibox225 2 (32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_226 h,accepted_228 h⟩
private noncomputable def tree224 : TapeTree := .centered (candidateRows ibox224) (candidateRows (FixedTape.midBox ibox224))
attribute [irreducible] tree224
private theorem sign_224 : 2*denominator*(computed denominator (FixedTape.midBox ibox224)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox224).gradient k).lo.natAbs ((computed denominator ibox224).gradient k).hi.natAbs : Int)*((ibox224 k).hi-(ibox224 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox224
    (computed denominator ibox224) (computed denominator (FixedTape.midBox ibox224))
    (by decide +kernel)
private theorem midpoint_even_224 : ∀ k, 2 ∣ (ibox224 k).lo+(ibox224 k).hi := by decide +kernel
private theorem accepted_224 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox224) tree224 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox224 midpoint_even_224
  simp only [tree224,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox224,candidate_valid h (FixedTape.midBox ibox224),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox224 139 (FixedTape.rowsAux denominator ibox224 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox224) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_224
private noncomputable def tree223 : TapeTree := .centered (candidateRows ibox223) (candidateRows (FixedTape.midBox ibox223))
attribute [irreducible] tree223
private theorem sign_223 : 2*denominator*(computed denominator (FixedTape.midBox ibox223)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox223).gradient k).lo.natAbs ((computed denominator ibox223).gradient k).hi.natAbs : Int)*((ibox223 k).hi-(ibox223 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox223
    (computed denominator ibox223) (computed denominator (FixedTape.midBox ibox223))
    (by decide +kernel)
private theorem midpoint_even_223 : ∀ k, 2 ∣ (ibox223 k).lo+(ibox223 k).hi := by decide +kernel
private theorem accepted_223 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox223) tree223 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox223 midpoint_even_223
  simp only [tree223,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox223,candidate_valid h (FixedTape.midBox ibox223),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox223 139 (FixedTape.rowsAux denominator ibox223 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox223) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_223
private noncomputable def tree222 : TapeTree := .face 2 false (candidateRows ibox222) tree223
attribute [irreducible] tree222
private theorem sign_222 : ((computed denominator ibox222).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_222 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox222) tree222 = true := by
  simp only [tree222,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox222,?_,accepted_223 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox222)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox222).gradient 2).hi) denominator_positive).1 sign_222
private noncomputable def tree221 : TapeTree := .split 2 (((32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree222 tree224
attribute [irreducible] tree221
private theorem accepted_221 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox221) tree221 = true := by
  simp only [tree221,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox221 2 (32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 : Int) false,decode_split denominator ibox221 2 (32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_222 h,accepted_224 h⟩
private noncomputable def tree220 : TapeTree := .split 1 (((17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree221 tree225
attribute [irreducible] tree220
private theorem accepted_220 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox220) tree220 = true := by
  simp only [tree220,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox220 1 (17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 : Int) false,decode_split denominator ibox220 1 (17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_221 h,accepted_225 h⟩
private noncomputable def tree219 : TapeTree := .centered (candidateRows ibox219) (candidateRows (FixedTape.midBox ibox219))
attribute [irreducible] tree219
private theorem sign_219 : 2*denominator*(computed denominator (FixedTape.midBox ibox219)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox219).gradient k).lo.natAbs ((computed denominator ibox219).gradient k).hi.natAbs : Int)*((ibox219 k).hi-(ibox219 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox219
    (computed denominator ibox219) (computed denominator (FixedTape.midBox ibox219))
    (by decide +kernel)
private theorem midpoint_even_219 : ∀ k, 2 ∣ (ibox219 k).lo+(ibox219 k).hi := by decide +kernel
private theorem accepted_219 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox219) tree219 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox219 midpoint_even_219
  simp only [tree219,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox219,candidate_valid h (FixedTape.midBox ibox219),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox219 139 (FixedTape.rowsAux denominator ibox219 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox219) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_219
private noncomputable def tree218 : TapeTree := .face 2 false (candidateRows ibox218) tree219
attribute [irreducible] tree218
private theorem sign_218 : ((computed denominator ibox218).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_218 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox218) tree218 = true := by
  simp only [tree218,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox218,?_,accepted_219 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox218)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox218).gradient 2).hi) denominator_positive).1 sign_218
private noncomputable def tree217 : TapeTree := .centered (candidateRows ibox217) (candidateRows (FixedTape.midBox ibox217))
attribute [irreducible] tree217
private theorem sign_217 : 2*denominator*(computed denominator (FixedTape.midBox ibox217)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox217).gradient k).lo.natAbs ((computed denominator ibox217).gradient k).hi.natAbs : Int)*((ibox217 k).hi-(ibox217 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox217
    (computed denominator ibox217) (computed denominator (FixedTape.midBox ibox217))
    (by decide +kernel)
private theorem midpoint_even_217 : ∀ k, 2 ∣ (ibox217 k).lo+(ibox217 k).hi := by decide +kernel
private theorem accepted_217 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox217) tree217 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox217 midpoint_even_217
  simp only [tree217,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox217,candidate_valid h (FixedTape.midBox ibox217),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox217 139 (FixedTape.rowsAux denominator ibox217 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox217) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_217
private noncomputable def tree216 : TapeTree := .face 2 false (candidateRows ibox216) tree217
attribute [irreducible] tree216
private theorem sign_216 : ((computed denominator ibox216).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_216 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox216) tree216 = true := by
  simp only [tree216,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox216,?_,accepted_217 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox216)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox216).gradient 2).hi) denominator_positive).1 sign_216
private noncomputable def tree215 : TapeTree := .centered (candidateRows ibox215) (candidateRows (FixedTape.midBox ibox215))
attribute [irreducible] tree215
private theorem sign_215 : 2*denominator*(computed denominator (FixedTape.midBox ibox215)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox215).gradient k).lo.natAbs ((computed denominator ibox215).gradient k).hi.natAbs : Int)*((ibox215 k).hi-(ibox215 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox215
    (computed denominator ibox215) (computed denominator (FixedTape.midBox ibox215))
    (by decide +kernel)
private theorem midpoint_even_215 : ∀ k, 2 ∣ (ibox215 k).lo+(ibox215 k).hi := by decide +kernel
private theorem accepted_215 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox215) tree215 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox215 midpoint_even_215
  simp only [tree215,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox215,candidate_valid h (FixedTape.midBox ibox215),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox215 139 (FixedTape.rowsAux denominator ibox215 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox215) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_215
private noncomputable def tree214 : TapeTree := .centered (candidateRows ibox214) (candidateRows (FixedTape.midBox ibox214))
attribute [irreducible] tree214
private theorem sign_214 : 2*denominator*(computed denominator (FixedTape.midBox ibox214)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox214).gradient k).lo.natAbs ((computed denominator ibox214).gradient k).hi.natAbs : Int)*((ibox214 k).hi-(ibox214 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox214
    (computed denominator ibox214) (computed denominator (FixedTape.midBox ibox214))
    (by decide +kernel)
private theorem midpoint_even_214 : ∀ k, 2 ∣ (ibox214 k).lo+(ibox214 k).hi := by decide +kernel
private theorem accepted_214 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox214) tree214 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox214 midpoint_even_214
  simp only [tree214,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox214,candidate_valid h (FixedTape.midBox ibox214),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox214 139 (FixedTape.rowsAux denominator ibox214 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox214) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_214
private noncomputable def tree213 : TapeTree := .split 2 (((26871878405145400401000294166348027513089855395282014775893977543915273580487639040000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree214 tree215
attribute [irreducible] tree213
private theorem accepted_213 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox213) tree213 = true := by
  simp only [tree213,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox213 2 (26871878405145400401000294166348027513089855395282014775893977543915273580487639040000000000000000000000000 : Int) false,decode_split denominator ibox213 2 (26871878405145400401000294166348027513089855395282014775893977543915273580487639040000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_214 h,accepted_215 h⟩
private noncomputable def tree212 : TapeTree := .split 1 (((25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree213 tree216
attribute [irreducible] tree212
private theorem accepted_212 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox212) tree212 = true := by
  simp only [tree212,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox212 1 (25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 : Int) false,decode_split denominator ibox212 1 (25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_213 h,accepted_216 h⟩
private noncomputable def tree211 : TapeTree := .split 2 (((27946753541351216417040305933001948613613449611093295366929736645671884523707144601600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree212 tree218
attribute [irreducible] tree211
private theorem accepted_211 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox211) tree211 = true := by
  simp only [tree211,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox211 2 (27946753541351216417040305933001948613613449611093295366929736645671884523707144601600000000000000000000000 : Int) false,decode_split denominator ibox211 2 (27946753541351216417040305933001948613613449611093295366929736645671884523707144601600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_212 h,accepted_218 h⟩
private noncomputable def tree210 : TapeTree := .centered (candidateRows ibox210) (candidateRows (FixedTape.midBox ibox210))
attribute [irreducible] tree210
private theorem sign_210 : 2*denominator*(computed denominator (FixedTape.midBox ibox210)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox210).gradient k).lo.natAbs ((computed denominator ibox210).gradient k).hi.natAbs : Int)*((ibox210 k).hi-(ibox210 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox210
    (computed denominator ibox210) (computed denominator (FixedTape.midBox ibox210))
    (by decide +kernel)
private theorem midpoint_even_210 : ∀ k, 2 ∣ (ibox210 k).lo+(ibox210 k).hi := by decide +kernel
private theorem accepted_210 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox210) tree210 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox210 midpoint_even_210
  simp only [tree210,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox210,candidate_valid h (FixedTape.midBox ibox210),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox210 139 (FixedTape.rowsAux denominator ibox210 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox210) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_210
private noncomputable def tree209 : TapeTree := .face 2 false (candidateRows ibox209) tree210
attribute [irreducible] tree209
private theorem sign_209 : ((computed denominator ibox209).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_209 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox209) tree209 = true := by
  simp only [tree209,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox209,?_,accepted_210 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox209)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox209).gradient 2).hi) denominator_positive).1 sign_209
private noncomputable def tree208 : TapeTree := .centered (candidateRows ibox208) (candidateRows (FixedTape.midBox ibox208))
attribute [irreducible] tree208
private theorem sign_208 : 2*denominator*(computed denominator (FixedTape.midBox ibox208)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox208).gradient k).lo.natAbs ((computed denominator ibox208).gradient k).hi.natAbs : Int)*((ibox208 k).hi-(ibox208 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox208
    (computed denominator ibox208) (computed denominator (FixedTape.midBox ibox208))
    (by decide +kernel)
private theorem midpoint_even_208 : ∀ k, 2 ∣ (ibox208 k).lo+(ibox208 k).hi := by decide +kernel
private theorem accepted_208 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox208) tree208 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox208 midpoint_even_208
  simp only [tree208,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox208,candidate_valid h (FixedTape.midBox ibox208),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox208 139 (FixedTape.rowsAux denominator ibox208 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox208) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_208
private noncomputable def tree207 : TapeTree := .face 2 false (candidateRows ibox207) tree208
attribute [irreducible] tree207
private theorem sign_207 : ((computed denominator ibox207).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_207 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox207) tree207 = true := by
  simp only [tree207,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox207,?_,accepted_208 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox207)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox207).gradient 2).hi) denominator_positive).1 sign_207
private noncomputable def tree206 : TapeTree := .centered (candidateRows ibox206) (candidateRows (FixedTape.midBox ibox206))
attribute [irreducible] tree206
private theorem sign_206 : 2*denominator*(computed denominator (FixedTape.midBox ibox206)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox206).gradient k).lo.natAbs ((computed denominator ibox206).gradient k).hi.natAbs : Int)*((ibox206 k).hi-(ibox206 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox206
    (computed denominator ibox206) (computed denominator (FixedTape.midBox ibox206))
    (by decide +kernel)
private theorem midpoint_even_206 : ∀ k, 2 ∣ (ibox206 k).lo+(ibox206 k).hi := by decide +kernel
private theorem accepted_206 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox206) tree206 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox206 midpoint_even_206
  simp only [tree206,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox206,candidate_valid h (FixedTape.midBox ibox206),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox206 139 (FixedTape.rowsAux denominator ibox206 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox206) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_206
private noncomputable def tree205 : TapeTree := .centered (candidateRows ibox205) (candidateRows (FixedTape.midBox ibox205))
attribute [irreducible] tree205
private theorem sign_205 : 2*denominator*(computed denominator (FixedTape.midBox ibox205)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox205).gradient k).lo.natAbs ((computed denominator ibox205).gradient k).hi.natAbs : Int)*((ibox205 k).hi-(ibox205 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox205
    (computed denominator ibox205) (computed denominator (FixedTape.midBox ibox205))
    (by decide +kernel)
private theorem midpoint_even_205 : ∀ k, 2 ∣ (ibox205 k).lo+(ibox205 k).hi := by decide +kernel
private theorem accepted_205 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox205) tree205 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox205 midpoint_even_205
  simp only [tree205,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox205,candidate_valid h (FixedTape.midBox ibox205),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox205 139 (FixedTape.rowsAux denominator ibox205 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox205) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_205
private noncomputable def tree204 : TapeTree := .split 1 (((8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree205 tree206
attribute [irreducible] tree204
private theorem accepted_204 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox204) tree204 = true := by
  simp only [tree204,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox204 1 (8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) false,decode_split denominator ibox204 1 (8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_205 h,accepted_206 h⟩
private noncomputable def tree203 : TapeTree := .split 2 (((26871878405145400401000294166348027513089855395282014775893977543915273580487639040000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree204 tree207
attribute [irreducible] tree203
private theorem accepted_203 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox203) tree203 = true := by
  simp only [tree203,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox203 2 (26871878405145400401000294166348027513089855395282014775893977543915273580487639040000000000000000000000000 : Int) false,decode_split denominator ibox203 2 (26871878405145400401000294166348027513089855395282014775893977543915273580487639040000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_204 h,accepted_207 h⟩
private noncomputable def tree202 : TapeTree := .split 2 (((27946753541351216417040305933001948613613449611093295366929736645671884523707144601600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree203 tree209
attribute [irreducible] tree202
private theorem accepted_202 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox202) tree202 = true := by
  simp only [tree202,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox202 2 (27946753541351216417040305933001948613613449611093295366929736645671884523707144601600000000000000000000000 : Int) false,decode_split denominator ibox202 2 (27946753541351216417040305933001948613613449611093295366929736645671884523707144601600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_203 h,accepted_209 h⟩
private noncomputable def tree201 : TapeTree := .split 1 (((17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree202 tree211
attribute [irreducible] tree201
private theorem accepted_201 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox201) tree201 = true := by
  simp only [tree201,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox201 1 (17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 : Int) false,decode_split denominator ibox201 1 (17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_202 h,accepted_211 h⟩
private noncomputable def tree200 : TapeTree := .face 3 false (candidateRows ibox200) tree201
attribute [irreducible] tree200
private theorem sign_200 : ((computed denominator ibox200).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_200 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox200) tree200 = true := by
  simp only [tree200,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox200,?_,accepted_201 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox200)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox200).gradient 3).hi) denominator_positive).1 sign_200
private noncomputable def tree199 : TapeTree := .split 2 (((30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree200 tree220
attribute [irreducible] tree199
private theorem accepted_199 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox199) tree199 = true := by
  simp only [tree199,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox199 2 (30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) false,decode_split denominator ibox199 2 (30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_200 h,accepted_220 h⟩
private noncomputable def tree198 : TapeTree := .centered (candidateRows ibox198) (candidateRows (FixedTape.midBox ibox198))
attribute [irreducible] tree198
private theorem sign_198 : 2*denominator*(computed denominator (FixedTape.midBox ibox198)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox198).gradient k).lo.natAbs ((computed denominator ibox198).gradient k).hi.natAbs : Int)*((ibox198 k).hi-(ibox198 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox198
    (computed denominator ibox198) (computed denominator (FixedTape.midBox ibox198))
    (by decide +kernel)
private theorem midpoint_even_198 : ∀ k, 2 ∣ (ibox198 k).lo+(ibox198 k).hi := by decide +kernel
private theorem accepted_198 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox198) tree198 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox198 midpoint_even_198
  simp only [tree198,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox198,candidate_valid h (FixedTape.midBox ibox198),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox198 139 (FixedTape.rowsAux denominator ibox198 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox198) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_198
private noncomputable def tree197 : TapeTree := .centered (candidateRows ibox197) (candidateRows (FixedTape.midBox ibox197))
attribute [irreducible] tree197
private theorem sign_197 : 2*denominator*(computed denominator (FixedTape.midBox ibox197)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox197).gradient k).lo.natAbs ((computed denominator ibox197).gradient k).hi.natAbs : Int)*((ibox197 k).hi-(ibox197 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox197
    (computed denominator ibox197) (computed denominator (FixedTape.midBox ibox197))
    (by decide +kernel)
private theorem midpoint_even_197 : ∀ k, 2 ∣ (ibox197 k).lo+(ibox197 k).hi := by decide +kernel
private theorem accepted_197 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox197) tree197 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox197 midpoint_even_197
  simp only [tree197,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox197,candidate_valid h (FixedTape.midBox ibox197),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox197 139 (FixedTape.rowsAux denominator ibox197 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox197) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_197
private noncomputable def tree196 : TapeTree := .split 2 (((24722128132733768368920270633040185312042666963659453593822459340402051694048627916800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree197 tree198
attribute [irreducible] tree196
private theorem accepted_196 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox196) tree196 = true := by
  simp only [tree196,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox196 2 (24722128132733768368920270633040185312042666963659453593822459340402051694048627916800000000000000000000000 : Int) false,decode_split denominator ibox196 2 (24722128132733768368920270633040185312042666963659453593822459340402051694048627916800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_197 h,accepted_198 h⟩
private noncomputable def tree195 : TapeTree := .centered (candidateRows ibox195) (candidateRows (FixedTape.midBox ibox195))
attribute [irreducible] tree195
private theorem sign_195 : 2*denominator*(computed denominator (FixedTape.midBox ibox195)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox195).gradient k).lo.natAbs ((computed denominator ibox195).gradient k).hi.natAbs : Int)*((ibox195 k).hi-(ibox195 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox195
    (computed denominator ibox195) (computed denominator (FixedTape.midBox ibox195))
    (by decide +kernel)
private theorem midpoint_even_195 : ∀ k, 2 ∣ (ibox195 k).lo+(ibox195 k).hi := by decide +kernel
private theorem accepted_195 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox195) tree195 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox195 midpoint_even_195
  simp only [tree195,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox195,candidate_valid h (FixedTape.midBox ibox195),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox195 139 (FixedTape.rowsAux denominator ibox195 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox195) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_195
private noncomputable def tree194 : TapeTree := .centered (candidateRows ibox194) (candidateRows (FixedTape.midBox ibox194))
attribute [irreducible] tree194
private theorem sign_194 : 2*denominator*(computed denominator (FixedTape.midBox ibox194)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox194).gradient k).lo.natAbs ((computed denominator ibox194).gradient k).hi.natAbs : Int)*((ibox194 k).hi-(ibox194 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox194
    (computed denominator ibox194) (computed denominator (FixedTape.midBox ibox194))
    (by decide +kernel)
private theorem midpoint_even_194 : ∀ k, 2 ∣ (ibox194 k).lo+(ibox194 k).hi := by decide +kernel
private theorem accepted_194 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox194) tree194 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox194 midpoint_even_194
  simp only [tree194,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox194,candidate_valid h (FixedTape.midBox ibox194),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox194 139 (FixedTape.rowsAux denominator ibox194 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox194) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_194
private noncomputable def tree193 : TapeTree := .split 2 (((24722128132733768368920270633040185312042666963659453593822459340402051694048627916800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree194 tree195
attribute [irreducible] tree193
private theorem accepted_193 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox193) tree193 = true := by
  simp only [tree193,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox193 2 (24722128132733768368920270633040185312042666963659453593822459340402051694048627916800000000000000000000000 : Int) false,decode_split denominator ibox193 2 (24722128132733768368920270633040185312042666963659453593822459340402051694048627916800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_194 h,accepted_195 h⟩
private noncomputable def tree192 : TapeTree := .split 1 (((25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree193 tree196
attribute [irreducible] tree192
private theorem accepted_192 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox192) tree192 = true := by
  simp only [tree192,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox192 1 (25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 : Int) false,decode_split denominator ibox192 1 (25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_193 h,accepted_196 h⟩
private noncomputable def tree191 : TapeTree := .centered (candidateRows ibox191) (candidateRows (FixedTape.midBox ibox191))
attribute [irreducible] tree191
private theorem sign_191 : 2*denominator*(computed denominator (FixedTape.midBox ibox191)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox191).gradient k).lo.natAbs ((computed denominator ibox191).gradient k).hi.natAbs : Int)*((ibox191 k).hi-(ibox191 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox191
    (computed denominator ibox191) (computed denominator (FixedTape.midBox ibox191))
    (by decide +kernel)
private theorem midpoint_even_191 : ∀ k, 2 ∣ (ibox191 k).lo+(ibox191 k).hi := by decide +kernel
private theorem accepted_191 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox191) tree191 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox191 midpoint_even_191
  simp only [tree191,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox191,candidate_valid h (FixedTape.midBox ibox191),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox191 139 (FixedTape.rowsAux denominator ibox191 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox191) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_191
private noncomputable def tree190 : TapeTree := .centered (candidateRows ibox190) (candidateRows (FixedTape.midBox ibox190))
attribute [irreducible] tree190
private theorem sign_190 : 2*denominator*(computed denominator (FixedTape.midBox ibox190)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox190).gradient k).lo.natAbs ((computed denominator ibox190).gradient k).hi.natAbs : Int)*((ibox190 k).hi-(ibox190 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox190
    (computed denominator ibox190) (computed denominator (FixedTape.midBox ibox190))
    (by decide +kernel)
private theorem midpoint_even_190 : ∀ k, 2 ∣ (ibox190 k).lo+(ibox190 k).hi := by decide +kernel
private theorem accepted_190 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox190) tree190 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox190 midpoint_even_190
  simp only [tree190,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox190,candidate_valid h (FixedTape.midBox ibox190),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox190 139 (FixedTape.rowsAux denominator ibox190 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox190) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_190
private noncomputable def tree189 : TapeTree := .split 1 (((30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree190 tree191
attribute [irreducible] tree189
private theorem accepted_189 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox189) tree189 = true := by
  simp only [tree189,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox189 1 (30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) false,decode_split denominator ibox189 1 (30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_190 h,accepted_191 h⟩
private noncomputable def tree188 : TapeTree := .centered (candidateRows ibox188) (candidateRows (FixedTape.midBox ibox188))
attribute [irreducible] tree188
private theorem sign_188 : 2*denominator*(computed denominator (FixedTape.midBox ibox188)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox188).gradient k).lo.natAbs ((computed denominator ibox188).gradient k).hi.natAbs : Int)*((ibox188 k).hi-(ibox188 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox188
    (computed denominator ibox188) (computed denominator (FixedTape.midBox ibox188))
    (by decide +kernel)
private theorem midpoint_even_188 : ∀ k, 2 ∣ (ibox188 k).lo+(ibox188 k).hi := by decide +kernel
private theorem accepted_188 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox188) tree188 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox188 midpoint_even_188
  simp only [tree188,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox188,candidate_valid h (FixedTape.midBox ibox188),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox188 139 (FixedTape.rowsAux denominator ibox188 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox188) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_188
private noncomputable def tree187 : TapeTree := .centered (candidateRows ibox187) (candidateRows (FixedTape.midBox ibox187))
attribute [irreducible] tree187
private theorem sign_187 : 2*denominator*(computed denominator (FixedTape.midBox ibox187)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox187).gradient k).lo.natAbs ((computed denominator ibox187).gradient k).hi.natAbs : Int)*((ibox187 k).hi-(ibox187 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox187
    (computed denominator ibox187) (computed denominator (FixedTape.midBox ibox187))
    (by decide +kernel)
private theorem midpoint_even_187 : ∀ k, 2 ∣ (ibox187 k).lo+(ibox187 k).hi := by decide +kernel
private theorem accepted_187 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox187) tree187 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox187 midpoint_even_187
  simp only [tree187,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox187,candidate_valid h (FixedTape.midBox ibox187),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox187 139 (FixedTape.rowsAux denominator ibox187 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox187) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_187
private noncomputable def tree186 : TapeTree := .split 2 (((22572377860322136336840247099732343110995478532036892411750941136888829807609616793600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree187 tree188
attribute [irreducible] tree186
private theorem accepted_186 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox186) tree186 = true := by
  simp only [tree186,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox186 2 (22572377860322136336840247099732343110995478532036892411750941136888829807609616793600000000000000000000000 : Int) false,decode_split denominator ibox186 2 (22572377860322136336840247099732343110995478532036892411750941136888829807609616793600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_187 h,accepted_188 h⟩
private noncomputable def tree185 : TapeTree := .split 1 (((25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree186 tree189
attribute [irreducible] tree185
private theorem accepted_185 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox185) tree185 = true := by
  simp only [tree185,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox185 1 (25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 : Int) false,decode_split denominator ibox185 1 (25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_186 h,accepted_189 h⟩
private noncomputable def tree184 : TapeTree := .split 2 (((23647252996527952352880258866386264211519072747848173002786700238645440750829122355200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree185 tree192
attribute [irreducible] tree184
private theorem accepted_184 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox184) tree184 = true := by
  simp only [tree184,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox184 2 (23647252996527952352880258866386264211519072747848173002786700238645440750829122355200000000000000000000000 : Int) false,decode_split denominator ibox184 2 (23647252996527952352880258866386264211519072747848173002786700238645440750829122355200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_185 h,accepted_192 h⟩
private noncomputable def tree183 : TapeTree := .centered (candidateRows ibox183) (candidateRows (FixedTape.midBox ibox183))
attribute [irreducible] tree183
private theorem sign_183 : 2*denominator*(computed denominator (FixedTape.midBox ibox183)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox183).gradient k).lo.natAbs ((computed denominator ibox183).gradient k).hi.natAbs : Int)*((ibox183 k).hi-(ibox183 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox183
    (computed denominator ibox183) (computed denominator (FixedTape.midBox ibox183))
    (by decide +kernel)
private theorem midpoint_even_183 : ∀ k, 2 ∣ (ibox183 k).lo+(ibox183 k).hi := by decide +kernel
private theorem accepted_183 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox183) tree183 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox183 midpoint_even_183
  simp only [tree183,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox183,candidate_valid h (FixedTape.midBox ibox183),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox183 139 (FixedTape.rowsAux denominator ibox183 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox183) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_183
private noncomputable def tree182 : TapeTree := .centered (candidateRows ibox182) (candidateRows (FixedTape.midBox ibox182))
attribute [irreducible] tree182
private theorem sign_182 : 2*denominator*(computed denominator (FixedTape.midBox ibox182)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox182).gradient k).lo.natAbs ((computed denominator ibox182).gradient k).hi.natAbs : Int)*((ibox182 k).hi-(ibox182 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox182
    (computed denominator ibox182) (computed denominator (FixedTape.midBox ibox182))
    (by decide +kernel)
private theorem midpoint_even_182 : ∀ k, 2 ∣ (ibox182 k).lo+(ibox182 k).hi := by decide +kernel
private theorem accepted_182 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox182) tree182 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox182 midpoint_even_182
  simp only [tree182,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox182,candidate_valid h (FixedTape.midBox ibox182),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox182 139 (FixedTape.rowsAux denominator ibox182 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox182) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_182
private noncomputable def tree181 : TapeTree := .split 2 (((24722128132733768368920270633040185312042666963659453593822459340402051694048627916800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree182 tree183
attribute [irreducible] tree181
private theorem accepted_181 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox181) tree181 = true := by
  simp only [tree181,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox181 2 (24722128132733768368920270633040185312042666963659453593822459340402051694048627916800000000000000000000000 : Int) false,decode_split denominator ibox181 2 (24722128132733768368920270633040185312042666963659453593822459340402051694048627916800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_182 h,accepted_183 h⟩
private noncomputable def tree180 : TapeTree := .centered (candidateRows ibox180) (candidateRows (FixedTape.midBox ibox180))
attribute [irreducible] tree180
private theorem sign_180 : 2*denominator*(computed denominator (FixedTape.midBox ibox180)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox180).gradient k).lo.natAbs ((computed denominator ibox180).gradient k).hi.natAbs : Int)*((ibox180 k).hi-(ibox180 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox180
    (computed denominator ibox180) (computed denominator (FixedTape.midBox ibox180))
    (by decide +kernel)
private theorem midpoint_even_180 : ∀ k, 2 ∣ (ibox180 k).lo+(ibox180 k).hi := by decide +kernel
private theorem accepted_180 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox180) tree180 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox180 midpoint_even_180
  simp only [tree180,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox180,candidate_valid h (FixedTape.midBox ibox180),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox180 139 (FixedTape.rowsAux denominator ibox180 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox180) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_180
private noncomputable def tree179 : TapeTree := .centered (candidateRows ibox179) (candidateRows (FixedTape.midBox ibox179))
attribute [irreducible] tree179
private theorem sign_179 : 2*denominator*(computed denominator (FixedTape.midBox ibox179)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox179).gradient k).lo.natAbs ((computed denominator ibox179).gradient k).hi.natAbs : Int)*((ibox179 k).hi-(ibox179 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox179
    (computed denominator ibox179) (computed denominator (FixedTape.midBox ibox179))
    (by decide +kernel)
private theorem midpoint_even_179 : ∀ k, 2 ∣ (ibox179 k).lo+(ibox179 k).hi := by decide +kernel
private theorem accepted_179 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox179) tree179 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox179 midpoint_even_179
  simp only [tree179,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox179,candidate_valid h (FixedTape.midBox ibox179),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox179 139 (FixedTape.rowsAux denominator ibox179 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox179) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_179
private noncomputable def tree178 : TapeTree := .split 2 (((24722128132733768368920270633040185312042666963659453593822459340402051694048627916800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree179 tree180
attribute [irreducible] tree178
private theorem accepted_178 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox178) tree178 = true := by
  simp only [tree178,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox178 2 (24722128132733768368920270633040185312042666963659453593822459340402051694048627916800000000000000000000000 : Int) false,decode_split denominator ibox178 2 (24722128132733768368920270633040185312042666963659453593822459340402051694048627916800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_179 h,accepted_180 h⟩
private noncomputable def tree177 : TapeTree := .split 1 (((8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree178 tree181
attribute [irreducible] tree177
private theorem accepted_177 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox177) tree177 = true := by
  simp only [tree177,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox177 1 (8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) false,decode_split denominator ibox177 1 (8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_178 h,accepted_181 h⟩
private noncomputable def tree176 : TapeTree := .centered (candidateRows ibox176) (candidateRows (FixedTape.midBox ibox176))
attribute [irreducible] tree176
private theorem sign_176 : 2*denominator*(computed denominator (FixedTape.midBox ibox176)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox176).gradient k).lo.natAbs ((computed denominator ibox176).gradient k).hi.natAbs : Int)*((ibox176 k).hi-(ibox176 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox176
    (computed denominator ibox176) (computed denominator (FixedTape.midBox ibox176))
    (by decide +kernel)
private theorem midpoint_even_176 : ∀ k, 2 ∣ (ibox176 k).lo+(ibox176 k).hi := by decide +kernel
private theorem accepted_176 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox176) tree176 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox176 midpoint_even_176
  simp only [tree176,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox176,candidate_valid h (FixedTape.midBox ibox176),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox176 139 (FixedTape.rowsAux denominator ibox176 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox176) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_176
private noncomputable def tree175 : TapeTree := .centered (candidateRows ibox175) (candidateRows (FixedTape.midBox ibox175))
attribute [irreducible] tree175
private theorem sign_175 : 2*denominator*(computed denominator (FixedTape.midBox ibox175)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox175).gradient k).lo.natAbs ((computed denominator ibox175).gradient k).hi.natAbs : Int)*((ibox175 k).hi-(ibox175 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox175
    (computed denominator ibox175) (computed denominator (FixedTape.midBox ibox175))
    (by decide +kernel)
private theorem midpoint_even_175 : ∀ k, 2 ∣ (ibox175 k).lo+(ibox175 k).hi := by decide +kernel
private theorem accepted_175 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox175) tree175 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox175 midpoint_even_175
  simp only [tree175,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox175,candidate_valid h (FixedTape.midBox ibox175),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox175 139 (FixedTape.rowsAux denominator ibox175 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox175) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_175
private noncomputable def tree174 : TapeTree := .split 2 (((22572377860322136336840247099732343110995478532036892411750941136888829807609616793600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree175 tree176
attribute [irreducible] tree174
private theorem accepted_174 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox174) tree174 = true := by
  simp only [tree174,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox174 2 (22572377860322136336840247099732343110995478532036892411750941136888829807609616793600000000000000000000000 : Int) false,decode_split denominator ibox174 2 (22572377860322136336840247099732343110995478532036892411750941136888829807609616793600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_175 h,accepted_176 h⟩
private noncomputable def tree173 : TapeTree := .centered (candidateRows ibox173) (candidateRows (FixedTape.midBox ibox173))
attribute [irreducible] tree173
private theorem sign_173 : 2*denominator*(computed denominator (FixedTape.midBox ibox173)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox173).gradient k).lo.natAbs ((computed denominator ibox173).gradient k).hi.natAbs : Int)*((ibox173 k).hi-(ibox173 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox173
    (computed denominator ibox173) (computed denominator (FixedTape.midBox ibox173))
    (by decide +kernel)
private theorem midpoint_even_173 : ∀ k, 2 ∣ (ibox173 k).lo+(ibox173 k).hi := by decide +kernel
private theorem accepted_173 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox173) tree173 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox173 midpoint_even_173
  simp only [tree173,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox173,candidate_valid h (FixedTape.midBox ibox173),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox173 139 (FixedTape.rowsAux denominator ibox173 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox173) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_173
private noncomputable def tree172 : TapeTree := .centered (candidateRows ibox172) (candidateRows (FixedTape.midBox ibox172))
attribute [irreducible] tree172
private theorem sign_172 : 2*denominator*(computed denominator (FixedTape.midBox ibox172)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox172).gradient k).lo.natAbs ((computed denominator ibox172).gradient k).hi.natAbs : Int)*((ibox172 k).hi-(ibox172 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox172
    (computed denominator ibox172) (computed denominator (FixedTape.midBox ibox172))
    (by decide +kernel)
private theorem midpoint_even_172 : ∀ k, 2 ∣ (ibox172 k).lo+(ibox172 k).hi := by decide +kernel
private theorem accepted_172 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox172) tree172 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox172 midpoint_even_172
  simp only [tree172,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox172,candidate_valid h (FixedTape.midBox ibox172),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox172 139 (FixedTape.rowsAux denominator ibox172 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox172) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_172
private noncomputable def tree171 : TapeTree := .split 1 (((4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree172 tree173
attribute [irreducible] tree171
private theorem accepted_171 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox171) tree171 = true := by
  simp only [tree171,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox171 1 (4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 : Int) false,decode_split denominator ibox171 1 (4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_172 h,accepted_173 h⟩
private noncomputable def tree170 : TapeTree := .split 1 (((8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree171 tree174
attribute [irreducible] tree170
private theorem accepted_170 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox170) tree170 = true := by
  simp only [tree170,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox170 1 (8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) false,decode_split denominator ibox170 1 (8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_171 h,accepted_174 h⟩
private noncomputable def tree169 : TapeTree := .split 2 (((23647252996527952352880258866386264211519072747848173002786700238645440750829122355200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree170 tree177
attribute [irreducible] tree169
private theorem accepted_169 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox169) tree169 = true := by
  simp only [tree169,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox169 2 (23647252996527952352880258866386264211519072747848173002786700238645440750829122355200000000000000000000000 : Int) false,decode_split denominator ibox169 2 (23647252996527952352880258866386264211519072747848173002786700238645440750829122355200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_170 h,accepted_177 h⟩
private noncomputable def tree168 : TapeTree := .split 1 (((17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree169 tree184
attribute [irreducible] tree168
private theorem accepted_168 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox168) tree168 = true := by
  simp only [tree168,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox168 1 (17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 : Int) false,decode_split denominator ibox168 1 (17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_169 h,accepted_184 h⟩
private noncomputable def tree167 : TapeTree := .centered (candidateRows ibox167) (candidateRows (FixedTape.midBox ibox167))
attribute [irreducible] tree167
private theorem sign_167 : 2*denominator*(computed denominator (FixedTape.midBox ibox167)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox167).gradient k).lo.natAbs ((computed denominator ibox167).gradient k).hi.natAbs : Int)*((ibox167 k).hi-(ibox167 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox167
    (computed denominator ibox167) (computed denominator (FixedTape.midBox ibox167))
    (by decide +kernel)
private theorem midpoint_even_167 : ∀ k, 2 ∣ (ibox167 k).lo+(ibox167 k).hi := by decide +kernel
private theorem accepted_167 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox167) tree167 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox167 midpoint_even_167
  simp only [tree167,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox167,candidate_valid h (FixedTape.midBox ibox167),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox167 139 (FixedTape.rowsAux denominator ibox167 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox167) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_167
private noncomputable def tree166 : TapeTree := .centered (candidateRows ibox166) (candidateRows (FixedTape.midBox ibox166))
attribute [irreducible] tree166
private theorem sign_166 : 2*denominator*(computed denominator (FixedTape.midBox ibox166)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox166).gradient k).lo.natAbs ((computed denominator ibox166).gradient k).hi.natAbs : Int)*((ibox166 k).hi-(ibox166 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox166
    (computed denominator ibox166) (computed denominator (FixedTape.midBox ibox166))
    (by decide +kernel)
private theorem midpoint_even_166 : ∀ k, 2 ∣ (ibox166 k).lo+(ibox166 k).hi := by decide +kernel
private theorem accepted_166 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox166) tree166 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox166 midpoint_even_166
  simp only [tree166,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox166,candidate_valid h (FixedTape.midBox ibox166),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox166 139 (FixedTape.rowsAux denominator ibox166 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox166) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_166
private noncomputable def tree165 : TapeTree := .split 1 (((30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree166 tree167
attribute [irreducible] tree165
private theorem accepted_165 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox165) tree165 = true := by
  simp only [tree165,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox165 1 (30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) false,decode_split denominator ibox165 1 (30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_166 h,accepted_167 h⟩
private noncomputable def tree164 : TapeTree := .centered (candidateRows ibox164) (candidateRows (FixedTape.midBox ibox164))
attribute [irreducible] tree164
private theorem sign_164 : 2*denominator*(computed denominator (FixedTape.midBox ibox164)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox164).gradient k).lo.natAbs ((computed denominator ibox164).gradient k).hi.natAbs : Int)*((ibox164 k).hi-(ibox164 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox164
    (computed denominator ibox164) (computed denominator (FixedTape.midBox ibox164))
    (by decide +kernel)
private theorem midpoint_even_164 : ∀ k, 2 ∣ (ibox164 k).lo+(ibox164 k).hi := by decide +kernel
private theorem accepted_164 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox164) tree164 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox164 midpoint_even_164
  simp only [tree164,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox164,candidate_valid h (FixedTape.midBox ibox164),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox164 139 (FixedTape.rowsAux denominator ibox164 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox164) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_164
private noncomputable def tree163 : TapeTree := .centered (candidateRows ibox163) (candidateRows (FixedTape.midBox ibox163))
attribute [irreducible] tree163
private theorem sign_163 : 2*denominator*(computed denominator (FixedTape.midBox ibox163)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox163).gradient k).lo.natAbs ((computed denominator ibox163).gradient k).hi.natAbs : Int)*((ibox163 k).hi-(ibox163 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox163
    (computed denominator ibox163) (computed denominator (FixedTape.midBox ibox163))
    (by decide +kernel)
private theorem midpoint_even_163 : ∀ k, 2 ∣ (ibox163 k).lo+(ibox163 k).hi := by decide +kernel
private theorem accepted_163 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox163) tree163 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox163 midpoint_even_163
  simp only [tree163,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox163,candidate_valid h (FixedTape.midBox ibox163),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox163 139 (FixedTape.rowsAux denominator ibox163 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox163) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_163
private noncomputable def tree162 : TapeTree := .split 1 (((30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree163 tree164
attribute [irreducible] tree162
private theorem accepted_162 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox162) tree162 = true := by
  simp only [tree162,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox162 1 (30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) false,decode_split denominator ibox162 1 (30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_163 h,accepted_164 h⟩
private noncomputable def tree161 : TapeTree := .split 2 (((19347752451704688288720211799770579809424695884603050638643663831618996977951100108800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree162 tree165
attribute [irreducible] tree161
private theorem accepted_161 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox161) tree161 = true := by
  simp only [tree161,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox161 2 (19347752451704688288720211799770579809424695884603050638643663831618996977951100108800000000000000000000000 : Int) false,decode_split denominator ibox161 2 (19347752451704688288720211799770579809424695884603050638643663831618996977951100108800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_162 h,accepted_165 h⟩
private noncomputable def tree160 : TapeTree := .centered (candidateRows ibox160) (candidateRows (FixedTape.midBox ibox160))
attribute [irreducible] tree160
private theorem sign_160 : 2*denominator*(computed denominator (FixedTape.midBox ibox160)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox160).gradient k).lo.natAbs ((computed denominator ibox160).gradient k).hi.natAbs : Int)*((ibox160 k).hi-(ibox160 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox160
    (computed denominator ibox160) (computed denominator (FixedTape.midBox ibox160))
    (by decide +kernel)
private theorem midpoint_even_160 : ∀ k, 2 ∣ (ibox160 k).lo+(ibox160 k).hi := by decide +kernel
private theorem accepted_160 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox160) tree160 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox160 midpoint_even_160
  simp only [tree160,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox160,candidate_valid h (FixedTape.midBox ibox160),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox160 139 (FixedTape.rowsAux denominator ibox160 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox160) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_160
private noncomputable def tree159 : TapeTree := .centered (candidateRows ibox159) (candidateRows (FixedTape.midBox ibox159))
attribute [irreducible] tree159
private theorem sign_159 : 2*denominator*(computed denominator (FixedTape.midBox ibox159)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox159).gradient k).lo.natAbs ((computed denominator ibox159).gradient k).hi.natAbs : Int)*((ibox159 k).hi-(ibox159 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox159
    (computed denominator ibox159) (computed denominator (FixedTape.midBox ibox159))
    (by decide +kernel)
private theorem midpoint_even_159 : ∀ k, 2 ∣ (ibox159 k).lo+(ibox159 k).hi := by decide +kernel
private theorem accepted_159 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox159) tree159 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox159 midpoint_even_159
  simp only [tree159,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox159,candidate_valid h (FixedTape.midBox ibox159),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox159 139 (FixedTape.rowsAux denominator ibox159 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox159) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_159
private noncomputable def tree158 : TapeTree := .split 1 (((21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree159 tree160
attribute [irreducible] tree158
private theorem accepted_158 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox158) tree158 = true := by
  simp only [tree158,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox158 1 (21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 : Int) false,decode_split denominator ibox158 1 (21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_159 h,accepted_160 h⟩
private noncomputable def tree157 : TapeTree := .centered (candidateRows ibox157) (candidateRows (FixedTape.midBox ibox157))
attribute [irreducible] tree157
private theorem sign_157 : 2*denominator*(computed denominator (FixedTape.midBox ibox157)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox157).gradient k).lo.natAbs ((computed denominator ibox157).gradient k).hi.natAbs : Int)*((ibox157 k).hi-(ibox157 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox157
    (computed denominator ibox157) (computed denominator (FixedTape.midBox ibox157))
    (by decide +kernel)
private theorem midpoint_even_157 : ∀ k, 2 ∣ (ibox157 k).lo+(ibox157 k).hi := by decide +kernel
private theorem accepted_157 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox157) tree157 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox157 midpoint_even_157
  simp only [tree157,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox157,candidate_valid h (FixedTape.midBox ibox157),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox157 139 (FixedTape.rowsAux denominator ibox157 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox157) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_157
private noncomputable def tree156 : TapeTree := .centered (candidateRows ibox156) (candidateRows (FixedTape.midBox ibox156))
attribute [irreducible] tree156
private theorem sign_156 : 2*denominator*(computed denominator (FixedTape.midBox ibox156)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox156).gradient k).lo.natAbs ((computed denominator ibox156).gradient k).hi.natAbs : Int)*((ibox156 k).hi-(ibox156 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox156
    (computed denominator ibox156) (computed denominator (FixedTape.midBox ibox156))
    (by decide +kernel)
private theorem midpoint_even_156 : ∀ k, 2 ∣ (ibox156 k).lo+(ibox156 k).hi := by decide +kernel
private theorem accepted_156 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox156) tree156 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox156 midpoint_even_156
  simp only [tree156,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox156,candidate_valid h (FixedTape.midBox ibox156),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox156 139 (FixedTape.rowsAux denominator ibox156 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox156) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_156
private noncomputable def tree155 : TapeTree := .split 1 (((21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree156 tree157
attribute [irreducible] tree155
private theorem accepted_155 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox155) tree155 = true := by
  simp only [tree155,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox155 1 (21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 : Int) false,decode_split denominator ibox155 1 (21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_156 h,accepted_157 h⟩
private noncomputable def tree154 : TapeTree := .split 2 (((19347752451704688288720211799770579809424695884603050638643663831618996977951100108800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree155 tree158
attribute [irreducible] tree154
private theorem accepted_154 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox154) tree154 = true := by
  simp only [tree154,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox154 2 (19347752451704688288720211799770579809424695884603050638643663831618996977951100108800000000000000000000000 : Int) false,decode_split denominator ibox154 2 (19347752451704688288720211799770579809424695884603050638643663831618996977951100108800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_155 h,accepted_158 h⟩
private noncomputable def tree153 : TapeTree := .split 1 (((25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree154 tree161
attribute [irreducible] tree153
private theorem accepted_153 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox153) tree153 = true := by
  simp only [tree153,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox153 1 (25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 : Int) false,decode_split denominator ibox153 1 (25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_154 h,accepted_161 h⟩
private noncomputable def tree152 : TapeTree := .centered (candidateRows ibox152) (candidateRows (FixedTape.midBox ibox152))
attribute [irreducible] tree152
private theorem sign_152 : 2*denominator*(computed denominator (FixedTape.midBox ibox152)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox152).gradient k).lo.natAbs ((computed denominator ibox152).gradient k).hi.natAbs : Int)*((ibox152 k).hi-(ibox152 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox152
    (computed denominator ibox152) (computed denominator (FixedTape.midBox ibox152))
    (by decide +kernel)
private theorem midpoint_even_152 : ∀ k, 2 ∣ (ibox152 k).lo+(ibox152 k).hi := by decide +kernel
private theorem accepted_152 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox152) tree152 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox152 midpoint_even_152
  simp only [tree152,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox152,candidate_valid h (FixedTape.midBox ibox152),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox152 139 (FixedTape.rowsAux denominator ibox152 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox152) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_152
private noncomputable def tree151 : TapeTree := .centered (candidateRows ibox151) (candidateRows (FixedTape.midBox ibox151))
attribute [irreducible] tree151
private theorem sign_151 : 2*denominator*(computed denominator (FixedTape.midBox ibox151)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox151).gradient k).lo.natAbs ((computed denominator ibox151).gradient k).hi.natAbs : Int)*((ibox151 k).hi-(ibox151 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox151
    (computed denominator ibox151) (computed denominator (FixedTape.midBox ibox151))
    (by decide +kernel)
private theorem midpoint_even_151 : ∀ k, 2 ∣ (ibox151 k).lo+(ibox151 k).hi := by decide +kernel
private theorem accepted_151 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox151) tree151 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox151 midpoint_even_151
  simp only [tree151,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox151,candidate_valid h (FixedTape.midBox ibox151),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox151 139 (FixedTape.rowsAux denominator ibox151 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox151) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_151
private noncomputable def tree150 : TapeTree := .split 1 (((12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree151 tree152
attribute [irreducible] tree150
private theorem accepted_150 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox150) tree150 = true := by
  simp only [tree150,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox150 1 (12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 : Int) false,decode_split denominator ibox150 1 (12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_151 h,accepted_152 h⟩
private noncomputable def tree149 : TapeTree := .centered (candidateRows ibox149) (candidateRows (FixedTape.midBox ibox149))
attribute [irreducible] tree149
private theorem sign_149 : 2*denominator*(computed denominator (FixedTape.midBox ibox149)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox149).gradient k).lo.natAbs ((computed denominator ibox149).gradient k).hi.natAbs : Int)*((ibox149 k).hi-(ibox149 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox149
    (computed denominator ibox149) (computed denominator (FixedTape.midBox ibox149))
    (by decide +kernel)
private theorem midpoint_even_149 : ∀ k, 2 ∣ (ibox149 k).lo+(ibox149 k).hi := by decide +kernel
private theorem accepted_149 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox149) tree149 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox149 midpoint_even_149
  simp only [tree149,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox149,candidate_valid h (FixedTape.midBox ibox149),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox149 139 (FixedTape.rowsAux denominator ibox149 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox149) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_149
private noncomputable def tree148 : TapeTree := .split 2 (((19347752451704688288720211799770579809424695884603050638643663831618996977951100108800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree149 tree150
attribute [irreducible] tree148
private theorem accepted_148 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox148) tree148 = true := by
  simp only [tree148,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox148 2 (19347752451704688288720211799770579809424695884603050638643663831618996977951100108800000000000000000000000 : Int) false,decode_split denominator ibox148 2 (19347752451704688288720211799770579809424695884603050638643663831618996977951100108800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_149 h,accepted_150 h⟩
private noncomputable def tree147 : TapeTree := .centered (candidateRows ibox147) (candidateRows (FixedTape.midBox ibox147))
attribute [irreducible] tree147
private theorem sign_147 : 2*denominator*(computed denominator (FixedTape.midBox ibox147)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox147).gradient k).lo.natAbs ((computed denominator ibox147).gradient k).hi.natAbs : Int)*((ibox147 k).hi-(ibox147 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox147
    (computed denominator ibox147) (computed denominator (FixedTape.midBox ibox147))
    (by decide +kernel)
private theorem midpoint_even_147 : ∀ k, 2 ∣ (ibox147 k).lo+(ibox147 k).hi := by decide +kernel
private theorem accepted_147 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox147) tree147 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox147 midpoint_even_147
  simp only [tree147,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox147,candidate_valid h (FixedTape.midBox ibox147),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox147 139 (FixedTape.rowsAux denominator ibox147 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox147) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_147
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
private noncomputable def tree145 : TapeTree := .split 1 (((4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree146 tree147
attribute [irreducible] tree145
private theorem accepted_145 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox145) tree145 = true := by
  simp only [tree145,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox145 1 (4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 : Int) false,decode_split denominator ibox145 1 (4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_146 h,accepted_147 h⟩
private noncomputable def tree144 : TapeTree := .centered (candidateRows ibox144) (candidateRows (FixedTape.midBox ibox144))
attribute [irreducible] tree144
private theorem sign_144 : 2*denominator*(computed denominator (FixedTape.midBox ibox144)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox144).gradient k).lo.natAbs ((computed denominator ibox144).gradient k).hi.natAbs : Int)*((ibox144 k).hi-(ibox144 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox144
    (computed denominator ibox144) (computed denominator (FixedTape.midBox ibox144))
    (by decide +kernel)
private theorem midpoint_even_144 : ∀ k, 2 ∣ (ibox144 k).lo+(ibox144 k).hi := by decide +kernel
private theorem accepted_144 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox144) tree144 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox144 midpoint_even_144
  simp only [tree144,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox144,candidate_valid h (FixedTape.midBox ibox144),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox144 139 (FixedTape.rowsAux denominator ibox144 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox144) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_144
private noncomputable def tree143 : TapeTree := .split 2 (((19347752451704688288720211799770579809424695884603050638643663831618996977951100108800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree144 tree145
attribute [irreducible] tree143
private theorem accepted_143 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox143) tree143 = true := by
  simp only [tree143,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox143 2 (19347752451704688288720211799770579809424695884603050638643663831618996977951100108800000000000000000000000 : Int) false,decode_split denominator ibox143 2 (19347752451704688288720211799770579809424695884603050638643663831618996977951100108800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_144 h,accepted_145 h⟩
private noncomputable def tree142 : TapeTree := .split 1 (((8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree143 tree148
attribute [irreducible] tree142
private theorem accepted_142 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox142) tree142 = true := by
  simp only [tree142,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox142 1 (8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) false,decode_split denominator ibox142 1 (8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_143 h,accepted_148 h⟩
private noncomputable def tree141 : TapeTree := .split 1 (((17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree142 tree153
attribute [irreducible] tree141
private theorem accepted_141 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox141) tree141 = true := by
  simp only [tree141,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox141 1 (17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 : Int) false,decode_split denominator ibox141 1 (17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_142 h,accepted_153 h⟩
private noncomputable def tree140 : TapeTree := .split 2 (((21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree141 tree168
attribute [irreducible] tree140
private theorem accepted_140 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox140) tree140 = true := by
  simp only [tree140,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox140 2 (21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 : Int) false,decode_split denominator ibox140 2 (21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_141 h,accepted_168 h⟩
private noncomputable def tree139 : TapeTree := .face 3 false (candidateRows ibox139) tree140
attribute [irreducible] tree139
private theorem sign_139 : ((computed denominator ibox139).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_139 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox139) tree139 = true := by
  simp only [tree139,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox139,?_,accepted_140 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox139)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox139).gradient 3).hi) denominator_positive).1 sign_139
private noncomputable def tree138 : TapeTree := .split 2 (((25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree139 tree199
attribute [irreducible] tree138
private theorem accepted_138 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox138) tree138 = true := by
  simp only [tree138,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox138 2 (25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 : Int) false,decode_split denominator ibox138 2 (25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_139 h,accepted_199 h⟩
private noncomputable def tree137 : TapeTree := .centered (candidateRows ibox137) (candidateRows (FixedTape.midBox ibox137))
attribute [irreducible] tree137
private theorem sign_137 : 2*denominator*(computed denominator (FixedTape.midBox ibox137)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox137).gradient k).lo.natAbs ((computed denominator ibox137).gradient k).hi.natAbs : Int)*((ibox137 k).hi-(ibox137 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox137
    (computed denominator ibox137) (computed denominator (FixedTape.midBox ibox137))
    (by decide +kernel)
private theorem midpoint_even_137 : ∀ k, 2 ∣ (ibox137 k).lo+(ibox137 k).hi := by decide +kernel
private theorem accepted_137 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox137) tree137 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox137 midpoint_even_137
  simp only [tree137,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox137,candidate_valid h (FixedTape.midBox ibox137),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox137 139 (FixedTape.rowsAux denominator ibox137 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox137) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_137
private noncomputable def tree136 : TapeTree := .centered (candidateRows ibox136) (candidateRows (FixedTape.midBox ibox136))
attribute [irreducible] tree136
private theorem sign_136 : 2*denominator*(computed denominator (FixedTape.midBox ibox136)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox136).gradient k).lo.natAbs ((computed denominator ibox136).gradient k).hi.natAbs : Int)*((ibox136 k).hi-(ibox136 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox136
    (computed denominator ibox136) (computed denominator (FixedTape.midBox ibox136))
    (by decide +kernel)
private theorem midpoint_even_136 : ∀ k, 2 ∣ (ibox136 k).lo+(ibox136 k).hi := by decide +kernel
private theorem accepted_136 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox136) tree136 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox136 midpoint_even_136
  simp only [tree136,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox136,candidate_valid h (FixedTape.midBox ibox136),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox136 139 (FixedTape.rowsAux denominator ibox136 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox136) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_136
private noncomputable def tree135 : TapeTree := .split 0 (((24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) : ℚ)/(denominator : ℚ)) tree136 tree137
attribute [irreducible] tree135
private theorem accepted_135 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox135) tree135 = true := by
  simp only [tree135,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox135 0 (24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) false,decode_split denominator ibox135 0 (24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_136 h,accepted_137 h⟩
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
private noncomputable def tree133 : TapeTree := .split 1 (((30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree134 tree135
attribute [irreducible] tree133
private theorem accepted_133 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox133) tree133 = true := by
  simp only [tree133,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox133 1 (30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) false,decode_split denominator ibox133 1 (30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_134 h,accepted_135 h⟩
private noncomputable def tree132 : TapeTree := .centered (candidateRows ibox132) (candidateRows (FixedTape.midBox ibox132))
attribute [irreducible] tree132
private theorem sign_132 : 2*denominator*(computed denominator (FixedTape.midBox ibox132)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox132).gradient k).lo.natAbs ((computed denominator ibox132).gradient k).hi.natAbs : Int)*((ibox132 k).hi-(ibox132 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox132
    (computed denominator ibox132) (computed denominator (FixedTape.midBox ibox132))
    (by decide +kernel)
private theorem midpoint_even_132 : ∀ k, 2 ∣ (ibox132 k).lo+(ibox132 k).hi := by decide +kernel
private theorem accepted_132 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox132) tree132 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox132 midpoint_even_132
  simp only [tree132,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox132,candidate_valid h (FixedTape.midBox ibox132),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox132 139 (FixedTape.rowsAux denominator ibox132 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox132) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_132
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
private noncomputable def tree130 : TapeTree := .split 0 (((24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) : ℚ)/(denominator : ℚ)) tree131 tree132
attribute [irreducible] tree130
private theorem accepted_130 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox130) tree130 = true := by
  simp only [tree130,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox130 0 (24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) false,decode_split denominator ibox130 0 (24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_131 h,accepted_132 h⟩
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
private noncomputable def tree128 : TapeTree := .split 1 (((30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree129 tree130
attribute [irreducible] tree128
private theorem accepted_128 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox128) tree128 = true := by
  simp only [tree128,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox128 1 (30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) false,decode_split denominator ibox128 1 (30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_129 h,accepted_130 h⟩
private noncomputable def tree127 : TapeTree := .split 2 (((15048251906881424224560164733154895407330319021357928274500627424592553205073077862400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree128 tree133
attribute [irreducible] tree127
private theorem accepted_127 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox127) tree127 = true := by
  simp only [tree127,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox127 2 (15048251906881424224560164733154895407330319021357928274500627424592553205073077862400000000000000000000000 : Int) false,decode_split denominator ibox127 2 (15048251906881424224560164733154895407330319021357928274500627424592553205073077862400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_128 h,accepted_133 h⟩
private noncomputable def tree126 : TapeTree := .centered (candidateRows ibox126) (candidateRows (FixedTape.midBox ibox126))
attribute [irreducible] tree126
private theorem sign_126 : 2*denominator*(computed denominator (FixedTape.midBox ibox126)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox126).gradient k).lo.natAbs ((computed denominator ibox126).gradient k).hi.natAbs : Int)*((ibox126 k).hi-(ibox126 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox126
    (computed denominator ibox126) (computed denominator (FixedTape.midBox ibox126))
    (by decide +kernel)
private theorem midpoint_even_126 : ∀ k, 2 ∣ (ibox126 k).lo+(ibox126 k).hi := by decide +kernel
private theorem accepted_126 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox126) tree126 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox126 midpoint_even_126
  simp only [tree126,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox126,candidate_valid h (FixedTape.midBox ibox126),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox126 139 (FixedTape.rowsAux denominator ibox126 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox126) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_126
private noncomputable def tree125 : TapeTree := .centered (candidateRows ibox125) (candidateRows (FixedTape.midBox ibox125))
attribute [irreducible] tree125
private theorem sign_125 : 2*denominator*(computed denominator (FixedTape.midBox ibox125)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox125).gradient k).lo.natAbs ((computed denominator ibox125).gradient k).hi.natAbs : Int)*((ibox125 k).hi-(ibox125 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox125
    (computed denominator ibox125) (computed denominator (FixedTape.midBox ibox125))
    (by decide +kernel)
private theorem midpoint_even_125 : ∀ k, 2 ∣ (ibox125 k).lo+(ibox125 k).hi := by decide +kernel
private theorem accepted_125 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox125) tree125 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox125 midpoint_even_125
  simp only [tree125,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox125,candidate_valid h (FixedTape.midBox ibox125),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox125 139 (FixedTape.rowsAux denominator ibox125 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox125) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_125
private noncomputable def tree124 : TapeTree := .split 0 (((24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) : ℚ)/(denominator : ℚ)) tree125 tree126
attribute [irreducible] tree124
private theorem accepted_124 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox124) tree124 = true := by
  simp only [tree124,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox124 0 (24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) false,decode_split denominator ibox124 0 (24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_125 h,accepted_126 h⟩
private noncomputable def tree123 : TapeTree := .centered (candidateRows ibox123) (candidateRows (FixedTape.midBox ibox123))
attribute [irreducible] tree123
private theorem sign_123 : 2*denominator*(computed denominator (FixedTape.midBox ibox123)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox123).gradient k).lo.natAbs ((computed denominator ibox123).gradient k).hi.natAbs : Int)*((ibox123 k).hi-(ibox123 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox123
    (computed denominator ibox123) (computed denominator (FixedTape.midBox ibox123))
    (by decide +kernel)
private theorem midpoint_even_123 : ∀ k, 2 ∣ (ibox123 k).lo+(ibox123 k).hi := by decide +kernel
private theorem accepted_123 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox123) tree123 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox123 midpoint_even_123
  simp only [tree123,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox123,candidate_valid h (FixedTape.midBox ibox123),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox123 139 (FixedTape.rowsAux denominator ibox123 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox123) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_123
private noncomputable def tree122 : TapeTree := .split 1 (((32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree123 tree124
attribute [irreducible] tree122
private theorem accepted_122 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox122) tree122 = true := by
  simp only [tree122,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox122 1 (32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 : Int) false,decode_split denominator ibox122 1 (32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_123 h,accepted_124 h⟩
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
private noncomputable def tree119 : TapeTree := .split 0 (((24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) : ℚ)/(denominator : ℚ)) tree120 tree121
attribute [irreducible] tree119
private theorem accepted_119 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox119) tree119 = true := by
  simp only [tree119,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox119 0 (24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) false,decode_split denominator ibox119 0 (24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) true]
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
private noncomputable def tree117 : TapeTree := .split 1 (((32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree118 tree119
attribute [irreducible] tree117
private theorem accepted_117 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox117) tree117 = true := by
  simp only [tree117,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox117 1 (32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 : Int) false,decode_split denominator ibox117 1 (32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_118 h,accepted_119 h⟩
private noncomputable def tree116 : TapeTree := .split 2 (((10748751362058160160400117666539211005235942158112805910357591017566109432195055616000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree117 tree122
attribute [irreducible] tree116
private theorem accepted_116 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox116) tree116 = true := by
  simp only [tree116,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox116 2 (10748751362058160160400117666539211005235942158112805910357591017566109432195055616000000000000000000000000 : Int) false,decode_split denominator ibox116 2 (10748751362058160160400117666539211005235942158112805910357591017566109432195055616000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_117 h,accepted_122 h⟩
private noncomputable def tree115 : TapeTree := .centered (candidateRows ibox115) (candidateRows (FixedTape.midBox ibox115))
attribute [irreducible] tree115
private theorem sign_115 : 2*denominator*(computed denominator (FixedTape.midBox ibox115)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox115).gradient k).lo.natAbs ((computed denominator ibox115).gradient k).hi.natAbs : Int)*((ibox115 k).hi-(ibox115 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox115
    (computed denominator ibox115) (computed denominator (FixedTape.midBox ibox115))
    (by decide +kernel)
private theorem midpoint_even_115 : ∀ k, 2 ∣ (ibox115 k).lo+(ibox115 k).hi := by decide +kernel
private theorem accepted_115 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox115) tree115 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox115 midpoint_even_115
  simp only [tree115,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox115,candidate_valid h (FixedTape.midBox ibox115),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox115 139 (FixedTape.rowsAux denominator ibox115 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox115) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_115
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
private noncomputable def tree112 : TapeTree := .split 1 (((27946753541351216417040305933001948613613449611093295366929736645671884523707144601600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree113 tree114
attribute [irreducible] tree112
private theorem accepted_112 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox112) tree112 = true := by
  simp only [tree112,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox112 1 (27946753541351216417040305933001948613613449611093295366929736645671884523707144601600000000000000000000000 : Int) false,decode_split denominator ibox112 1 (27946753541351216417040305933001948613613449611093295366929736645671884523707144601600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_113 h,accepted_114 h⟩
private noncomputable def tree111 : TapeTree := .split 2 (((10748751362058160160400117666539211005235942158112805910357591017566109432195055616000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree112 tree115
attribute [irreducible] tree111
private theorem accepted_111 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox111) tree111 = true := by
  simp only [tree111,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox111 2 (10748751362058160160400117666539211005235942158112805910357591017566109432195055616000000000000000000000000 : Int) false,decode_split denominator ibox111 2 (10748751362058160160400117666539211005235942158112805910357591017566109432195055616000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_112 h,accepted_115 h⟩
private noncomputable def tree110 : TapeTree := .split 1 (((30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree111 tree116
attribute [irreducible] tree110
private theorem accepted_110 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox110) tree110 = true := by
  simp only [tree110,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox110 1 (30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) false,decode_split denominator ibox110 1 (30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_111 h,accepted_116 h⟩
private noncomputable def tree109 : TapeTree := .split 2 (((12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree110 tree127
attribute [irreducible] tree109
private theorem accepted_109 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox109) tree109 = true := by
  simp only [tree109,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox109 2 (12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 : Int) false,decode_split denominator ibox109 2 (12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_110 h,accepted_127 h⟩
private noncomputable def tree108 : TapeTree := .centered (candidateRows ibox108) (candidateRows (FixedTape.midBox ibox108))
attribute [irreducible] tree108
private theorem sign_108 : 2*denominator*(computed denominator (FixedTape.midBox ibox108)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox108).gradient k).lo.natAbs ((computed denominator ibox108).gradient k).hi.natAbs : Int)*((ibox108 k).hi-(ibox108 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox108
    (computed denominator ibox108) (computed denominator (FixedTape.midBox ibox108))
    (by decide +kernel)
private theorem midpoint_even_108 : ∀ k, 2 ∣ (ibox108 k).lo+(ibox108 k).hi := by decide +kernel
private theorem accepted_108 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox108) tree108 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox108 midpoint_even_108
  simp only [tree108,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox108,candidate_valid h (FixedTape.midBox ibox108),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox108 139 (FixedTape.rowsAux denominator ibox108 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox108) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_108
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
private noncomputable def tree106 : TapeTree := .split 2 (((15048251906881424224560164733154895407330319021357928274500627424592553205073077862400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree107 tree108
attribute [irreducible] tree106
private theorem accepted_106 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox106) tree106 = true := by
  simp only [tree106,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox106 2 (15048251906881424224560164733154895407330319021357928274500627424592553205073077862400000000000000000000000 : Int) false,decode_split denominator ibox106 2 (15048251906881424224560164733154895407330319021357928274500627424592553205073077862400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_107 h,accepted_108 h⟩
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
private noncomputable def tree104 : TapeTree := .split 1 (((21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree105 tree106
attribute [irreducible] tree104
private theorem accepted_104 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox104) tree104 = true := by
  simp only [tree104,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox104 1 (21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 : Int) false,decode_split denominator ibox104 1 (21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_105 h,accepted_106 h⟩
private noncomputable def tree103 : TapeTree := .centered (candidateRows ibox103) (candidateRows (FixedTape.midBox ibox103))
attribute [irreducible] tree103
private theorem sign_103 : 2*denominator*(computed denominator (FixedTape.midBox ibox103)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox103).gradient k).lo.natAbs ((computed denominator ibox103).gradient k).hi.natAbs : Int)*((ibox103 k).hi-(ibox103 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox103
    (computed denominator ibox103) (computed denominator (FixedTape.midBox ibox103))
    (by decide +kernel)
private theorem midpoint_even_103 : ∀ k, 2 ∣ (ibox103 k).lo+(ibox103 k).hi := by decide +kernel
private theorem accepted_103 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox103) tree103 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox103 midpoint_even_103
  simp only [tree103,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox103,candidate_valid h (FixedTape.midBox ibox103),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox103 139 (FixedTape.rowsAux denominator ibox103 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox103) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_103
private noncomputable def tree102 : TapeTree := .centered (candidateRows ibox102) (candidateRows (FixedTape.midBox ibox102))
attribute [irreducible] tree102
private theorem sign_102 : 2*denominator*(computed denominator (FixedTape.midBox ibox102)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox102).gradient k).lo.natAbs ((computed denominator ibox102).gradient k).hi.natAbs : Int)*((ibox102 k).hi-(ibox102 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox102
    (computed denominator ibox102) (computed denominator (FixedTape.midBox ibox102))
    (by decide +kernel)
private theorem midpoint_even_102 : ∀ k, 2 ∣ (ibox102 k).lo+(ibox102 k).hi := by decide +kernel
private theorem accepted_102 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox102) tree102 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox102 midpoint_even_102
  simp only [tree102,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox102,candidate_valid h (FixedTape.midBox ibox102),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox102 139 (FixedTape.rowsAux denominator ibox102 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox102) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_102
private noncomputable def tree101 : TapeTree := .split 2 (((10748751362058160160400117666539211005235942158112805910357591017566109432195055616000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree102 tree103
attribute [irreducible] tree101
private theorem accepted_101 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox101) tree101 = true := by
  simp only [tree101,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox101 2 (10748751362058160160400117666539211005235942158112805910357591017566109432195055616000000000000000000000000 : Int) false,decode_split denominator ibox101 2 (10748751362058160160400117666539211005235942158112805910357591017566109432195055616000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_102 h,accepted_103 h⟩
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
private noncomputable def tree99 : TapeTree := .split 1 (((21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree100 tree101
attribute [irreducible] tree99
private theorem accepted_99 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox99) tree99 = true := by
  simp only [tree99,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox99 1 (21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 : Int) false,decode_split denominator ibox99 1 (21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_100 h,accepted_101 h⟩
private noncomputable def tree98 : TapeTree := .split 2 (((12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree99 tree104
attribute [irreducible] tree98
private theorem accepted_98 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox98) tree98 = true := by
  simp only [tree98,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox98 2 (12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 : Int) false,decode_split denominator ibox98 2 (12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_99 h,accepted_104 h⟩
private noncomputable def tree97 : TapeTree := .split 1 (((25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree98 tree109
attribute [irreducible] tree97
private theorem accepted_97 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox97) tree97 = true := by
  simp only [tree97,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox97 1 (25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 : Int) false,decode_split denominator ibox97 1 (25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_98 h,accepted_109 h⟩
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
private noncomputable def tree95 : TapeTree := .face 1 true (candidateRows ibox95) tree96
attribute [irreducible] tree95
private theorem sign_95 : 0 ≤ ((computed denominator ibox95).gradient 1).lo := by decide +kernel
private theorem accepted_95 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox95) tree95 = true := by
  simp only [tree95,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox95,?_,accepted_96 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox95)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox95).gradient 1).lo) denominator_positive).2 sign_95
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
private noncomputable def tree93 : TapeTree := .split 0 (((24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) : ℚ)/(denominator : ℚ)) tree94 tree95
attribute [irreducible] tree93
private theorem accepted_93 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox93) tree93 = true := by
  simp only [tree93,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox93 0 (24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) false,decode_split denominator ibox93 0 (24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) true]
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
private noncomputable def tree90 : TapeTree := .split 0 (((24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) : ℚ)/(denominator : ℚ)) tree91 tree92
attribute [irreducible] tree90
private theorem accepted_90 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox90) tree90 = true := by
  simp only [tree90,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox90 0 (24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) false,decode_split denominator ibox90 0 (24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_91 h,accepted_92 h⟩
private noncomputable def tree89 : TapeTree := .split 1 (((32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree90 tree93
attribute [irreducible] tree89
private theorem accepted_89 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox89) tree89 = true := by
  simp only [tree89,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox89 1 (32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 : Int) false,decode_split denominator ibox89 1 (32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_90 h,accepted_93 h⟩
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
private noncomputable def tree87 : TapeTree := .face 1 true (candidateRows ibox87) tree88
attribute [irreducible] tree87
private theorem sign_87 : 0 ≤ ((computed denominator ibox87).gradient 1).lo := by decide +kernel
private theorem accepted_87 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox87) tree87 = true := by
  simp only [tree87,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox87,?_,accepted_88 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox87)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox87).gradient 1).lo) denominator_positive).2 sign_87
private noncomputable def tree86 : TapeTree := .centered (candidateRows ibox86) (candidateRows (FixedTape.midBox ibox86))
attribute [irreducible] tree86
private theorem sign_86 : 2*denominator*(computed denominator (FixedTape.midBox ibox86)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox86).gradient k).lo.natAbs ((computed denominator ibox86).gradient k).hi.natAbs : Int)*((ibox86 k).hi-(ibox86 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox86
    (computed denominator ibox86) (computed denominator (FixedTape.midBox ibox86))
    (by decide +kernel)
private theorem midpoint_even_86 : ∀ k, 2 ∣ (ibox86 k).lo+(ibox86 k).hi := by decide +kernel
private theorem accepted_86 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox86) tree86 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox86 midpoint_even_86
  simp only [tree86,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox86,candidate_valid h (FixedTape.midBox ibox86),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox86 139 (FixedTape.rowsAux denominator ibox86 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox86) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_86
private noncomputable def tree85 : TapeTree := .face 1 true (candidateRows ibox85) tree86
attribute [irreducible] tree85
private theorem sign_85 : 0 ≤ ((computed denominator ibox85).gradient 1).lo := by decide +kernel
private theorem accepted_85 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox85) tree85 = true := by
  simp only [tree85,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox85,?_,accepted_86 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox85)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox85).gradient 1).lo) denominator_positive).2 sign_85
private noncomputable def tree84 : TapeTree := .split 0 (((24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) : ℚ)/(denominator : ℚ)) tree85 tree87
attribute [irreducible] tree84
private theorem accepted_84 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox84) tree84 = true := by
  simp only [tree84,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox84 0 (24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) false,decode_split denominator ibox84 0 (24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_85 h,accepted_87 h⟩
private noncomputable def tree83 : TapeTree := .centered (candidateRows ibox83) (candidateRows (FixedTape.midBox ibox83))
attribute [irreducible] tree83
private theorem sign_83 : 2*denominator*(computed denominator (FixedTape.midBox ibox83)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox83).gradient k).lo.natAbs ((computed denominator ibox83).gradient k).hi.natAbs : Int)*((ibox83 k).hi-(ibox83 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox83
    (computed denominator ibox83) (computed denominator (FixedTape.midBox ibox83))
    (by decide +kernel)
private theorem midpoint_even_83 : ∀ k, 2 ∣ (ibox83 k).lo+(ibox83 k).hi := by decide +kernel
private theorem accepted_83 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox83) tree83 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox83 midpoint_even_83
  simp only [tree83,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox83,candidate_valid h (FixedTape.midBox ibox83),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox83 139 (FixedTape.rowsAux denominator ibox83 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox83) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_83
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
private noncomputable def tree81 : TapeTree := .split 0 (((24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) : ℚ)/(denominator : ℚ)) tree82 tree83
attribute [irreducible] tree81
private theorem accepted_81 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox81) tree81 = true := by
  simp only [tree81,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox81 0 (24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) false,decode_split denominator ibox81 0 (24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_82 h,accepted_83 h⟩
private noncomputable def tree80 : TapeTree := .split 1 (((32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree81 tree84
attribute [irreducible] tree80
private theorem accepted_80 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox80) tree80 = true := by
  simp only [tree80,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox80 1 (32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 : Int) false,decode_split denominator ibox80 1 (32246254086174480481200352999617633015707826474338417731072773052698328296585166848000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_81 h,accepted_84 h⟩
private noncomputable def tree79 : TapeTree := .split 2 (((6449250817234896096240070599923526603141565294867683546214554610539665659317033369600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree80 tree89
attribute [irreducible] tree79
private theorem accepted_79 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox79) tree79 = true := by
  simp only [tree79,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox79 2 (6449250817234896096240070599923526603141565294867683546214554610539665659317033369600000000000000000000000 : Int) false,decode_split denominator ibox79 2 (6449250817234896096240070599923526603141565294867683546214554610539665659317033369600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_80 h,accepted_89 h⟩
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
private noncomputable def tree77 : TapeTree := .centered (candidateRows ibox77) (candidateRows (FixedTape.midBox ibox77))
attribute [irreducible] tree77
private theorem sign_77 : 2*denominator*(computed denominator (FixedTape.midBox ibox77)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox77).gradient k).lo.natAbs ((computed denominator ibox77).gradient k).hi.natAbs : Int)*((ibox77 k).hi-(ibox77 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox77
    (computed denominator ibox77) (computed denominator (FixedTape.midBox ibox77))
    (by decide +kernel)
private theorem midpoint_even_77 : ∀ k, 2 ∣ (ibox77 k).lo+(ibox77 k).hi := by decide +kernel
private theorem accepted_77 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox77) tree77 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox77 midpoint_even_77
  simp only [tree77,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox77,candidate_valid h (FixedTape.midBox ibox77),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox77 139 (FixedTape.rowsAux denominator ibox77 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox77) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_77
private noncomputable def tree76 : TapeTree := .split 2 (((6449250817234896096240070599923526603141565294867683546214554610539665659317033369600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree77 tree78
attribute [irreducible] tree76
private theorem accepted_76 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox76) tree76 = true := by
  simp only [tree76,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox76 2 (6449250817234896096240070599923526603141565294867683546214554610539665659317033369600000000000000000000000 : Int) false,decode_split denominator ibox76 2 (6449250817234896096240070599923526603141565294867683546214554610539665659317033369600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_77 h,accepted_78 h⟩
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
private noncomputable def tree74 : TapeTree := .split 1 (((27946753541351216417040305933001948613613449611093295366929736645671884523707144601600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree75 tree76
attribute [irreducible] tree74
private theorem accepted_74 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox74) tree74 = true := by
  simp only [tree74,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox74 1 (27946753541351216417040305933001948613613449611093295366929736645671884523707144601600000000000000000000000 : Int) false,decode_split denominator ibox74 1 (27946753541351216417040305933001948613613449611093295366929736645671884523707144601600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_75 h,accepted_76 h⟩
private noncomputable def tree73 : TapeTree := .split 1 (((30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree74 tree79
attribute [irreducible] tree73
private theorem accepted_73 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox73) tree73 = true := by
  simp only [tree73,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox73 1 (30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) false,decode_split denominator ibox73 1 (30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_74 h,accepted_79 h⟩
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
private noncomputable def tree70 : TapeTree := .split 0 (((24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) : ℚ)/(denominator : ℚ)) tree71 tree72
attribute [irreducible] tree70
private theorem accepted_70 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox70) tree70 = true := by
  simp only [tree70,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox70 0 (24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) false,decode_split denominator ibox70 0 (24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_71 h,accepted_72 h⟩
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
private noncomputable def tree67 : TapeTree := .split 0 (((24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) : ℚ)/(denominator : ℚ)) tree68 tree69
attribute [irreducible] tree67
private theorem accepted_67 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox67) tree67 = true := by
  simp only [tree67,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox67 0 (24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) false,decode_split denominator ibox67 0 (24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_68 h,accepted_69 h⟩
private noncomputable def tree66 : TapeTree := .split 2 (((3224625408617448048120035299961763301570782647433841773107277305269832829658516684800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree67 tree70
attribute [irreducible] tree66
private theorem accepted_66 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox66) tree66 = true := by
  simp only [tree66,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox66 2 (3224625408617448048120035299961763301570782647433841773107277305269832829658516684800000000000000000000000 : Int) false,decode_split denominator ibox66 2 (3224625408617448048120035299961763301570782647433841773107277305269832829658516684800000000000000000000000 : Int) true]
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
private noncomputable def tree63 : TapeTree := .split 2 (((1612312704308724024060017649980881650785391323716920886553638652634916414829258342400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree64 tree65
attribute [irreducible] tree63
private theorem accepted_63 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox63) tree63 = true := by
  simp only [tree63,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox63 2 (1612312704308724024060017649980881650785391323716920886553638652634916414829258342400000000000000000000000 : Int) false,decode_split denominator ibox63 2 (1612312704308724024060017649980881650785391323716920886553638652634916414829258342400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_64 h,accepted_65 h⟩
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
private noncomputable def tree60 : TapeTree := .split 2 (((1612312704308724024060017649980881650785391323716920886553638652634916414829258342400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree61 tree62
attribute [irreducible] tree60
private theorem accepted_60 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox60) tree60 = true := by
  simp only [tree60,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox60 2 (1612312704308724024060017649980881650785391323716920886553638652634916414829258342400000000000000000000000 : Int) false,decode_split denominator ibox60 2 (1612312704308724024060017649980881650785391323716920886553638652634916414829258342400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_61 h,accepted_62 h⟩
private noncomputable def tree59 : TapeTree := .split 0 (((24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) : ℚ)/(denominator : ℚ)) tree60 tree63
attribute [irreducible] tree59
private theorem accepted_59 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox59) tree59 = true := by
  simp only [tree59,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox59 0 (24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) false,decode_split denominator ibox59 0 (24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_60 h,accepted_63 h⟩
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
private noncomputable def tree56 : TapeTree := .split 0 (((24632555204716617607517008962254233775005309661099767157153061181271982667851856723525836383736299520000000 : Int) : ℚ)/(denominator : ℚ)) tree57 tree58
attribute [irreducible] tree56
private theorem accepted_56 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox56) tree56 = true := by
  simp only [tree56,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox56 0 (24632555204716617607517008962254233775005309661099767157153061181271982667851856723525836383736299520000000 : Int) false,decode_split denominator ibox56 0 (24632555204716617607517008962254233775005309661099767157153061181271982667851856723525836383736299520000000 : Int) true]
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
private noncomputable def tree54 : TapeTree := .face 2 false (candidateRows ibox54) tree55
attribute [irreducible] tree54
private theorem sign_54 : ((computed denominator ibox54).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_54 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox54) tree54 = true := by
  simp only [tree54,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox54,?_,accepted_55 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox54)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox54).gradient 2).hi) denominator_positive).1 sign_54
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
private noncomputable def tree52 : TapeTree := .face 2 false (candidateRows ibox52) tree53
attribute [irreducible] tree52
private theorem sign_52 : ((computed denominator ibox52).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_52 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox52) tree52 = true := by
  simp only [tree52,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox52,?_,accepted_53 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox52)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox52).gradient 2).hi) denominator_positive).1 sign_52
private noncomputable def tree51 : TapeTree := .split 0 (((24632555204716617607517008962254233775005309661099767157153061181271982667851856723525836383736299520000000 : Int) : ℚ)/(denominator : ℚ)) tree52 tree54
attribute [irreducible] tree51
private theorem accepted_51 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox51) tree51 = true := by
  simp only [tree51,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox51 0 (24632555204716617607517008962254233775005309661099767157153061181271982667851856723525836383736299520000000 : Int) false,decode_split denominator ibox51 0 (24632555204716617607517008962254233775005309661099767157153061181271982667851856723525836383736299520000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_52 h,accepted_54 h⟩
private noncomputable def tree50 : TapeTree := .split 2 (((537437568102908008020005883326960550261797107905640295517879550878305471609752780800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree51 tree56
attribute [irreducible] tree50
private theorem accepted_50 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox50) tree50 = true := by
  simp only [tree50,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox50 2 (537437568102908008020005883326960550261797107905640295517879550878305471609752780800000000000000000000000 : Int) false,decode_split denominator ibox50 2 (537437568102908008020005883326960550261797107905640295517879550878305471609752780800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_51 h,accepted_56 h⟩
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
private noncomputable def tree47 : TapeTree := .split 0 (((24453409348682316084710485620682330700930595055980394283814264863011844615458314336977509151208898560000000 : Int) : ℚ)/(denominator : ℚ)) tree48 tree49
attribute [irreducible] tree47
private theorem accepted_47 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox47) tree47 = true := by
  simp only [tree47,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox47 0 (24453409348682316084710485620682330700930595055980394283814264863011844615458314336977509151208898560000000 : Int) false,decode_split denominator ibox47 0 (24453409348682316084710485620682330700930595055980394283814264863011844615458314336977509151208898560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_48 h,accepted_49 h⟩
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
private noncomputable def tree44 : TapeTree := .split 0 (((24453409348682316084710485620682330700930595055980394283814264863011844615458314336977509151208898560000000 : Int) : ℚ)/(denominator : ℚ)) tree45 tree46
attribute [irreducible] tree44
private theorem accepted_44 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox44) tree44 = true := by
  simp only [tree44,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox44 0 (24453409348682316084710485620682330700930595055980394283814264863011844615458314336977509151208898560000000 : Int) false,decode_split denominator ibox44 0 (24453409348682316084710485620682330700930595055980394283814264863011844615458314336977509151208898560000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_45 h,accepted_46 h⟩
private noncomputable def tree43 : TapeTree := .split 2 (((537437568102908008020005883326960550261797107905640295517879550878305471609752780800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree44 tree47
attribute [irreducible] tree43
private theorem accepted_43 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox43) tree43 = true := by
  simp only [tree43,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox43 2 (537437568102908008020005883326960550261797107905640295517879550878305471609752780800000000000000000000000 : Int) false,decode_split denominator ibox43 2 (537437568102908008020005883326960550261797107905640295517879550878305471609752780800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_44 h,accepted_47 h⟩
private noncomputable def tree42 : TapeTree := .split 0 (((24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) : ℚ)/(denominator : ℚ)) tree43 tree50
attribute [irreducible] tree42
private theorem accepted_42 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox42) tree42 = true := by
  simp only [tree42,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox42 0 (24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) false,decode_split denominator ibox42 0 (24542982276699466846113747291468282237967952358540080720483663022141913641655085530251672767472599040000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_43 h,accepted_50 h⟩
private noncomputable def tree41 : TapeTree := .split 2 (((1074875136205816016040011766653921100523594215811280591035759101756610943219505561600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree42 tree59
attribute [irreducible] tree41
private theorem accepted_41 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox41) tree41 = true := by
  simp only [tree41,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox41 2 (1074875136205816016040011766653921100523594215811280591035759101756610943219505561600000000000000000000000 : Int) false,decode_split denominator ibox41 2 (1074875136205816016040011766653921100523594215811280591035759101756610943219505561600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_42 h,accepted_59 h⟩
private noncomputable def tree40 : TapeTree := .split 2 (((2149750272411632032080023533307842201047188431622561182071518203513221886439011123200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree41 tree66
attribute [irreducible] tree40
private theorem accepted_40 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox40) tree40 = true := by
  simp only [tree40,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox40 2 (2149750272411632032080023533307842201047188431622561182071518203513221886439011123200000000000000000000000 : Int) false,decode_split denominator ibox40 2 (2149750272411632032080023533307842201047188431622561182071518203513221886439011123200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_41 h,accepted_66 h⟩
private noncomputable def tree39 : TapeTree := .face 1 true (candidateRows ibox39) tree40
attribute [irreducible] tree39
private theorem sign_39 : 0 ≤ ((computed denominator ibox39).gradient 1).lo := by decide +kernel
private theorem accepted_39 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox39) tree39 = true := by
  simp only [tree39,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox39,?_,accepted_40 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox39)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox39).gradient 1).lo) denominator_positive).2 sign_39
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
private noncomputable def tree37 : TapeTree := .face 1 true (candidateRows ibox37) tree38
attribute [irreducible] tree37
private theorem sign_37 : 0 ≤ ((computed denominator ibox37).gradient 1).lo := by decide +kernel
private theorem accepted_37 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox37) tree37 = true := by
  simp only [tree37,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox37,?_,accepted_38 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox37)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox37).gradient 1).lo) denominator_positive).2 sign_37
private noncomputable def tree36 : TapeTree := .split 1 (((30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree37 tree39
attribute [irreducible] tree36
private theorem accepted_36 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox36) tree36 = true := by
  simp only [tree36,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox36 1 (30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) false,decode_split denominator ibox36 1 (30096503813762848449120329466309790814660638042715856549001254849185106410146155724800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_37 h,accepted_39 h⟩
private noncomputable def tree35 : TapeTree := .split 2 (((4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree36 tree73
attribute [irreducible] tree35
private theorem accepted_35 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox35) tree35 = true := by
  simp only [tree35,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox35 2 (4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 : Int) false,decode_split denominator ibox35 2 (4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_36 h,accepted_73 h⟩
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
private noncomputable def tree32 : TapeTree := .split 2 (((6449250817234896096240070599923526603141565294867683546214554610539665659317033369600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree33 tree34
attribute [irreducible] tree32
private theorem accepted_32 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox32) tree32 = true := by
  simp only [tree32,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox32 2 (6449250817234896096240070599923526603141565294867683546214554610539665659317033369600000000000000000000000 : Int) false,decode_split denominator ibox32 2 (6449250817234896096240070599923526603141565294867683546214554610539665659317033369600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_33 h,accepted_34 h⟩
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
private noncomputable def tree30 : TapeTree := .split 1 (((21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree31 tree32
attribute [irreducible] tree30
private theorem accepted_30 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox30) tree30 = true := by
  simp only [tree30,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox30 1 (21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 : Int) false,decode_split denominator ibox30 1 (21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_31 h,accepted_32 h⟩
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
private noncomputable def tree27 : TapeTree := .split 1 (((21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree28 tree29
attribute [irreducible] tree27
private theorem accepted_27 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox27) tree27 = true := by
  simp only [tree27,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox27 1 (21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 : Int) false,decode_split denominator ibox27 1 (21497502724116320320800235333078422010471884316225611820715182035132218864390111232000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_28 h,accepted_29 h⟩
private noncomputable def tree26 : TapeTree := .split 2 (((4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree27 tree30
attribute [irreducible] tree26
private theorem accepted_26 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox26) tree26 = true := by
  simp only [tree26,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox26 2 (4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 : Int) false,decode_split denominator ibox26 2 (4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_27 h,accepted_30 h⟩
private noncomputable def tree25 : TapeTree := .split 1 (((25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree26 tree35
attribute [irreducible] tree25
private theorem accepted_25 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox25) tree25 = true := by
  simp only [tree25,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox25 1 (25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 : Int) false,decode_split denominator ibox25 1 (25797003268939584384960282399694106412566261179470734184858218442158662637268133478400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_26 h,accepted_35 h⟩
private noncomputable def tree24 : TapeTree := .split 2 (((8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree25 tree97
attribute [irreducible] tree24
private theorem accepted_24 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox24) tree24 = true := by
  simp only [tree24,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox24 2 (8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) false,decode_split denominator ibox24 2 (8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_25 h,accepted_97 h⟩
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
private noncomputable def tree21 : TapeTree := .split 1 (((12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree22 tree23
attribute [irreducible] tree21
private theorem accepted_21 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox21) tree21 = true := by
  simp only [tree21,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox21 1 (12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 : Int) false,decode_split denominator ibox21 1 (12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_22 h,accepted_23 h⟩
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
private noncomputable def tree18 : TapeTree := .split 2 (((15048251906881424224560164733154895407330319021357928274500627424592553205073077862400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree19 tree20
attribute [irreducible] tree18
private theorem accepted_18 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox18) tree18 = true := by
  simp only [tree18,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox18 2 (15048251906881424224560164733154895407330319021357928274500627424592553205073077862400000000000000000000000 : Int) false,decode_split denominator ibox18 2 (15048251906881424224560164733154895407330319021357928274500627424592553205073077862400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_19 h,accepted_20 h⟩
private noncomputable def tree17 : TapeTree := .split 1 (((8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree18 tree21
attribute [irreducible] tree17
private theorem accepted_17 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox17) tree17 = true := by
  simp only [tree17,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox17 1 (8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) false,decode_split denominator ibox17 1 (8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_18 h,accepted_21 h⟩
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
private noncomputable def tree14 : TapeTree := .split 1 (((12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree15 tree16
attribute [irreducible] tree14
private theorem accepted_14 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox14) tree14 = true := by
  simp only [tree14,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox14 1 (12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 : Int) false,decode_split denominator ibox14 1 (12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_15 h,accepted_16 h⟩
private noncomputable def tree13 : TapeTree := .centered (candidateRows ibox13) (candidateRows (FixedTape.midBox ibox13))
attribute [irreducible] tree13
private theorem sign_13 : 2*denominator*(computed denominator (FixedTape.midBox ibox13)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox13).gradient k).lo.natAbs ((computed denominator ibox13).gradient k).hi.natAbs : Int)*((ibox13 k).hi-(ibox13 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox13
    (computed denominator ibox13) (computed denominator (FixedTape.midBox ibox13))
    (by decide +kernel)
private theorem midpoint_even_13 : ∀ k, 2 ∣ (ibox13 k).lo+(ibox13 k).hi := by decide +kernel
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox13 midpoint_even_13
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox13,candidate_valid h (FixedTape.midBox ibox13),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox13 139 (FixedTape.rowsAux denominator ibox13 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox13) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_13
private noncomputable def tree12 : TapeTree := .split 1 (((8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree13 tree14
attribute [irreducible] tree12
private theorem accepted_12 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox12) tree12 = true := by
  simp only [tree12,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox12 1 (8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) false,decode_split denominator ibox12 1 (8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_13 h,accepted_14 h⟩
private noncomputable def tree11 : TapeTree := .split 2 (((12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree12 tree17
attribute [irreducible] tree11
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox11 2 (12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 : Int) false,decode_split denominator ibox11 2 (12898501634469792192480141199847053206283130589735367092429109221079331318634066739200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_12 h,accepted_17 h⟩
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
private noncomputable def tree8 : TapeTree := .split 2 (((4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree9 tree10
attribute [irreducible] tree8
private theorem accepted_8 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox8) tree8 = true := by
  simp only [tree8,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox8 2 (4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 : Int) false,decode_split denominator ibox8 2 (4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 : Int) true]
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
private noncomputable def tree5 : TapeTree := .split 2 (((4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree6 tree7
attribute [irreducible] tree5
private theorem accepted_5 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox5) tree5 = true := by
  simp only [tree5,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox5 2 (4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 : Int) false,decode_split denominator ibox5 2 (4299500544823264064160047066615684402094376863245122364143036407026443772878022246400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_6 h,accepted_7 h⟩
private noncomputable def tree4 : TapeTree := .split 1 (((8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree5 tree8
attribute [irreducible] tree4
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox4 1 (8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) false,decode_split denominator ibox4 1 (8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_5 h,accepted_8 h⟩
private noncomputable def tree3 : TapeTree := .split 2 (((8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree11
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 2 (8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) false,decode_split denominator ibox3 2 (8599001089646528128320094133231368804188753726490244728286072814052887545756044492800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_11 h⟩
private noncomputable def tree2 : TapeTree := .split 1 (((17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree24
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 1 (17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 : Int) false,decode_split denominator ibox2 1 (17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_3 h,accepted_24 h⟩
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
private noncomputable def tree0 : TapeTree := .split 2 (((17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree1 tree138
attribute [irreducible] tree0
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 139 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox0 2 (17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 : Int) false,decode_split denominator ibox0 2 (17198002179293056256640188266462737608377507452980489456572145628105775091512088985600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_1 h,accepted_138 h⟩
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (3541666666666667/5000000000000000 : ℚ) (23/32 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 139 = e144 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (3541666666666667/5000000000000000 : ℚ) (23/32 : ℚ)) x → eval e144 x ≤ 0 := by
  have hb := h.child_4 tape 139 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell93_high_internal_top

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell93_high_internal_top
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((3541666666666667/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((23/32 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 93 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 93 p)
    (hkb : ((23/32 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((3541666666666667/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r)
    (hcase : bStar < a), internalResidual (0 : Fin 9) a p A r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell93_high_internal_top.cell_bound h.child_8 h.child_9 (Cell93_high_internal_top.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell93_high_internal_top
