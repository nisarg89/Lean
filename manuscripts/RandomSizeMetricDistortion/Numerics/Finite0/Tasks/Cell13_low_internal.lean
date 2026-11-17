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
namespace Cell13_low_internal
private noncomputable def qValues : Fin 2 → ℚ := ![(10490037627495379536970925173629/12500000000000000000000000000000000 : ℚ),(70991576179427110215171/12500000000000000000000 : ℚ)]
private noncomputable abbrev e2 : PolyExpr := SharedFiniteSemantics5.e2 qValues
private noncomputable abbrev e11 : PolyExpr := SharedFiniteSemantics5.e11 qValues
private noncomputable abbrev e12 : PolyExpr := SharedFiniteSemantics5.e12 qValues
private noncomputable abbrev e16 : PolyExpr := SharedFiniteSemantics5.e16 qValues
private noncomputable abbrev e39 : PolyExpr := SharedFiniteSemantics5.e39 qValues
private noncomputable abbrev e219 : PolyExpr := SharedFiniteSemantics5.e219 qValues
private noncomputable abbrev node_1 := SharedFiniteSemantics5.node_1 qValues
private noncomputable abbrev node_2 := SharedFiniteSemantics5.node_2 qValues
private noncomputable abbrev node_3 := SharedFiniteSemantics5.node_3 qValues
private noncomputable abbrev node_4 := SharedFiniteSemantics5.node_4 qValues
private noncomputable abbrev node_5 := SharedFiniteSemantics5.node_5 qValues
private noncomputable abbrev node_6 := SharedFiniteSemantics5.node_6 qValues
private noncomputable abbrev node_9 := SharedFiniteSemantics5.node_9 qValues
private noncomputable abbrev node_10 := SharedFiniteSemantics5.node_10 qValues
private noncomputable abbrev node_11 := SharedFiniteSemantics5.node_11 qValues
private noncomputable abbrev node_12 := SharedFiniteSemantics5.node_12 qValues
private noncomputable abbrev node_13 := SharedFiniteSemantics5.node_13 qValues
private noncomputable abbrev node_14 := SharedFiniteSemantics5.node_14 qValues
private noncomputable abbrev node_15 := SharedFiniteSemantics5.node_15 qValues
private noncomputable abbrev node_16 := SharedFiniteSemantics5.node_16 qValues
private noncomputable abbrev node_38 := SharedFiniteSemantics5.node_38 qValues
private noncomputable abbrev node_39 := SharedFiniteSemantics5.node_39 qValues
private noncomputable abbrev node_180 := SharedFiniteSemantics5.node_180 qValues
private noncomputable abbrev node_181 := SharedFiniteSemantics5.node_181 qValues
private noncomputable abbrev node_182 := SharedFiniteSemantics5.node_182 qValues
private noncomputable abbrev node_183 := SharedFiniteSemantics5.node_183 qValues
private noncomputable abbrev node_184 := SharedFiniteSemantics5.node_184 qValues
private noncomputable abbrev node_185 := SharedFiniteSemantics5.node_185 qValues
private noncomputable abbrev node_186 := SharedFiniteSemantics5.node_186 qValues
private noncomputable abbrev node_187 := SharedFiniteSemantics5.node_187 qValues
private noncomputable abbrev node_188 := SharedFiniteSemantics5.node_188 qValues
private noncomputable abbrev node_189 := SharedFiniteSemantics5.node_189 qValues
private noncomputable abbrev node_190 := SharedFiniteSemantics5.node_190 qValues
private noncomputable abbrev node_191 := SharedFiniteSemantics5.node_191 qValues
private noncomputable abbrev node_192 := SharedFiniteSemantics5.node_192 qValues
private noncomputable abbrev node_193 := SharedFiniteSemantics5.node_193 qValues
private noncomputable abbrev node_194 := SharedFiniteSemantics5.node_194 qValues
private noncomputable abbrev node_199 := SharedFiniteSemantics5.node_199 qValues
private noncomputable abbrev node_200 := SharedFiniteSemantics5.node_200 qValues
private noncomputable abbrev node_201 := SharedFiniteSemantics5.node_201 qValues
private noncomputable abbrev node_218 := SharedFiniteSemantics5.node_218 qValues
private noncomputable abbrev node_219 := SharedFiniteSemantics5.node_219 qValues
private noncomputable abbrev semantic_H_37 := SharedFiniteSemantics5.semantic_H_37 qValues
private noncomputable abbrev semantic_psi_217 := SharedFiniteSemantics5.semantic_psi_217 qValues
private noncomputable abbrev semantic_Hd_179 := SharedFiniteSemantics5.semantic_Hd_179 qValues
private noncomputable def aPoint (x : Fin 4 → ℝ) : ℝ := x 0*x 1
private noncomputable def rPoint (x : Fin 4 → ℝ) : ℝ := ((49/100 : ℚ) : ℝ)+(((2840189/5000000 : ℚ) : ℝ)-((49/100 : ℚ) : ℝ))*x 3
private noncomputable def capPoint (x : Fin 4 → ℝ) : ℝ := x 0+(rPoint x-x 0)*x 2
private noncomputable def yPoint (x : Fin 4 → ℝ) : ℝ := aPoint x+capPoint x-x 0
private theorem point_12 (x : Fin 4 → ℝ) : eval e12 x = aPoint x := by
  simp only [node_2,node_3,node_12] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_11 (x : Fin 4 → ℝ) : eval e11 x = rPoint x := by
  simp only [node_5,node_6,node_9,node_10,node_11] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_2 (x : Fin 4 → ℝ) : eval e2 x = x 0 := by
  simp only [node_2] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_16 (x : Fin 4 → ℝ) : eval e16 x = capPoint x := by
  simp only [node_2,node_4,node_5,node_6,node_9,node_10,node_11,node_13,node_14,node_15,node_16] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_39 (x : Fin 4 → ℝ) : eval e39 x = yPoint x := by
  simp only [node_2,node_3,node_4,node_5,node_6,node_9,node_10,node_11,node_12,node_13,node_14,node_15,node_16,node_38,node_39] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem price_lambda_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceLambda 13 p = ((10490037627495379536970925173629/12500000000000000000000000000000000 : ℝ)+(70991576179427110215171/12500000000000000000000 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell13,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 13 p = (((145513/100000 : ℝ)+(145513/25000 : ℝ)*p)-(145513/100000 : ℝ)*(1/1 : ℝ))/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell13,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e219 x = (x 0*(1-x 0))*(aPoint x+priceLambda 13 (x 0)*(HStar (yPoint x)-HStar (aPoint x)-HStar (capPoint x))+priceTau 13 (x 0)*psiStar (rPoint x)+(0)-(0)) := by
  have hp0 : x 0 ≠ 0 := ne_of_gt hp.1
  have hp1 : x 0 ≠ 1 := ne_of_lt hp.2
  have heps : 1-x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  rw [price_lambda_normal _ hp,price_tau_normal _ hp]
  simp only [node_1,node_13,node_180,node_181,node_182,node_183,node_184,node_185,node_186,node_187,node_188,node_189,node_190,node_191,node_192,node_193,node_194,node_199,node_200,node_201,node_218,node_219,semantic_H_37,semantic_psi_217,semantic_Hd_179,point_12,point_11,point_2,point_16,point_39]
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
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) (ha : aPoint x ≤ bStar) (hA : capPoint x ≤ bStar)
    (hL : lambdaStar (x 0) = priceLambda 13 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 13 (x 0)) :
    (1)*eval e219 x = (x 0*(1-x 0))*(internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,if_pos hA,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (5208333333333333/500000000000000000 : ℚ) (13841287201/1000000000000 : ℚ)) x → eval e219 x ≤ 0)
    (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((5208333333333333/500000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((13841287201/1000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 13 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 13 p)
    (hk0 : ((13841287201/1000000000000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((5208333333333333/500000000000000000 : ℚ) : ℝ))
    (hk1 : ((13841287201/1000000000000 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((5208333333333333/500000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r) :
    internalResidual (0 : Fin 9) a p A r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxA,hxr⟩ := h3 (5208333333333333/500000000000000000 : ℚ) (13841287201/1000000000000 : ℚ) ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ) p a A r hpcell hk0 hk1 hr ha hap hpA hAr
  have hcut : ((13841287201/1000000000000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) := by norm_num [bStar]
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxa
  have hAx : capPoint x = A := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxA
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 13 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 13 (x 0) := by simpa only [hxp] using hT
  have hrootb : ((2840189/5000000 : ℚ) : ℝ) ≤ bStar := by norm_num [bStar]
  have hAb : A ≤ bStar := hAr.trans (hr.2.trans hrootb)
  have hflag : aPoint x ≤ bStar := by rw [hax]; exact hap.trans (hpA.trans hAb)
  have hflagA : capPoint x ≤ bStar := by simpa only [hAx] using hAb
  have hb := hbound x hx
  have hv : (1 : ℝ)*eval e219 x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 1) hb
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
.const (49/100 : ℚ),
.const (390189/5000000 : ℚ),
.mul 6 4,
.add 5 7,
.mul 1 2,
.neg 1,
.add 8 10,
.mul 11 3,
.add 1 12,
.const (1085/4818 : ℚ),
.mul 14 9,
.mul 9 9,
.const (19/146 : ℚ),
.mul 17 16,
.mul 9 16,
.const (35/438 : ℚ),
.mul 20 19,
.add 18 21,
.mul 16 16,
.mul 23 23,
.mul 24 24,
.mul 25 25,
.mul 9 26,
.const (1/66 : ℚ),
.mul 28 27,
.add 22 29,
.neg 30,
.add 15 31,
.const (4818/3733 : ℚ),
.mul 33 32,
.add 9 13,
.add 35 10,
.neg 9,
.add 1 37,
.add 13 36,
.mul 17 39,
.mul 13 13,
.mul 13 36,
.add 41 42,
.mul 36 36,
.add 43 44,
.mul 20 45,
.add 40 46,
.mul 41 41,
.mul 48 48,
.mul 49 49,
.mul 50 50,
.mul 13 41,
.mul 52 52,
.mul 13 53,
.mul 54 54,
.mul 13 55,
.mul 56 56,
.mul 13 57,
.mul 58 36,
.add 51 59,
.mul 57 44,
.add 60 61,
.mul 55 55,
.mul 13 63,
.mul 36 44,
.mul 64 65,
.add 62 66,
.mul 44 44,
.mul 63 68,
.add 67 69,
.mul 53 53,
.mul 13 71,
.mul 72 72,
.mul 13 73,
.mul 36 68,
.mul 74 75,
.add 70 76,
.mul 65 65,
.mul 73 78,
.add 77 79,
.mul 71 71,
.mul 13 81,
.mul 36 78,
.mul 82 83,
.add 80 84,
.mul 68 68,
.mul 81 86,
.add 85 87,
.mul 13 48,
.mul 89 89,
.mul 13 90,
.mul 91 91,
.mul 13 92,
.mul 36 86,
.mul 93 94,
.add 88 95,
.mul 75 75,
.mul 92 97,
.add 96 98,
.mul 90 90,
.mul 13 100,
.mul 36 97,
.mul 101 102,
.add 99 103,
.mul 78 78,
.mul 100 105,
.add 104 106,
.mul 13 49,
.mul 108 108,
.mul 13 109,
.mul 36 105,
.mul 110 111,
.add 107 112,
.mul 83 83,
.mul 109 114,
.add 113 115,
.mul 13 50,
.mul 36 114,
.mul 117 118,
.add 116 119,
.mul 86 86,
.mul 50 121,
.add 120 122,
.mul 36 121,
.mul 56 124,
.add 123 125,
.mul 94 94,
.mul 55 127,
.add 126 128,
.mul 36 127,
.mul 72 130,
.add 129 131,
.mul 97 97,
.mul 71 133,
.add 132 134,
.mul 36 133,
.mul 91 136,
.add 135 137,
.mul 102 102,
.mul 90 139,
.add 138 140,
.mul 36 139,
.mul 108 142,
.add 141 143,
.mul 105 105,
.mul 49 145,
.add 144 146,
.mul 36 145,
.mul 54 148,
.add 147 149,
.mul 111 111,
.mul 53 151,
.add 150 152,
.mul 36 151,
.mul 89 154,
.add 153 155,
.mul 114 114,
.mul 48 157,
.add 156 158,
.mul 36 157,
.mul 52 160,
.add 159 161,
.mul 118 118,
.mul 41 163,
.add 162 164,
.mul 36 163,
.mul 13 166,
.add 165 167,
.mul 121 121,
.add 168 169,
.mul 28 170,
.add 47 171,
.neg 172,
.add 14 173,
.mul 38 174,
.mul 33 175,
.add 34 176,
.neg 177,
.const (10490037627495379536970925173629/12500000000000000000000000000000000 : ℚ),
.const (70991576179427110215171/12500000000000000000000 : ℚ),
.mul 180 1,
.add 179 181,
.const (145513/100000 : ℚ),
.const (145513/25000 : ℚ),
.mul 184 1,
.add 183 185,
.add 0 10,
.mul 1 187,
.const (-145513/100000 : ℚ),
.add 186 189,
.mul 190 188,
.mul 9 188,
.mul 182 178,
.add 192 193,
.const (19/73 : ℚ),
.mul 195 8,
.mul 8 8,
.const (35/146 : ℚ),
.mul 198 197,
.add 196 199,
.mul 197 197,
.mul 201 201,
.mul 202 202,
.mul 203 203,
.const (1/2 : ℚ),
.mul 205 204,
.add 200 206,
.neg 207,
.add 14 208,
.mul 33 209,
.mul 191 210,
.add 194 211]
private noncomputable def ssaQVals : Fin 16 → ℚ := ![(1/1 : ℚ),(49/100 : ℚ),(390189/5000000 : ℚ),(1085/4818 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(4818/3733 : ℚ),(10490037627495379536970925173629/12500000000000000000000000000000000 : ℚ),(70991576179427110215171/12500000000000000000000 : ℚ),(145513/100000 : ℚ),(145513/25000 : ℚ),(-145513/100000 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ)]
private theorem ssa_tape : MetricDistortion.OptimizedSSAFinite0.S_004bb3bd23335d3f.p213 ssaQVals = tape := by rfl
private noncomputable def computed (D : Int) (B : Fin 4 → FixedTape.I) : FixedTape.Row :=
  MetricDistortion.OptimizedSSAFinite0.S_004bb3bd23335d3f.computed ssaQVals D B
private theorem ssa_matches (D : Int) (B : Fin 4 → FixedTape.I) :
    (FixedTape.rowsAux D B [] tape).getD 212 FixedTape.zeroRow = computed D B := by
  rw [←ssa_tape]
  exact MetricDistortion.OptimizedSSAFinite0.S_004bb3bd23335d3f.ssa_matches ssaQVals D B

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
private noncomputable def denominator : Int := 71248278217378879231820925594972979200000000000000000000000000000000000000000000000000000
private theorem denominator_positive : 0 < denominator := by decide +kernel
private noncomputable def candidateRows (B : Fin 4 → FixedTape.I) : List TapeBounds :=
  (FixedTape.rowsAux denominator B [] tape).map (FixedTape.decodeRow denominator)
private theorem root_in_range : 212 < tape.length := by decide +kernel
private theorem references_valid : tapeRefsValidAux 0 tape = true := by decide +kernel
private theorem candidate_valid (h : Needs) (B : Fin 4 → FixedTape.I) :
    tapeCheck (FixedTape.decodeBox denominator B) tape (candidateRows B) = true :=
  h.child_10.1 denominator denominator_positive B tape references_valid
private theorem candidate_root (B : Fin 4 → FixedTape.I) :
    (candidateRows B).getD 212 zeroTapeBounds = FixedTape.decodeRow denominator (computed denominator B) := by
  unfold candidateRows
  rw [←decode_zeroRow denominator,List.getD_map,ssa_matches]
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨742169564764363277832615830028382378786049603351347200000000000000000000000000000000000,986167881383493376879127689361672806941799219200000000000000000000000000000000000000000⟩,⟨0,71248278217378879231820925594972979200000000000000000000000000000000000000000000000000000⟩,⟨0,71248278217378879231820925594972979200000000000000000000000000000000000000000000000000000⟩,⟨0,71248278217378879231820925594972979200000000000000000000000000000000000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := splitI ibox0 2 35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 false
private noncomputable def ibox2 : Fin 4 → FixedTape.I := faceI ibox1 3 false
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 0 864168723073928327355871759695027592863924411275673600000000000000000000000000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 1 35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := faceI ibox4 2 true
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox3 1 35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 true
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox6 1 53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 false
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox6 1 53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 true
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox8 0 803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 false
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox8 0 803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 true
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox2 0 864168723073928327355871759695027592863924411275673600000000000000000000000000000000000 true
private noncomputable def ibox12 : Fin 4 → FixedTape.I := faceI ibox11 1 true
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox0 2 35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 true
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox13 0 864168723073928327355871759695027592863924411275673600000000000000000000000000000000000 false
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox14 2 53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 false
private noncomputable def ibox16 : Fin 4 → FixedTape.I := faceI ibox15 3 false
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox16 1 35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 false
private noncomputable def ibox18 : Fin 4 → FixedTape.I := faceI ibox17 2 true
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox16 1 35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 true
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox19 0 803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 false
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox19 0 803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 true
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox14 2 53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 true
private noncomputable def ibox23 : Fin 4 → FixedTape.I := splitI ibox22 1 35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 false
private noncomputable def ibox24 : Fin 4 → FixedTape.I := faceI ibox23 2 true
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox24 1 17812069554344719807955231398743244800000000000000000000000000000000000000000000000000000 false
private noncomputable def ibox26 : Fin 4 → FixedTape.I := splitI ibox25 1 8906034777172359903977615699371622400000000000000000000000000000000000000000000000000000 false
private noncomputable def ibox27 : Fin 4 → FixedTape.I := splitI ibox26 0 803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 false
private noncomputable def ibox28 : Fin 4 → FixedTape.I := faceI ibox27 1 false
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox28 3 35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 false
private noncomputable def ibox30 : Fin 4 → FixedTape.I := splitI ibox29 0 772669354341754540213429812445043682305518305332428800000000000000000000000000000000000 false
private noncomputable def ibox31 : Fin 4 → FixedTape.I := splitI ibox29 0 772669354341754540213429812445043682305518305332428800000000000000000000000000000000000 true
private noncomputable def ibox32 : Fin 4 → FixedTape.I := splitI ibox28 3 35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 true
private noncomputable def ibox33 : Fin 4 → FixedTape.I := splitI ibox32 0 772669354341754540213429812445043682305518305332428800000000000000000000000000000000000 false
private noncomputable def ibox34 : Fin 4 → FixedTape.I := splitI ibox32 0 772669354341754540213429812445043682305518305332428800000000000000000000000000000000000 true
private noncomputable def ibox35 : Fin 4 → FixedTape.I := splitI ibox26 0 803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 true
private noncomputable def ibox36 : Fin 4 → FixedTape.I := faceI ibox35 1 false
private noncomputable def ibox37 : Fin 4 → FixedTape.I := splitI ibox36 3 35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 false
private noncomputable def ibox38 : Fin 4 → FixedTape.I := splitI ibox37 0 833668933496537064975057777278366289344455709294592000000000000000000000000000000000000 false
private noncomputable def ibox39 : Fin 4 → FixedTape.I := splitI ibox37 0 833668933496537064975057777278366289344455709294592000000000000000000000000000000000000 true
private noncomputable def ibox40 : Fin 4 → FixedTape.I := splitI ibox36 3 35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 true
private noncomputable def ibox41 : Fin 4 → FixedTape.I := splitI ibox40 0 833668933496537064975057777278366289344455709294592000000000000000000000000000000000000 false
private noncomputable def ibox42 : Fin 4 → FixedTape.I := splitI ibox40 0 833668933496537064975057777278366289344455709294592000000000000000000000000000000000000 true
private noncomputable def ibox43 : Fin 4 → FixedTape.I := splitI ibox25 1 8906034777172359903977615699371622400000000000000000000000000000000000000000000000000000 true
private noncomputable def ibox44 : Fin 4 → FixedTape.I := splitI ibox43 0 803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 false
private noncomputable def ibox45 : Fin 4 → FixedTape.I := faceI ibox44 1 false
private noncomputable def ibox46 : Fin 4 → FixedTape.I := splitI ibox45 3 35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 false
private noncomputable def ibox47 : Fin 4 → FixedTape.I := splitI ibox45 3 35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 true
private noncomputable def ibox48 : Fin 4 → FixedTape.I := splitI ibox43 0 803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 true
private noncomputable def ibox49 : Fin 4 → FixedTape.I := faceI ibox48 1 false
private noncomputable def ibox50 : Fin 4 → FixedTape.I := splitI ibox24 1 17812069554344719807955231398743244800000000000000000000000000000000000000000000000000000 true
private noncomputable def ibox51 : Fin 4 → FixedTape.I := splitI ibox50 0 803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 false
private noncomputable def ibox52 : Fin 4 → FixedTape.I := faceI ibox51 1 false
private noncomputable def ibox53 : Fin 4 → FixedTape.I := splitI ibox50 0 803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 true
private noncomputable def ibox54 : Fin 4 → FixedTape.I := faceI ibox53 1 false
private noncomputable def ibox55 : Fin 4 → FixedTape.I := splitI ibox22 1 35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 true
private noncomputable def ibox56 : Fin 4 → FixedTape.I := faceI ibox55 3 false
private noncomputable def ibox57 : Fin 4 → FixedTape.I := splitI ibox56 0 803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 false
private noncomputable def ibox58 : Fin 4 → FixedTape.I := splitI ibox57 1 53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 false
private noncomputable def ibox59 : Fin 4 → FixedTape.I := splitI ibox57 1 53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 true
private noncomputable def ibox60 : Fin 4 → FixedTape.I := splitI ibox56 0 803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 true
private noncomputable def ibox61 : Fin 4 → FixedTape.I := splitI ibox60 1 53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 false
private noncomputable def ibox62 : Fin 4 → FixedTape.I := splitI ibox60 1 53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 true
private noncomputable def ibox63 : Fin 4 → FixedTape.I := splitI ibox13 0 864168723073928327355871759695027592863924411275673600000000000000000000000000000000000 true
private noncomputable def ibox64 : Fin 4 → FixedTape.I := splitI ibox63 2 53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 false
private noncomputable def ibox65 : Fin 4 → FixedTape.I := faceI ibox64 3 false
private noncomputable def ibox66 : Fin 4 → FixedTape.I := splitI ibox65 1 35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 false
private noncomputable def ibox67 : Fin 4 → FixedTape.I := faceI ibox66 2 true
private noncomputable def ibox68 : Fin 4 → FixedTape.I := splitI ibox65 1 35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 true
private noncomputable def ibox69 : Fin 4 → FixedTape.I := splitI ibox68 0 925168302228710852117499724528350199902861815237836800000000000000000000000000000000000 false
private noncomputable def ibox70 : Fin 4 → FixedTape.I := splitI ibox68 0 925168302228710852117499724528350199902861815237836800000000000000000000000000000000000 true
private noncomputable def ibox71 : Fin 4 → FixedTape.I := splitI ibox63 2 53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 true
private noncomputable def ibox72 : Fin 4 → FixedTape.I := splitI ibox71 1 35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 false
private noncomputable def ibox73 : Fin 4 → FixedTape.I := faceI ibox72 2 true
private noncomputable def ibox74 : Fin 4 → FixedTape.I := splitI ibox73 1 17812069554344719807955231398743244800000000000000000000000000000000000000000000000000000 false
private noncomputable def ibox75 : Fin 4 → FixedTape.I := splitI ibox74 1 8906034777172359903977615699371622400000000000000000000000000000000000000000000000000000 false
private noncomputable def ibox76 : Fin 4 → FixedTape.I := splitI ibox75 0 925168302228710852117499724528350199902861815237836800000000000000000000000000000000000 false
private noncomputable def ibox77 : Fin 4 → FixedTape.I := faceI ibox76 1 false
private noncomputable def ibox78 : Fin 4 → FixedTape.I := splitI ibox77 3 35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 false
private noncomputable def ibox79 : Fin 4 → FixedTape.I := splitI ibox78 0 894668512651319589736685742111688896383393113256755200000000000000000000000000000000000 false
private noncomputable def ibox80 : Fin 4 → FixedTape.I := splitI ibox78 0 894668512651319589736685742111688896383393113256755200000000000000000000000000000000000 true
private noncomputable def ibox81 : Fin 4 → FixedTape.I := splitI ibox77 3 35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 true
private noncomputable def ibox82 : Fin 4 → FixedTape.I := splitI ibox81 3 53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 false
private noncomputable def ibox83 : Fin 4 → FixedTape.I := splitI ibox81 3 53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 true
private noncomputable def ibox84 : Fin 4 → FixedTape.I := splitI ibox75 0 925168302228710852117499724528350199902861815237836800000000000000000000000000000000000 true
private noncomputable def ibox85 : Fin 4 → FixedTape.I := faceI ibox84 1 false
private noncomputable def ibox86 : Fin 4 → FixedTape.I := splitI ibox85 3 35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 false
private noncomputable def ibox87 : Fin 4 → FixedTape.I := splitI ibox86 0 955668091806102114498313706945011503422330517218918400000000000000000000000000000000000 false
private noncomputable def ibox88 : Fin 4 → FixedTape.I := splitI ibox86 0 955668091806102114498313706945011503422330517218918400000000000000000000000000000000000 true
private noncomputable def ibox89 : Fin 4 → FixedTape.I := splitI ibox85 3 35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 true
private noncomputable def ibox90 : Fin 4 → FixedTape.I := splitI ibox74 1 8906034777172359903977615699371622400000000000000000000000000000000000000000000000000000 true
private noncomputable def ibox91 : Fin 4 → FixedTape.I := splitI ibox90 3 35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 false
private noncomputable def ibox92 : Fin 4 → FixedTape.I := splitI ibox91 0 925168302228710852117499724528350199902861815237836800000000000000000000000000000000000 false
private noncomputable def ibox93 : Fin 4 → FixedTape.I := faceI ibox92 1 false
private noncomputable def ibox94 : Fin 4 → FixedTape.I := splitI ibox91 0 925168302228710852117499724528350199902861815237836800000000000000000000000000000000000 true
private noncomputable def ibox95 : Fin 4 → FixedTape.I := splitI ibox90 3 35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 true
private noncomputable def ibox96 : Fin 4 → FixedTape.I := faceI ibox95 1 false
private noncomputable def ibox97 : Fin 4 → FixedTape.I := splitI ibox73 1 17812069554344719807955231398743244800000000000000000000000000000000000000000000000000000 true
private noncomputable def ibox98 : Fin 4 → FixedTape.I := splitI ibox97 1 26718104331517079711932847098114867200000000000000000000000000000000000000000000000000000 false
private noncomputable def ibox99 : Fin 4 → FixedTape.I := splitI ibox98 3 35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 false
private noncomputable def ibox100 : Fin 4 → FixedTape.I := splitI ibox99 0 925168302228710852117499724528350199902861815237836800000000000000000000000000000000000 false
private noncomputable def ibox101 : Fin 4 → FixedTape.I := splitI ibox99 0 925168302228710852117499724528350199902861815237836800000000000000000000000000000000000 true
private noncomputable def ibox102 : Fin 4 → FixedTape.I := splitI ibox98 3 35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 true
private noncomputable def ibox103 : Fin 4 → FixedTape.I := splitI ibox97 1 26718104331517079711932847098114867200000000000000000000000000000000000000000000000000000 true
private noncomputable def ibox104 : Fin 4 → FixedTape.I := faceI ibox103 3 false
private noncomputable def ibox105 : Fin 4 → FixedTape.I := splitI ibox71 1 35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 true
private noncomputable def ibox106 : Fin 4 → FixedTape.I := faceI ibox105 3 false
private noncomputable def ibox107 : Fin 4 → FixedTape.I := splitI ibox106 0 925168302228710852117499724528350199902861815237836800000000000000000000000000000000000 false
private noncomputable def ibox108 : Fin 4 → FixedTape.I := splitI ibox107 1 53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 false
private noncomputable def ibox109 : Fin 4 → FixedTape.I := splitI ibox107 1 53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 true
private noncomputable def ibox110 : Fin 4 → FixedTape.I := splitI ibox106 0 925168302228710852117499724528350199902861815237836800000000000000000000000000000000000 true
private noncomputable def ibox111 : Fin 4 → FixedTape.I := splitI ibox110 1 53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 false
private noncomputable def ibox112 : Fin 4 → FixedTape.I := splitI ibox110 1 53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 true
private noncomputable def tree112 : TapeTree := .centered (candidateRows ibox112) (candidateRows (FixedTape.midBox ibox112))
attribute [irreducible] tree112
private theorem sign_112 : 2*denominator*(computed denominator (FixedTape.midBox ibox112)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox112).gradient k).lo.natAbs ((computed denominator ibox112).gradient k).hi.natAbs : Int)*((ibox112 k).hi-(ibox112 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox112
    (computed denominator ibox112) (computed denominator (FixedTape.midBox ibox112))
    (by decide +kernel)
private theorem midpoint_even_112 : ∀ k, 2 ∣ (ibox112 k).lo+(ibox112 k).hi := by decide +kernel
private theorem accepted_112 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox112) tree112 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox112 midpoint_even_112
  simp only [tree112,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox112,candidate_valid h (FixedTape.midBox ibox112),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox112 212 (FixedTape.rowsAux denominator ibox112 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox112) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_112
private noncomputable def tree111 : TapeTree := .centered (candidateRows ibox111) (candidateRows (FixedTape.midBox ibox111))
attribute [irreducible] tree111
private theorem sign_111 : 2*denominator*(computed denominator (FixedTape.midBox ibox111)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox111).gradient k).lo.natAbs ((computed denominator ibox111).gradient k).hi.natAbs : Int)*((ibox111 k).hi-(ibox111 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox111
    (computed denominator ibox111) (computed denominator (FixedTape.midBox ibox111))
    (by decide +kernel)
private theorem midpoint_even_111 : ∀ k, 2 ∣ (ibox111 k).lo+(ibox111 k).hi := by decide +kernel
private theorem accepted_111 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox111) tree111 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox111 midpoint_even_111
  simp only [tree111,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox111,candidate_valid h (FixedTape.midBox ibox111),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox111 212 (FixedTape.rowsAux denominator ibox111 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox111) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_111
private noncomputable def tree110 : TapeTree := .split 1 (((53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree111 tree112
attribute [irreducible] tree110
private theorem accepted_110 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox110) tree110 = true := by
  simp only [tree110,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox110 1 (53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 : Int) false,decode_split denominator ibox110 1 (53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_111 h,accepted_112 h⟩
private noncomputable def tree109 : TapeTree := .centered (candidateRows ibox109) (candidateRows (FixedTape.midBox ibox109))
attribute [irreducible] tree109
private theorem sign_109 : 2*denominator*(computed denominator (FixedTape.midBox ibox109)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox109).gradient k).lo.natAbs ((computed denominator ibox109).gradient k).hi.natAbs : Int)*((ibox109 k).hi-(ibox109 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox109
    (computed denominator ibox109) (computed denominator (FixedTape.midBox ibox109))
    (by decide +kernel)
private theorem midpoint_even_109 : ∀ k, 2 ∣ (ibox109 k).lo+(ibox109 k).hi := by decide +kernel
private theorem accepted_109 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox109) tree109 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox109 midpoint_even_109
  simp only [tree109,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox109,candidate_valid h (FixedTape.midBox ibox109),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox109 212 (FixedTape.rowsAux denominator ibox109 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox109) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_109
private noncomputable def tree108 : TapeTree := .centered (candidateRows ibox108) (candidateRows (FixedTape.midBox ibox108))
attribute [irreducible] tree108
private theorem sign_108 : 2*denominator*(computed denominator (FixedTape.midBox ibox108)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox108).gradient k).lo.natAbs ((computed denominator ibox108).gradient k).hi.natAbs : Int)*((ibox108 k).hi-(ibox108 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox108
    (computed denominator ibox108) (computed denominator (FixedTape.midBox ibox108))
    (by decide +kernel)
private theorem midpoint_even_108 : ∀ k, 2 ∣ (ibox108 k).lo+(ibox108 k).hi := by decide +kernel
private theorem accepted_108 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox108) tree108 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox108 midpoint_even_108
  simp only [tree108,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox108,candidate_valid h (FixedTape.midBox ibox108),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox108 212 (FixedTape.rowsAux denominator ibox108 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox108) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_108
private noncomputable def tree107 : TapeTree := .split 1 (((53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree108 tree109
attribute [irreducible] tree107
private theorem accepted_107 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox107) tree107 = true := by
  simp only [tree107,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox107 1 (53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 : Int) false,decode_split denominator ibox107 1 (53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_108 h,accepted_109 h⟩
private noncomputable def tree106 : TapeTree := .split 0 (((925168302228710852117499724528350199902861815237836800000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree107 tree110
attribute [irreducible] tree106
private theorem accepted_106 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox106) tree106 = true := by
  simp only [tree106,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox106 0 (925168302228710852117499724528350199902861815237836800000000000000000000000000000000000 : Int) false,decode_split denominator ibox106 0 (925168302228710852117499724528350199902861815237836800000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_107 h,accepted_110 h⟩
private noncomputable def tree105 : TapeTree := .face 3 false (candidateRows ibox105) tree106
attribute [irreducible] tree105
private theorem sign_105 : ((computed denominator ibox105).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_105 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox105) tree105 = true := by
  simp only [tree105,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox105,?_,accepted_106 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox105)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox105).gradient 3).hi) denominator_positive).1 sign_105
private noncomputable def tree104 : TapeTree := .centered (candidateRows ibox104) (candidateRows (FixedTape.midBox ibox104))
attribute [irreducible] tree104
private theorem sign_104 : 2*denominator*(computed denominator (FixedTape.midBox ibox104)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox104).gradient k).lo.natAbs ((computed denominator ibox104).gradient k).hi.natAbs : Int)*((ibox104 k).hi-(ibox104 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox104
    (computed denominator ibox104) (computed denominator (FixedTape.midBox ibox104))
    (by decide +kernel)
private theorem midpoint_even_104 : ∀ k, 2 ∣ (ibox104 k).lo+(ibox104 k).hi := by decide +kernel
private theorem accepted_104 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox104) tree104 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox104 midpoint_even_104
  simp only [tree104,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox104,candidate_valid h (FixedTape.midBox ibox104),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox104 212 (FixedTape.rowsAux denominator ibox104 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox104) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_104
private noncomputable def tree103 : TapeTree := .face 3 false (candidateRows ibox103) tree104
attribute [irreducible] tree103
private theorem sign_103 : ((computed denominator ibox103).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_103 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox103) tree103 = true := by
  simp only [tree103,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox103,?_,accepted_104 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox103)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox103).gradient 3).hi) denominator_positive).1 sign_103
private noncomputable def tree102 : TapeTree := .centered (candidateRows ibox102) (candidateRows (FixedTape.midBox ibox102))
attribute [irreducible] tree102
private theorem sign_102 : 2*denominator*(computed denominator (FixedTape.midBox ibox102)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox102).gradient k).lo.natAbs ((computed denominator ibox102).gradient k).hi.natAbs : Int)*((ibox102 k).hi-(ibox102 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox102
    (computed denominator ibox102) (computed denominator (FixedTape.midBox ibox102))
    (by decide +kernel)
private theorem midpoint_even_102 : ∀ k, 2 ∣ (ibox102 k).lo+(ibox102 k).hi := by decide +kernel
private theorem accepted_102 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox102) tree102 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox102 midpoint_even_102
  simp only [tree102,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox102,candidate_valid h (FixedTape.midBox ibox102),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox102 212 (FixedTape.rowsAux denominator ibox102 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox102) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_102
private noncomputable def tree101 : TapeTree := .centered (candidateRows ibox101) (candidateRows (FixedTape.midBox ibox101))
attribute [irreducible] tree101
private theorem sign_101 : 2*denominator*(computed denominator (FixedTape.midBox ibox101)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox101).gradient k).lo.natAbs ((computed denominator ibox101).gradient k).hi.natAbs : Int)*((ibox101 k).hi-(ibox101 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox101
    (computed denominator ibox101) (computed denominator (FixedTape.midBox ibox101))
    (by decide +kernel)
private theorem midpoint_even_101 : ∀ k, 2 ∣ (ibox101 k).lo+(ibox101 k).hi := by decide +kernel
private theorem accepted_101 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox101) tree101 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox101 midpoint_even_101
  simp only [tree101,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox101,candidate_valid h (FixedTape.midBox ibox101),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox101 212 (FixedTape.rowsAux denominator ibox101 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox101) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_101
private noncomputable def tree100 : TapeTree := .centered (candidateRows ibox100) (candidateRows (FixedTape.midBox ibox100))
attribute [irreducible] tree100
private theorem sign_100 : 2*denominator*(computed denominator (FixedTape.midBox ibox100)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox100).gradient k).lo.natAbs ((computed denominator ibox100).gradient k).hi.natAbs : Int)*((ibox100 k).hi-(ibox100 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox100
    (computed denominator ibox100) (computed denominator (FixedTape.midBox ibox100))
    (by decide +kernel)
private theorem midpoint_even_100 : ∀ k, 2 ∣ (ibox100 k).lo+(ibox100 k).hi := by decide +kernel
private theorem accepted_100 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox100) tree100 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox100 midpoint_even_100
  simp only [tree100,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox100,candidate_valid h (FixedTape.midBox ibox100),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox100 212 (FixedTape.rowsAux denominator ibox100 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox100) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_100
private noncomputable def tree99 : TapeTree := .split 0 (((925168302228710852117499724528350199902861815237836800000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree100 tree101
attribute [irreducible] tree99
private theorem accepted_99 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox99) tree99 = true := by
  simp only [tree99,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox99 0 (925168302228710852117499724528350199902861815237836800000000000000000000000000000000000 : Int) false,decode_split denominator ibox99 0 (925168302228710852117499724528350199902861815237836800000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_100 h,accepted_101 h⟩
private noncomputable def tree98 : TapeTree := .split 3 (((35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree99 tree102
attribute [irreducible] tree98
private theorem accepted_98 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox98) tree98 = true := by
  simp only [tree98,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox98 3 (35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) false,decode_split denominator ibox98 3 (35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_99 h,accepted_102 h⟩
private noncomputable def tree97 : TapeTree := .split 1 (((26718104331517079711932847098114867200000000000000000000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree98 tree103
attribute [irreducible] tree97
private theorem accepted_97 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox97) tree97 = true := by
  simp only [tree97,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox97 1 (26718104331517079711932847098114867200000000000000000000000000000000000000000000000000000 : Int) false,decode_split denominator ibox97 1 (26718104331517079711932847098114867200000000000000000000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_98 h,accepted_103 h⟩
private noncomputable def tree96 : TapeTree := .centered (candidateRows ibox96) (candidateRows (FixedTape.midBox ibox96))
attribute [irreducible] tree96
private theorem sign_96 : 2*denominator*(computed denominator (FixedTape.midBox ibox96)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox96).gradient k).lo.natAbs ((computed denominator ibox96).gradient k).hi.natAbs : Int)*((ibox96 k).hi-(ibox96 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox96
    (computed denominator ibox96) (computed denominator (FixedTape.midBox ibox96))
    (by decide +kernel)
private theorem midpoint_even_96 : ∀ k, 2 ∣ (ibox96 k).lo+(ibox96 k).hi := by decide +kernel
private theorem accepted_96 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox96) tree96 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox96 midpoint_even_96
  simp only [tree96,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox96,candidate_valid h (FixedTape.midBox ibox96),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox96 212 (FixedTape.rowsAux denominator ibox96 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox96) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_96
private noncomputable def tree95 : TapeTree := .face 1 false (candidateRows ibox95) tree96
attribute [irreducible] tree95
private theorem sign_95 : ((computed denominator ibox95).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_95 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox95) tree95 = true := by
  simp only [tree95,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox95,?_,accepted_96 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox95)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox95).gradient 1).hi) denominator_positive).1 sign_95
private noncomputable def tree94 : TapeTree := .centered (candidateRows ibox94) (candidateRows (FixedTape.midBox ibox94))
attribute [irreducible] tree94
private theorem sign_94 : 2*denominator*(computed denominator (FixedTape.midBox ibox94)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox94).gradient k).lo.natAbs ((computed denominator ibox94).gradient k).hi.natAbs : Int)*((ibox94 k).hi-(ibox94 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox94
    (computed denominator ibox94) (computed denominator (FixedTape.midBox ibox94))
    (by decide +kernel)
private theorem midpoint_even_94 : ∀ k, 2 ∣ (ibox94 k).lo+(ibox94 k).hi := by decide +kernel
private theorem accepted_94 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox94) tree94 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox94 midpoint_even_94
  simp only [tree94,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox94,candidate_valid h (FixedTape.midBox ibox94),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox94 212 (FixedTape.rowsAux denominator ibox94 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox94) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_94
private noncomputable def tree93 : TapeTree := .centered (candidateRows ibox93) (candidateRows (FixedTape.midBox ibox93))
attribute [irreducible] tree93
private theorem sign_93 : 2*denominator*(computed denominator (FixedTape.midBox ibox93)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox93).gradient k).lo.natAbs ((computed denominator ibox93).gradient k).hi.natAbs : Int)*((ibox93 k).hi-(ibox93 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox93
    (computed denominator ibox93) (computed denominator (FixedTape.midBox ibox93))
    (by decide +kernel)
private theorem midpoint_even_93 : ∀ k, 2 ∣ (ibox93 k).lo+(ibox93 k).hi := by decide +kernel
private theorem accepted_93 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox93) tree93 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox93 midpoint_even_93
  simp only [tree93,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox93,candidate_valid h (FixedTape.midBox ibox93),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox93 212 (FixedTape.rowsAux denominator ibox93 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox93) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_93
private noncomputable def tree92 : TapeTree := .face 1 false (candidateRows ibox92) tree93
attribute [irreducible] tree92
private theorem sign_92 : ((computed denominator ibox92).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_92 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox92) tree92 = true := by
  simp only [tree92,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox92,?_,accepted_93 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox92)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox92).gradient 1).hi) denominator_positive).1 sign_92
private noncomputable def tree91 : TapeTree := .split 0 (((925168302228710852117499724528350199902861815237836800000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree92 tree94
attribute [irreducible] tree91
private theorem accepted_91 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox91) tree91 = true := by
  simp only [tree91,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox91 0 (925168302228710852117499724528350199902861815237836800000000000000000000000000000000000 : Int) false,decode_split denominator ibox91 0 (925168302228710852117499724528350199902861815237836800000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_92 h,accepted_94 h⟩
private noncomputable def tree90 : TapeTree := .split 3 (((35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree91 tree95
attribute [irreducible] tree90
private theorem accepted_90 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox90) tree90 = true := by
  simp only [tree90,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox90 3 (35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) false,decode_split denominator ibox90 3 (35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_91 h,accepted_95 h⟩
private noncomputable def tree89 : TapeTree := .centered (candidateRows ibox89) (candidateRows (FixedTape.midBox ibox89))
attribute [irreducible] tree89
private theorem sign_89 : 2*denominator*(computed denominator (FixedTape.midBox ibox89)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox89).gradient k).lo.natAbs ((computed denominator ibox89).gradient k).hi.natAbs : Int)*((ibox89 k).hi-(ibox89 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox89
    (computed denominator ibox89) (computed denominator (FixedTape.midBox ibox89))
    (by decide +kernel)
private theorem midpoint_even_89 : ∀ k, 2 ∣ (ibox89 k).lo+(ibox89 k).hi := by decide +kernel
private theorem accepted_89 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox89) tree89 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox89 midpoint_even_89
  simp only [tree89,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox89,candidate_valid h (FixedTape.midBox ibox89),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox89 212 (FixedTape.rowsAux denominator ibox89 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox89) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_89
private noncomputable def tree88 : TapeTree := .centered (candidateRows ibox88) (candidateRows (FixedTape.midBox ibox88))
attribute [irreducible] tree88
private theorem sign_88 : 2*denominator*(computed denominator (FixedTape.midBox ibox88)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox88).gradient k).lo.natAbs ((computed denominator ibox88).gradient k).hi.natAbs : Int)*((ibox88 k).hi-(ibox88 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox88
    (computed denominator ibox88) (computed denominator (FixedTape.midBox ibox88))
    (by decide +kernel)
private theorem midpoint_even_88 : ∀ k, 2 ∣ (ibox88 k).lo+(ibox88 k).hi := by decide +kernel
private theorem accepted_88 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox88) tree88 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox88 midpoint_even_88
  simp only [tree88,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox88,candidate_valid h (FixedTape.midBox ibox88),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox88 212 (FixedTape.rowsAux denominator ibox88 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox88) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_88
private noncomputable def tree87 : TapeTree := .centered (candidateRows ibox87) (candidateRows (FixedTape.midBox ibox87))
attribute [irreducible] tree87
private theorem sign_87 : 2*denominator*(computed denominator (FixedTape.midBox ibox87)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox87).gradient k).lo.natAbs ((computed denominator ibox87).gradient k).hi.natAbs : Int)*((ibox87 k).hi-(ibox87 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox87
    (computed denominator ibox87) (computed denominator (FixedTape.midBox ibox87))
    (by decide +kernel)
private theorem midpoint_even_87 : ∀ k, 2 ∣ (ibox87 k).lo+(ibox87 k).hi := by decide +kernel
private theorem accepted_87 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox87) tree87 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox87 midpoint_even_87
  simp only [tree87,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox87,candidate_valid h (FixedTape.midBox ibox87),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox87 212 (FixedTape.rowsAux denominator ibox87 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox87) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_87
private noncomputable def tree86 : TapeTree := .split 0 (((955668091806102114498313706945011503422330517218918400000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree87 tree88
attribute [irreducible] tree86
private theorem accepted_86 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox86) tree86 = true := by
  simp only [tree86,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox86 0 (955668091806102114498313706945011503422330517218918400000000000000000000000000000000000 : Int) false,decode_split denominator ibox86 0 (955668091806102114498313706945011503422330517218918400000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_87 h,accepted_88 h⟩
private noncomputable def tree85 : TapeTree := .split 3 (((35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree86 tree89
attribute [irreducible] tree85
private theorem accepted_85 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox85) tree85 = true := by
  simp only [tree85,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox85 3 (35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) false,decode_split denominator ibox85 3 (35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_86 h,accepted_89 h⟩
private noncomputable def tree84 : TapeTree := .face 1 false (candidateRows ibox84) tree85
attribute [irreducible] tree84
private theorem sign_84 : ((computed denominator ibox84).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_84 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox84) tree84 = true := by
  simp only [tree84,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox84,?_,accepted_85 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox84)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox84).gradient 1).hi) denominator_positive).1 sign_84
private noncomputable def tree83 : TapeTree := .centered (candidateRows ibox83) (candidateRows (FixedTape.midBox ibox83))
attribute [irreducible] tree83
private theorem sign_83 : 2*denominator*(computed denominator (FixedTape.midBox ibox83)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox83).gradient k).lo.natAbs ((computed denominator ibox83).gradient k).hi.natAbs : Int)*((ibox83 k).hi-(ibox83 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox83
    (computed denominator ibox83) (computed denominator (FixedTape.midBox ibox83))
    (by decide +kernel)
private theorem midpoint_even_83 : ∀ k, 2 ∣ (ibox83 k).lo+(ibox83 k).hi := by decide +kernel
private theorem accepted_83 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox83) tree83 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox83 midpoint_even_83
  simp only [tree83,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox83,candidate_valid h (FixedTape.midBox ibox83),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox83 212 (FixedTape.rowsAux denominator ibox83 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox83) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_83
private noncomputable def tree82 : TapeTree := .centered (candidateRows ibox82) (candidateRows (FixedTape.midBox ibox82))
attribute [irreducible] tree82
private theorem sign_82 : 2*denominator*(computed denominator (FixedTape.midBox ibox82)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox82).gradient k).lo.natAbs ((computed denominator ibox82).gradient k).hi.natAbs : Int)*((ibox82 k).hi-(ibox82 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox82
    (computed denominator ibox82) (computed denominator (FixedTape.midBox ibox82))
    (by decide +kernel)
private theorem midpoint_even_82 : ∀ k, 2 ∣ (ibox82 k).lo+(ibox82 k).hi := by decide +kernel
private theorem accepted_82 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox82) tree82 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox82 midpoint_even_82
  simp only [tree82,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox82,candidate_valid h (FixedTape.midBox ibox82),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox82 212 (FixedTape.rowsAux denominator ibox82 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox82) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_82
private noncomputable def tree81 : TapeTree := .split 3 (((53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree82 tree83
attribute [irreducible] tree81
private theorem accepted_81 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox81) tree81 = true := by
  simp only [tree81,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox81 3 (53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 : Int) false,decode_split denominator ibox81 3 (53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_82 h,accepted_83 h⟩
private noncomputable def tree80 : TapeTree := .centered (candidateRows ibox80) (candidateRows (FixedTape.midBox ibox80))
attribute [irreducible] tree80
private theorem sign_80 : 2*denominator*(computed denominator (FixedTape.midBox ibox80)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox80).gradient k).lo.natAbs ((computed denominator ibox80).gradient k).hi.natAbs : Int)*((ibox80 k).hi-(ibox80 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox80
    (computed denominator ibox80) (computed denominator (FixedTape.midBox ibox80))
    (by decide +kernel)
private theorem midpoint_even_80 : ∀ k, 2 ∣ (ibox80 k).lo+(ibox80 k).hi := by decide +kernel
private theorem accepted_80 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox80) tree80 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox80 midpoint_even_80
  simp only [tree80,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox80,candidate_valid h (FixedTape.midBox ibox80),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox80 212 (FixedTape.rowsAux denominator ibox80 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox80) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_80
private noncomputable def tree79 : TapeTree := .centered (candidateRows ibox79) (candidateRows (FixedTape.midBox ibox79))
attribute [irreducible] tree79
private theorem sign_79 : 2*denominator*(computed denominator (FixedTape.midBox ibox79)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox79).gradient k).lo.natAbs ((computed denominator ibox79).gradient k).hi.natAbs : Int)*((ibox79 k).hi-(ibox79 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox79
    (computed denominator ibox79) (computed denominator (FixedTape.midBox ibox79))
    (by decide +kernel)
private theorem midpoint_even_79 : ∀ k, 2 ∣ (ibox79 k).lo+(ibox79 k).hi := by decide +kernel
private theorem accepted_79 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox79) tree79 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox79 midpoint_even_79
  simp only [tree79,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox79,candidate_valid h (FixedTape.midBox ibox79),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox79 212 (FixedTape.rowsAux denominator ibox79 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox79) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_79
private noncomputable def tree78 : TapeTree := .split 0 (((894668512651319589736685742111688896383393113256755200000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree79 tree80
attribute [irreducible] tree78
private theorem accepted_78 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox78) tree78 = true := by
  simp only [tree78,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox78 0 (894668512651319589736685742111688896383393113256755200000000000000000000000000000000000 : Int) false,decode_split denominator ibox78 0 (894668512651319589736685742111688896383393113256755200000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_79 h,accepted_80 h⟩
private noncomputable def tree77 : TapeTree := .split 3 (((35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree78 tree81
attribute [irreducible] tree77
private theorem accepted_77 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox77) tree77 = true := by
  simp only [tree77,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox77 3 (35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) false,decode_split denominator ibox77 3 (35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_78 h,accepted_81 h⟩
private noncomputable def tree76 : TapeTree := .face 1 false (candidateRows ibox76) tree77
attribute [irreducible] tree76
private theorem sign_76 : ((computed denominator ibox76).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_76 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox76) tree76 = true := by
  simp only [tree76,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox76,?_,accepted_77 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox76)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox76).gradient 1).hi) denominator_positive).1 sign_76
private noncomputable def tree75 : TapeTree := .split 0 (((925168302228710852117499724528350199902861815237836800000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree76 tree84
attribute [irreducible] tree75
private theorem accepted_75 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox75) tree75 = true := by
  simp only [tree75,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox75 0 (925168302228710852117499724528350199902861815237836800000000000000000000000000000000000 : Int) false,decode_split denominator ibox75 0 (925168302228710852117499724528350199902861815237836800000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_76 h,accepted_84 h⟩
private noncomputable def tree74 : TapeTree := .split 1 (((8906034777172359903977615699371622400000000000000000000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree75 tree90
attribute [irreducible] tree74
private theorem accepted_74 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox74) tree74 = true := by
  simp only [tree74,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox74 1 (8906034777172359903977615699371622400000000000000000000000000000000000000000000000000000 : Int) false,decode_split denominator ibox74 1 (8906034777172359903977615699371622400000000000000000000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_75 h,accepted_90 h⟩
private noncomputable def tree73 : TapeTree := .split 1 (((17812069554344719807955231398743244800000000000000000000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree74 tree97
attribute [irreducible] tree73
private theorem accepted_73 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox73) tree73 = true := by
  simp only [tree73,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox73 1 (17812069554344719807955231398743244800000000000000000000000000000000000000000000000000000 : Int) false,decode_split denominator ibox73 1 (17812069554344719807955231398743244800000000000000000000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_74 h,accepted_97 h⟩
private noncomputable def tree72 : TapeTree := .face 2 true (candidateRows ibox72) tree73
attribute [irreducible] tree72
private theorem sign_72 : 0 ≤ ((computed denominator ibox72).gradient 2).lo := by decide +kernel
private theorem accepted_72 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox72) tree72 = true := by
  simp only [tree72,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox72,?_,accepted_73 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox72)).gradient 2).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox72).gradient 2).lo) denominator_positive).2 sign_72
private noncomputable def tree71 : TapeTree := .split 1 (((35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree72 tree105
attribute [irreducible] tree71
private theorem accepted_71 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox71) tree71 = true := by
  simp only [tree71,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox71 1 (35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) false,decode_split denominator ibox71 1 (35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_72 h,accepted_105 h⟩
private noncomputable def tree70 : TapeTree := .centered (candidateRows ibox70) (candidateRows (FixedTape.midBox ibox70))
attribute [irreducible] tree70
private theorem sign_70 : 2*denominator*(computed denominator (FixedTape.midBox ibox70)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox70).gradient k).lo.natAbs ((computed denominator ibox70).gradient k).hi.natAbs : Int)*((ibox70 k).hi-(ibox70 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox70
    (computed denominator ibox70) (computed denominator (FixedTape.midBox ibox70))
    (by decide +kernel)
private theorem midpoint_even_70 : ∀ k, 2 ∣ (ibox70 k).lo+(ibox70 k).hi := by decide +kernel
private theorem accepted_70 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox70) tree70 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox70 midpoint_even_70
  simp only [tree70,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox70,candidate_valid h (FixedTape.midBox ibox70),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox70 212 (FixedTape.rowsAux denominator ibox70 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox70) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_70
private noncomputable def tree69 : TapeTree := .centered (candidateRows ibox69) (candidateRows (FixedTape.midBox ibox69))
attribute [irreducible] tree69
private theorem sign_69 : 2*denominator*(computed denominator (FixedTape.midBox ibox69)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox69).gradient k).lo.natAbs ((computed denominator ibox69).gradient k).hi.natAbs : Int)*((ibox69 k).hi-(ibox69 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox69
    (computed denominator ibox69) (computed denominator (FixedTape.midBox ibox69))
    (by decide +kernel)
private theorem midpoint_even_69 : ∀ k, 2 ∣ (ibox69 k).lo+(ibox69 k).hi := by decide +kernel
private theorem accepted_69 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox69) tree69 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox69 midpoint_even_69
  simp only [tree69,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox69,candidate_valid h (FixedTape.midBox ibox69),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox69 212 (FixedTape.rowsAux denominator ibox69 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox69) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_69
private noncomputable def tree68 : TapeTree := .split 0 (((925168302228710852117499724528350199902861815237836800000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree69 tree70
attribute [irreducible] tree68
private theorem accepted_68 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox68) tree68 = true := by
  simp only [tree68,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox68 0 (925168302228710852117499724528350199902861815237836800000000000000000000000000000000000 : Int) false,decode_split denominator ibox68 0 (925168302228710852117499724528350199902861815237836800000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_69 h,accepted_70 h⟩
private noncomputable def tree67 : TapeTree := .centered (candidateRows ibox67) (candidateRows (FixedTape.midBox ibox67))
attribute [irreducible] tree67
private theorem sign_67 : 2*denominator*(computed denominator (FixedTape.midBox ibox67)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox67).gradient k).lo.natAbs ((computed denominator ibox67).gradient k).hi.natAbs : Int)*((ibox67 k).hi-(ibox67 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox67
    (computed denominator ibox67) (computed denominator (FixedTape.midBox ibox67))
    (by decide +kernel)
private theorem midpoint_even_67 : ∀ k, 2 ∣ (ibox67 k).lo+(ibox67 k).hi := by decide +kernel
private theorem accepted_67 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox67) tree67 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox67 midpoint_even_67
  simp only [tree67,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox67,candidate_valid h (FixedTape.midBox ibox67),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox67 212 (FixedTape.rowsAux denominator ibox67 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox67) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_67
private noncomputable def tree66 : TapeTree := .face 2 true (candidateRows ibox66) tree67
attribute [irreducible] tree66
private theorem sign_66 : 0 ≤ ((computed denominator ibox66).gradient 2).lo := by decide +kernel
private theorem accepted_66 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox66) tree66 = true := by
  simp only [tree66,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox66,?_,accepted_67 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox66)).gradient 2).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox66).gradient 2).lo) denominator_positive).2 sign_66
private noncomputable def tree65 : TapeTree := .split 1 (((35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree66 tree68
attribute [irreducible] tree65
private theorem accepted_65 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox65) tree65 = true := by
  simp only [tree65,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox65 1 (35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) false,decode_split denominator ibox65 1 (35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_66 h,accepted_68 h⟩
private noncomputable def tree64 : TapeTree := .face 3 false (candidateRows ibox64) tree65
attribute [irreducible] tree64
private theorem sign_64 : ((computed denominator ibox64).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_64 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox64) tree64 = true := by
  simp only [tree64,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox64,?_,accepted_65 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox64)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox64).gradient 3).hi) denominator_positive).1 sign_64
private noncomputable def tree63 : TapeTree := .split 2 (((53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree64 tree71
attribute [irreducible] tree63
private theorem accepted_63 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox63) tree63 = true := by
  simp only [tree63,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox63 2 (53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 : Int) false,decode_split denominator ibox63 2 (53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_64 h,accepted_71 h⟩
private noncomputable def tree62 : TapeTree := .centered (candidateRows ibox62) (candidateRows (FixedTape.midBox ibox62))
attribute [irreducible] tree62
private theorem sign_62 : 2*denominator*(computed denominator (FixedTape.midBox ibox62)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox62).gradient k).lo.natAbs ((computed denominator ibox62).gradient k).hi.natAbs : Int)*((ibox62 k).hi-(ibox62 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox62
    (computed denominator ibox62) (computed denominator (FixedTape.midBox ibox62))
    (by decide +kernel)
private theorem midpoint_even_62 : ∀ k, 2 ∣ (ibox62 k).lo+(ibox62 k).hi := by decide +kernel
private theorem accepted_62 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox62) tree62 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox62 midpoint_even_62
  simp only [tree62,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox62,candidate_valid h (FixedTape.midBox ibox62),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox62 212 (FixedTape.rowsAux denominator ibox62 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox62) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_62
private noncomputable def tree61 : TapeTree := .centered (candidateRows ibox61) (candidateRows (FixedTape.midBox ibox61))
attribute [irreducible] tree61
private theorem sign_61 : 2*denominator*(computed denominator (FixedTape.midBox ibox61)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox61).gradient k).lo.natAbs ((computed denominator ibox61).gradient k).hi.natAbs : Int)*((ibox61 k).hi-(ibox61 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox61
    (computed denominator ibox61) (computed denominator (FixedTape.midBox ibox61))
    (by decide +kernel)
private theorem midpoint_even_61 : ∀ k, 2 ∣ (ibox61 k).lo+(ibox61 k).hi := by decide +kernel
private theorem accepted_61 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox61) tree61 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox61 midpoint_even_61
  simp only [tree61,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox61,candidate_valid h (FixedTape.midBox ibox61),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox61 212 (FixedTape.rowsAux denominator ibox61 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox61) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_61
private noncomputable def tree60 : TapeTree := .split 1 (((53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree61 tree62
attribute [irreducible] tree60
private theorem accepted_60 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox60) tree60 = true := by
  simp only [tree60,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox60 1 (53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 : Int) false,decode_split denominator ibox60 1 (53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_61 h,accepted_62 h⟩
private noncomputable def tree59 : TapeTree := .centered (candidateRows ibox59) (candidateRows (FixedTape.midBox ibox59))
attribute [irreducible] tree59
private theorem sign_59 : 2*denominator*(computed denominator (FixedTape.midBox ibox59)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox59).gradient k).lo.natAbs ((computed denominator ibox59).gradient k).hi.natAbs : Int)*((ibox59 k).hi-(ibox59 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox59
    (computed denominator ibox59) (computed denominator (FixedTape.midBox ibox59))
    (by decide +kernel)
private theorem midpoint_even_59 : ∀ k, 2 ∣ (ibox59 k).lo+(ibox59 k).hi := by decide +kernel
private theorem accepted_59 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox59) tree59 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox59 midpoint_even_59
  simp only [tree59,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox59,candidate_valid h (FixedTape.midBox ibox59),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox59 212 (FixedTape.rowsAux denominator ibox59 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox59) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_59
private noncomputable def tree58 : TapeTree := .centered (candidateRows ibox58) (candidateRows (FixedTape.midBox ibox58))
attribute [irreducible] tree58
private theorem sign_58 : 2*denominator*(computed denominator (FixedTape.midBox ibox58)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox58).gradient k).lo.natAbs ((computed denominator ibox58).gradient k).hi.natAbs : Int)*((ibox58 k).hi-(ibox58 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox58
    (computed denominator ibox58) (computed denominator (FixedTape.midBox ibox58))
    (by decide +kernel)
private theorem midpoint_even_58 : ∀ k, 2 ∣ (ibox58 k).lo+(ibox58 k).hi := by decide +kernel
private theorem accepted_58 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox58) tree58 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox58 midpoint_even_58
  simp only [tree58,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox58,candidate_valid h (FixedTape.midBox ibox58),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox58 212 (FixedTape.rowsAux denominator ibox58 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox58) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_58
private noncomputable def tree57 : TapeTree := .split 1 (((53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree58 tree59
attribute [irreducible] tree57
private theorem accepted_57 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox57) tree57 = true := by
  simp only [tree57,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox57 1 (53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 : Int) false,decode_split denominator ibox57 1 (53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_58 h,accepted_59 h⟩
private noncomputable def tree56 : TapeTree := .split 0 (((803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree57 tree60
attribute [irreducible] tree56
private theorem accepted_56 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox56) tree56 = true := by
  simp only [tree56,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox56 0 (803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 : Int) false,decode_split denominator ibox56 0 (803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_57 h,accepted_60 h⟩
private noncomputable def tree55 : TapeTree := .face 3 false (candidateRows ibox55) tree56
attribute [irreducible] tree55
private theorem sign_55 : ((computed denominator ibox55).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_55 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox55) tree55 = true := by
  simp only [tree55,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox55,?_,accepted_56 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox55)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox55).gradient 3).hi) denominator_positive).1 sign_55
private noncomputable def tree54 : TapeTree := .centered (candidateRows ibox54) (candidateRows (FixedTape.midBox ibox54))
attribute [irreducible] tree54
private theorem sign_54 : 2*denominator*(computed denominator (FixedTape.midBox ibox54)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox54).gradient k).lo.natAbs ((computed denominator ibox54).gradient k).hi.natAbs : Int)*((ibox54 k).hi-(ibox54 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox54
    (computed denominator ibox54) (computed denominator (FixedTape.midBox ibox54))
    (by decide +kernel)
private theorem midpoint_even_54 : ∀ k, 2 ∣ (ibox54 k).lo+(ibox54 k).hi := by decide +kernel
private theorem accepted_54 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox54) tree54 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox54 midpoint_even_54
  simp only [tree54,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox54,candidate_valid h (FixedTape.midBox ibox54),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox54 212 (FixedTape.rowsAux denominator ibox54 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox54) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_54
private noncomputable def tree53 : TapeTree := .face 1 false (candidateRows ibox53) tree54
attribute [irreducible] tree53
private theorem sign_53 : ((computed denominator ibox53).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_53 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox53) tree53 = true := by
  simp only [tree53,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox53,?_,accepted_54 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox53)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox53).gradient 1).hi) denominator_positive).1 sign_53
private noncomputable def tree52 : TapeTree := .centered (candidateRows ibox52) (candidateRows (FixedTape.midBox ibox52))
attribute [irreducible] tree52
private theorem sign_52 : 2*denominator*(computed denominator (FixedTape.midBox ibox52)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox52).gradient k).lo.natAbs ((computed denominator ibox52).gradient k).hi.natAbs : Int)*((ibox52 k).hi-(ibox52 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox52
    (computed denominator ibox52) (computed denominator (FixedTape.midBox ibox52))
    (by decide +kernel)
private theorem midpoint_even_52 : ∀ k, 2 ∣ (ibox52 k).lo+(ibox52 k).hi := by decide +kernel
private theorem accepted_52 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox52) tree52 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox52 midpoint_even_52
  simp only [tree52,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox52,candidate_valid h (FixedTape.midBox ibox52),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox52 212 (FixedTape.rowsAux denominator ibox52 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox52) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_52
private noncomputable def tree51 : TapeTree := .face 1 false (candidateRows ibox51) tree52
attribute [irreducible] tree51
private theorem sign_51 : ((computed denominator ibox51).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_51 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox51) tree51 = true := by
  simp only [tree51,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox51,?_,accepted_52 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox51)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox51).gradient 1).hi) denominator_positive).1 sign_51
private noncomputable def tree50 : TapeTree := .split 0 (((803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree51 tree53
attribute [irreducible] tree50
private theorem accepted_50 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox50) tree50 = true := by
  simp only [tree50,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox50 0 (803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 : Int) false,decode_split denominator ibox50 0 (803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_51 h,accepted_53 h⟩
private noncomputable def tree49 : TapeTree := .centered (candidateRows ibox49) (candidateRows (FixedTape.midBox ibox49))
attribute [irreducible] tree49
private theorem sign_49 : 2*denominator*(computed denominator (FixedTape.midBox ibox49)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox49).gradient k).lo.natAbs ((computed denominator ibox49).gradient k).hi.natAbs : Int)*((ibox49 k).hi-(ibox49 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox49
    (computed denominator ibox49) (computed denominator (FixedTape.midBox ibox49))
    (by decide +kernel)
private theorem midpoint_even_49 : ∀ k, 2 ∣ (ibox49 k).lo+(ibox49 k).hi := by decide +kernel
private theorem accepted_49 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox49) tree49 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox49 midpoint_even_49
  simp only [tree49,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox49,candidate_valid h (FixedTape.midBox ibox49),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox49 212 (FixedTape.rowsAux denominator ibox49 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox49) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_49
private noncomputable def tree48 : TapeTree := .face 1 false (candidateRows ibox48) tree49
attribute [irreducible] tree48
private theorem sign_48 : ((computed denominator ibox48).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_48 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox48) tree48 = true := by
  simp only [tree48,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox48,?_,accepted_49 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox48)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox48).gradient 1).hi) denominator_positive).1 sign_48
private noncomputable def tree47 : TapeTree := .centered (candidateRows ibox47) (candidateRows (FixedTape.midBox ibox47))
attribute [irreducible] tree47
private theorem sign_47 : 2*denominator*(computed denominator (FixedTape.midBox ibox47)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox47).gradient k).lo.natAbs ((computed denominator ibox47).gradient k).hi.natAbs : Int)*((ibox47 k).hi-(ibox47 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox47
    (computed denominator ibox47) (computed denominator (FixedTape.midBox ibox47))
    (by decide +kernel)
private theorem midpoint_even_47 : ∀ k, 2 ∣ (ibox47 k).lo+(ibox47 k).hi := by decide +kernel
private theorem accepted_47 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox47) tree47 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox47 midpoint_even_47
  simp only [tree47,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox47,candidate_valid h (FixedTape.midBox ibox47),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox47 212 (FixedTape.rowsAux denominator ibox47 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox47) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_47
private noncomputable def tree46 : TapeTree := .centered (candidateRows ibox46) (candidateRows (FixedTape.midBox ibox46))
attribute [irreducible] tree46
private theorem sign_46 : 2*denominator*(computed denominator (FixedTape.midBox ibox46)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox46).gradient k).lo.natAbs ((computed denominator ibox46).gradient k).hi.natAbs : Int)*((ibox46 k).hi-(ibox46 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox46
    (computed denominator ibox46) (computed denominator (FixedTape.midBox ibox46))
    (by decide +kernel)
private theorem midpoint_even_46 : ∀ k, 2 ∣ (ibox46 k).lo+(ibox46 k).hi := by decide +kernel
private theorem accepted_46 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox46) tree46 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox46 midpoint_even_46
  simp only [tree46,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox46,candidate_valid h (FixedTape.midBox ibox46),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox46 212 (FixedTape.rowsAux denominator ibox46 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox46) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_46
private noncomputable def tree45 : TapeTree := .split 3 (((35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree46 tree47
attribute [irreducible] tree45
private theorem accepted_45 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox45) tree45 = true := by
  simp only [tree45,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox45 3 (35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) false,decode_split denominator ibox45 3 (35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_46 h,accepted_47 h⟩
private noncomputable def tree44 : TapeTree := .face 1 false (candidateRows ibox44) tree45
attribute [irreducible] tree44
private theorem sign_44 : ((computed denominator ibox44).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_44 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox44) tree44 = true := by
  simp only [tree44,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox44,?_,accepted_45 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox44)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox44).gradient 1).hi) denominator_positive).1 sign_44
private noncomputable def tree43 : TapeTree := .split 0 (((803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree44 tree48
attribute [irreducible] tree43
private theorem accepted_43 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox43) tree43 = true := by
  simp only [tree43,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox43 0 (803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 : Int) false,decode_split denominator ibox43 0 (803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_44 h,accepted_48 h⟩
private noncomputable def tree42 : TapeTree := .centered (candidateRows ibox42) (candidateRows (FixedTape.midBox ibox42))
attribute [irreducible] tree42
private theorem sign_42 : 2*denominator*(computed denominator (FixedTape.midBox ibox42)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox42).gradient k).lo.natAbs ((computed denominator ibox42).gradient k).hi.natAbs : Int)*((ibox42 k).hi-(ibox42 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox42
    (computed denominator ibox42) (computed denominator (FixedTape.midBox ibox42))
    (by decide +kernel)
private theorem midpoint_even_42 : ∀ k, 2 ∣ (ibox42 k).lo+(ibox42 k).hi := by decide +kernel
private theorem accepted_42 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox42) tree42 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox42 midpoint_even_42
  simp only [tree42,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox42,candidate_valid h (FixedTape.midBox ibox42),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox42 212 (FixedTape.rowsAux denominator ibox42 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox42) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_42
private noncomputable def tree41 : TapeTree := .centered (candidateRows ibox41) (candidateRows (FixedTape.midBox ibox41))
attribute [irreducible] tree41
private theorem sign_41 : 2*denominator*(computed denominator (FixedTape.midBox ibox41)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox41).gradient k).lo.natAbs ((computed denominator ibox41).gradient k).hi.natAbs : Int)*((ibox41 k).hi-(ibox41 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox41
    (computed denominator ibox41) (computed denominator (FixedTape.midBox ibox41))
    (by decide +kernel)
private theorem midpoint_even_41 : ∀ k, 2 ∣ (ibox41 k).lo+(ibox41 k).hi := by decide +kernel
private theorem accepted_41 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox41) tree41 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox41 midpoint_even_41
  simp only [tree41,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox41,candidate_valid h (FixedTape.midBox ibox41),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox41 212 (FixedTape.rowsAux denominator ibox41 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox41) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_41
private noncomputable def tree40 : TapeTree := .split 0 (((833668933496537064975057777278366289344455709294592000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree41 tree42
attribute [irreducible] tree40
private theorem accepted_40 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox40) tree40 = true := by
  simp only [tree40,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox40 0 (833668933496537064975057777278366289344455709294592000000000000000000000000000000000000 : Int) false,decode_split denominator ibox40 0 (833668933496537064975057777278366289344455709294592000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_41 h,accepted_42 h⟩
private noncomputable def tree39 : TapeTree := .centered (candidateRows ibox39) (candidateRows (FixedTape.midBox ibox39))
attribute [irreducible] tree39
private theorem sign_39 : 2*denominator*(computed denominator (FixedTape.midBox ibox39)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox39).gradient k).lo.natAbs ((computed denominator ibox39).gradient k).hi.natAbs : Int)*((ibox39 k).hi-(ibox39 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox39
    (computed denominator ibox39) (computed denominator (FixedTape.midBox ibox39))
    (by decide +kernel)
private theorem midpoint_even_39 : ∀ k, 2 ∣ (ibox39 k).lo+(ibox39 k).hi := by decide +kernel
private theorem accepted_39 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox39) tree39 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox39 midpoint_even_39
  simp only [tree39,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox39,candidate_valid h (FixedTape.midBox ibox39),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox39 212 (FixedTape.rowsAux denominator ibox39 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox39) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_39
private noncomputable def tree38 : TapeTree := .centered (candidateRows ibox38) (candidateRows (FixedTape.midBox ibox38))
attribute [irreducible] tree38
private theorem sign_38 : 2*denominator*(computed denominator (FixedTape.midBox ibox38)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox38).gradient k).lo.natAbs ((computed denominator ibox38).gradient k).hi.natAbs : Int)*((ibox38 k).hi-(ibox38 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox38
    (computed denominator ibox38) (computed denominator (FixedTape.midBox ibox38))
    (by decide +kernel)
private theorem midpoint_even_38 : ∀ k, 2 ∣ (ibox38 k).lo+(ibox38 k).hi := by decide +kernel
private theorem accepted_38 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox38) tree38 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox38 midpoint_even_38
  simp only [tree38,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox38,candidate_valid h (FixedTape.midBox ibox38),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox38 212 (FixedTape.rowsAux denominator ibox38 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox38) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_38
private noncomputable def tree37 : TapeTree := .split 0 (((833668933496537064975057777278366289344455709294592000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree38 tree39
attribute [irreducible] tree37
private theorem accepted_37 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox37) tree37 = true := by
  simp only [tree37,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox37 0 (833668933496537064975057777278366289344455709294592000000000000000000000000000000000000 : Int) false,decode_split denominator ibox37 0 (833668933496537064975057777278366289344455709294592000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_38 h,accepted_39 h⟩
private noncomputable def tree36 : TapeTree := .split 3 (((35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree37 tree40
attribute [irreducible] tree36
private theorem accepted_36 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox36) tree36 = true := by
  simp only [tree36,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox36 3 (35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) false,decode_split denominator ibox36 3 (35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_37 h,accepted_40 h⟩
private noncomputable def tree35 : TapeTree := .face 1 false (candidateRows ibox35) tree36
attribute [irreducible] tree35
private theorem sign_35 : ((computed denominator ibox35).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_35 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox35) tree35 = true := by
  simp only [tree35,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox35,?_,accepted_36 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox35)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox35).gradient 1).hi) denominator_positive).1 sign_35
private noncomputable def tree34 : TapeTree := .centered (candidateRows ibox34) (candidateRows (FixedTape.midBox ibox34))
attribute [irreducible] tree34
private theorem sign_34 : 2*denominator*(computed denominator (FixedTape.midBox ibox34)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox34).gradient k).lo.natAbs ((computed denominator ibox34).gradient k).hi.natAbs : Int)*((ibox34 k).hi-(ibox34 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox34
    (computed denominator ibox34) (computed denominator (FixedTape.midBox ibox34))
    (by decide +kernel)
private theorem midpoint_even_34 : ∀ k, 2 ∣ (ibox34 k).lo+(ibox34 k).hi := by decide +kernel
private theorem accepted_34 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox34) tree34 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox34 midpoint_even_34
  simp only [tree34,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox34,candidate_valid h (FixedTape.midBox ibox34),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox34 212 (FixedTape.rowsAux denominator ibox34 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox34) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_34
private noncomputable def tree33 : TapeTree := .centered (candidateRows ibox33) (candidateRows (FixedTape.midBox ibox33))
attribute [irreducible] tree33
private theorem sign_33 : 2*denominator*(computed denominator (FixedTape.midBox ibox33)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox33).gradient k).lo.natAbs ((computed denominator ibox33).gradient k).hi.natAbs : Int)*((ibox33 k).hi-(ibox33 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox33
    (computed denominator ibox33) (computed denominator (FixedTape.midBox ibox33))
    (by decide +kernel)
private theorem midpoint_even_33 : ∀ k, 2 ∣ (ibox33 k).lo+(ibox33 k).hi := by decide +kernel
private theorem accepted_33 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox33) tree33 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox33 midpoint_even_33
  simp only [tree33,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox33,candidate_valid h (FixedTape.midBox ibox33),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox33 212 (FixedTape.rowsAux denominator ibox33 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox33) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_33
private noncomputable def tree32 : TapeTree := .split 0 (((772669354341754540213429812445043682305518305332428800000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree33 tree34
attribute [irreducible] tree32
private theorem accepted_32 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox32) tree32 = true := by
  simp only [tree32,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox32 0 (772669354341754540213429812445043682305518305332428800000000000000000000000000000000000 : Int) false,decode_split denominator ibox32 0 (772669354341754540213429812445043682305518305332428800000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_33 h,accepted_34 h⟩
private noncomputable def tree31 : TapeTree := .centered (candidateRows ibox31) (candidateRows (FixedTape.midBox ibox31))
attribute [irreducible] tree31
private theorem sign_31 : 2*denominator*(computed denominator (FixedTape.midBox ibox31)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox31).gradient k).lo.natAbs ((computed denominator ibox31).gradient k).hi.natAbs : Int)*((ibox31 k).hi-(ibox31 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox31
    (computed denominator ibox31) (computed denominator (FixedTape.midBox ibox31))
    (by decide +kernel)
private theorem midpoint_even_31 : ∀ k, 2 ∣ (ibox31 k).lo+(ibox31 k).hi := by decide +kernel
private theorem accepted_31 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox31) tree31 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox31 midpoint_even_31
  simp only [tree31,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox31,candidate_valid h (FixedTape.midBox ibox31),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox31 212 (FixedTape.rowsAux denominator ibox31 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox31) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_31
private noncomputable def tree30 : TapeTree := .centered (candidateRows ibox30) (candidateRows (FixedTape.midBox ibox30))
attribute [irreducible] tree30
private theorem sign_30 : 2*denominator*(computed denominator (FixedTape.midBox ibox30)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox30).gradient k).lo.natAbs ((computed denominator ibox30).gradient k).hi.natAbs : Int)*((ibox30 k).hi-(ibox30 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox30
    (computed denominator ibox30) (computed denominator (FixedTape.midBox ibox30))
    (by decide +kernel)
private theorem midpoint_even_30 : ∀ k, 2 ∣ (ibox30 k).lo+(ibox30 k).hi := by decide +kernel
private theorem accepted_30 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox30) tree30 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox30 midpoint_even_30
  simp only [tree30,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox30,candidate_valid h (FixedTape.midBox ibox30),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox30 212 (FixedTape.rowsAux denominator ibox30 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox30) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_30
private noncomputable def tree29 : TapeTree := .split 0 (((772669354341754540213429812445043682305518305332428800000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree30 tree31
attribute [irreducible] tree29
private theorem accepted_29 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox29) tree29 = true := by
  simp only [tree29,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox29 0 (772669354341754540213429812445043682305518305332428800000000000000000000000000000000000 : Int) false,decode_split denominator ibox29 0 (772669354341754540213429812445043682305518305332428800000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_30 h,accepted_31 h⟩
private noncomputable def tree28 : TapeTree := .split 3 (((35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree29 tree32
attribute [irreducible] tree28
private theorem accepted_28 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox28) tree28 = true := by
  simp only [tree28,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox28 3 (35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) false,decode_split denominator ibox28 3 (35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_29 h,accepted_32 h⟩
private noncomputable def tree27 : TapeTree := .face 1 false (candidateRows ibox27) tree28
attribute [irreducible] tree27
private theorem sign_27 : ((computed denominator ibox27).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_27 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox27) tree27 = true := by
  simp only [tree27,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox27,?_,accepted_28 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox27)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox27).gradient 1).hi) denominator_positive).1 sign_27
private noncomputable def tree26 : TapeTree := .split 0 (((803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree27 tree35
attribute [irreducible] tree26
private theorem accepted_26 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox26) tree26 = true := by
  simp only [tree26,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox26 0 (803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 : Int) false,decode_split denominator ibox26 0 (803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_27 h,accepted_35 h⟩
private noncomputable def tree25 : TapeTree := .split 1 (((8906034777172359903977615699371622400000000000000000000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree26 tree43
attribute [irreducible] tree25
private theorem accepted_25 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox25) tree25 = true := by
  simp only [tree25,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox25 1 (8906034777172359903977615699371622400000000000000000000000000000000000000000000000000000 : Int) false,decode_split denominator ibox25 1 (8906034777172359903977615699371622400000000000000000000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_26 h,accepted_43 h⟩
private noncomputable def tree24 : TapeTree := .split 1 (((17812069554344719807955231398743244800000000000000000000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree25 tree50
attribute [irreducible] tree24
private theorem accepted_24 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox24) tree24 = true := by
  simp only [tree24,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox24 1 (17812069554344719807955231398743244800000000000000000000000000000000000000000000000000000 : Int) false,decode_split denominator ibox24 1 (17812069554344719807955231398743244800000000000000000000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_25 h,accepted_50 h⟩
private noncomputable def tree23 : TapeTree := .face 2 true (candidateRows ibox23) tree24
attribute [irreducible] tree23
private theorem sign_23 : 0 ≤ ((computed denominator ibox23).gradient 2).lo := by decide +kernel
private theorem accepted_23 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox23) tree23 = true := by
  simp only [tree23,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox23,?_,accepted_24 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox23)).gradient 2).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox23).gradient 2).lo) denominator_positive).2 sign_23
private noncomputable def tree22 : TapeTree := .split 1 (((35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree23 tree55
attribute [irreducible] tree22
private theorem accepted_22 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox22) tree22 = true := by
  simp only [tree22,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox22 1 (35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) false,decode_split denominator ibox22 1 (35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_23 h,accepted_55 h⟩
private noncomputable def tree21 : TapeTree := .centered (candidateRows ibox21) (candidateRows (FixedTape.midBox ibox21))
attribute [irreducible] tree21
private theorem sign_21 : 2*denominator*(computed denominator (FixedTape.midBox ibox21)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox21).gradient k).lo.natAbs ((computed denominator ibox21).gradient k).hi.natAbs : Int)*((ibox21 k).hi-(ibox21 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox21
    (computed denominator ibox21) (computed denominator (FixedTape.midBox ibox21))
    (by decide +kernel)
private theorem midpoint_even_21 : ∀ k, 2 ∣ (ibox21 k).lo+(ibox21 k).hi := by decide +kernel
private theorem accepted_21 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox21) tree21 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox21 midpoint_even_21
  simp only [tree21,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox21,candidate_valid h (FixedTape.midBox ibox21),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox21 212 (FixedTape.rowsAux denominator ibox21 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox21) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_21
private noncomputable def tree20 : TapeTree := .centered (candidateRows ibox20) (candidateRows (FixedTape.midBox ibox20))
attribute [irreducible] tree20
private theorem sign_20 : 2*denominator*(computed denominator (FixedTape.midBox ibox20)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox20).gradient k).lo.natAbs ((computed denominator ibox20).gradient k).hi.natAbs : Int)*((ibox20 k).hi-(ibox20 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox20
    (computed denominator ibox20) (computed denominator (FixedTape.midBox ibox20))
    (by decide +kernel)
private theorem midpoint_even_20 : ∀ k, 2 ∣ (ibox20 k).lo+(ibox20 k).hi := by decide +kernel
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox20 midpoint_even_20
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox20,candidate_valid h (FixedTape.midBox ibox20),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox20 212 (FixedTape.rowsAux denominator ibox20 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox20) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_20
private noncomputable def tree19 : TapeTree := .split 0 (((803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree20 tree21
attribute [irreducible] tree19
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox19 0 (803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 : Int) false,decode_split denominator ibox19 0 (803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_20 h,accepted_21 h⟩
private noncomputable def tree18 : TapeTree := .centered (candidateRows ibox18) (candidateRows (FixedTape.midBox ibox18))
attribute [irreducible] tree18
private theorem sign_18 : 2*denominator*(computed denominator (FixedTape.midBox ibox18)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox18).gradient k).lo.natAbs ((computed denominator ibox18).gradient k).hi.natAbs : Int)*((ibox18 k).hi-(ibox18 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox18
    (computed denominator ibox18) (computed denominator (FixedTape.midBox ibox18))
    (by decide +kernel)
private theorem midpoint_even_18 : ∀ k, 2 ∣ (ibox18 k).lo+(ibox18 k).hi := by decide +kernel
private theorem accepted_18 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox18) tree18 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox18 midpoint_even_18
  simp only [tree18,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox18,candidate_valid h (FixedTape.midBox ibox18),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox18 212 (FixedTape.rowsAux denominator ibox18 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox18) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_18
private noncomputable def tree17 : TapeTree := .face 2 true (candidateRows ibox17) tree18
attribute [irreducible] tree17
private theorem sign_17 : 0 ≤ ((computed denominator ibox17).gradient 2).lo := by decide +kernel
private theorem accepted_17 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox17) tree17 = true := by
  simp only [tree17,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox17,?_,accepted_18 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox17)).gradient 2).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox17).gradient 2).lo) denominator_positive).2 sign_17
private noncomputable def tree16 : TapeTree := .split 1 (((35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree17 tree19
attribute [irreducible] tree16
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox16 1 (35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) false,decode_split denominator ibox16 1 (35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_17 h,accepted_19 h⟩
private noncomputable def tree15 : TapeTree := .face 3 false (candidateRows ibox15) tree16
attribute [irreducible] tree15
private theorem sign_15 : ((computed denominator ibox15).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_15 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox15) tree15 = true := by
  simp only [tree15,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox15,?_,accepted_16 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox15)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox15).gradient 3).hi) denominator_positive).1 sign_15
private noncomputable def tree14 : TapeTree := .split 2 (((53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree15 tree22
attribute [irreducible] tree14
private theorem accepted_14 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox14) tree14 = true := by
  simp only [tree14,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox14 2 (53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 : Int) false,decode_split denominator ibox14 2 (53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_15 h,accepted_22 h⟩
private noncomputable def tree13 : TapeTree := .split 0 (((864168723073928327355871759695027592863924411275673600000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree14 tree63
attribute [irreducible] tree13
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox13 0 (864168723073928327355871759695027592863924411275673600000000000000000000000000000000000 : Int) false,decode_split denominator ibox13 0 (864168723073928327355871759695027592863924411275673600000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_14 h,accepted_63 h⟩
private noncomputable def tree12 : TapeTree := .centered (candidateRows ibox12) (candidateRows (FixedTape.midBox ibox12))
attribute [irreducible] tree12
private theorem sign_12 : 2*denominator*(computed denominator (FixedTape.midBox ibox12)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox12).gradient k).lo.natAbs ((computed denominator ibox12).gradient k).hi.natAbs : Int)*((ibox12 k).hi-(ibox12 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox12
    (computed denominator ibox12) (computed denominator (FixedTape.midBox ibox12))
    (by decide +kernel)
private theorem midpoint_even_12 : ∀ k, 2 ∣ (ibox12 k).lo+(ibox12 k).hi := by decide +kernel
private theorem accepted_12 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox12) tree12 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox12 midpoint_even_12
  simp only [tree12,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox12,candidate_valid h (FixedTape.midBox ibox12),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox12 212 (FixedTape.rowsAux denominator ibox12 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox12) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_12
private noncomputable def tree11 : TapeTree := .face 1 true (candidateRows ibox11) tree12
attribute [irreducible] tree11
private theorem sign_11 : 0 ≤ ((computed denominator ibox11).gradient 1).lo := by decide +kernel
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox11,?_,accepted_12 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox11)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox11).gradient 1).lo) denominator_positive).2 sign_11
private noncomputable def tree10 : TapeTree := .centered (candidateRows ibox10) (candidateRows (FixedTape.midBox ibox10))
attribute [irreducible] tree10
private theorem sign_10 : 2*denominator*(computed denominator (FixedTape.midBox ibox10)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox10).gradient k).lo.natAbs ((computed denominator ibox10).gradient k).hi.natAbs : Int)*((ibox10 k).hi-(ibox10 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox10
    (computed denominator ibox10) (computed denominator (FixedTape.midBox ibox10))
    (by decide +kernel)
private theorem midpoint_even_10 : ∀ k, 2 ∣ (ibox10 k).lo+(ibox10 k).hi := by decide +kernel
private theorem accepted_10 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox10) tree10 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox10 midpoint_even_10
  simp only [tree10,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox10,candidate_valid h (FixedTape.midBox ibox10),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox10 212 (FixedTape.rowsAux denominator ibox10 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox10) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_10
private noncomputable def tree9 : TapeTree := .centered (candidateRows ibox9) (candidateRows (FixedTape.midBox ibox9))
attribute [irreducible] tree9
private theorem sign_9 : 2*denominator*(computed denominator (FixedTape.midBox ibox9)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox9).gradient k).lo.natAbs ((computed denominator ibox9).gradient k).hi.natAbs : Int)*((ibox9 k).hi-(ibox9 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox9
    (computed denominator ibox9) (computed denominator (FixedTape.midBox ibox9))
    (by decide +kernel)
private theorem midpoint_even_9 : ∀ k, 2 ∣ (ibox9 k).lo+(ibox9 k).hi := by decide +kernel
private theorem accepted_9 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox9) tree9 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox9 midpoint_even_9
  simp only [tree9,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox9,candidate_valid h (FixedTape.midBox ibox9),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox9 212 (FixedTape.rowsAux denominator ibox9 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox9) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_9
private noncomputable def tree8 : TapeTree := .split 0 (((803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree9 tree10
attribute [irreducible] tree8
private theorem accepted_8 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox8) tree8 = true := by
  simp only [tree8,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox8 0 (803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 : Int) false,decode_split denominator ibox8 0 (803169143919145802594243794861704985824987007313510400000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_9 h,accepted_10 h⟩
private noncomputable def tree7 : TapeTree := .centered (candidateRows ibox7) (candidateRows (FixedTape.midBox ibox7))
attribute [irreducible] tree7
private theorem sign_7 : 2*denominator*(computed denominator (FixedTape.midBox ibox7)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox7).gradient k).lo.natAbs ((computed denominator ibox7).gradient k).hi.natAbs : Int)*((ibox7 k).hi-(ibox7 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox7
    (computed denominator ibox7) (computed denominator (FixedTape.midBox ibox7))
    (by decide +kernel)
private theorem midpoint_even_7 : ∀ k, 2 ∣ (ibox7 k).lo+(ibox7 k).hi := by decide +kernel
private theorem accepted_7 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox7) tree7 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox7 midpoint_even_7
  simp only [tree7,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox7,candidate_valid h (FixedTape.midBox ibox7),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox7 212 (FixedTape.rowsAux denominator ibox7 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox7) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_7
private noncomputable def tree6 : TapeTree := .split 1 (((53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree7 tree8
attribute [irreducible] tree6
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox6 1 (53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 : Int) false,decode_split denominator ibox6 1 (53436208663034159423865694196229734400000000000000000000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_7 h,accepted_8 h⟩
private noncomputable def tree5 : TapeTree := .centered (candidateRows ibox5) (candidateRows (FixedTape.midBox ibox5))
attribute [irreducible] tree5
private theorem sign_5 : 2*denominator*(computed denominator (FixedTape.midBox ibox5)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox5).gradient k).lo.natAbs ((computed denominator ibox5).gradient k).hi.natAbs : Int)*((ibox5 k).hi-(ibox5 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox5
    (computed denominator ibox5) (computed denominator (FixedTape.midBox ibox5))
    (by decide +kernel)
private theorem midpoint_even_5 : ∀ k, 2 ∣ (ibox5 k).lo+(ibox5 k).hi := by decide +kernel
private theorem accepted_5 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox5) tree5 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox5 midpoint_even_5
  simp only [tree5,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox5,candidate_valid h (FixedTape.midBox ibox5),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox5 212 (FixedTape.rowsAux denominator ibox5 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox5) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_5
private noncomputable def tree4 : TapeTree := .face 2 true (candidateRows ibox4) tree5
attribute [irreducible] tree4
private theorem sign_4 : 0 ≤ ((computed denominator ibox4).gradient 2).lo := by decide +kernel
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox4,?_,accepted_5 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox4)).gradient 2).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox4).gradient 2).lo) denominator_positive).2 sign_4
private noncomputable def tree3 : TapeTree := .split 1 (((35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree6
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 1 (35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) false,decode_split denominator ibox3 1 (35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_6 h⟩
private noncomputable def tree2 : TapeTree := .split 0 (((864168723073928327355871759695027592863924411275673600000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree11
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 0 (864168723073928327355871759695027592863924411275673600000000000000000000000000000000000 : Int) false,decode_split denominator ibox2 0 (864168723073928327355871759695027592863924411275673600000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_3 h,accepted_11 h⟩
private noncomputable def tree1 : TapeTree := .face 3 false (candidateRows ibox1) tree2
attribute [irreducible] tree1
private theorem sign_1 : ((computed denominator ibox1).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_1 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox1) tree1 = true := by
  simp only [tree1,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox1,?_,accepted_2 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox1)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox1).gradient 3).hi) denominator_positive).1 sign_1
private noncomputable def tree0 : TapeTree := .split 2 (((35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree1 tree13
attribute [irreducible] tree0
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox0 2 (35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) false,decode_split denominator ibox0 2 (35624139108689439615910462797486489600000000000000000000000000000000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_1 h,accepted_13 h⟩
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (5208333333333333/500000000000000000 : ℚ) (13841287201/1000000000000 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 212 = e219 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (5208333333333333/500000000000000000 : ℚ) (13841287201/1000000000000 : ℚ)) x → eval e219 x ≤ 0 := by
  have hb := h.child_4 tape 212 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell13_low_internal

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell13_low_internal
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((5208333333333333/500000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((13841287201/1000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 13 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 13 p)
    (hk0 : ((13841287201/1000000000000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((5208333333333333/500000000000000000 : ℚ) : ℝ))
    (hk1 : ((13841287201/1000000000000 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((5208333333333333/500000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r), internalResidual (0 : Fin 9) a p A r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell13_low_internal.cell_bound h.child_8 h.child_9 (Cell13_low_internal.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell13_low_internal
