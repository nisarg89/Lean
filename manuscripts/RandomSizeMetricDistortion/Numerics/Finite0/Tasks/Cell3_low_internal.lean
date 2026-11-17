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
namespace Cell3_low_internal
private noncomputable def qValues : Fin 2 → ℚ := ![(2445636991/1310720000000000 : ℚ),(18604273589/3200000000 : ℚ)]
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
    priceLambda 3 p = ((2445636991/1310720000000000 : ℝ)+(18604273589/3200000000 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell3,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 3 p = (((145513/100000 : ℝ)+(145513/25000 : ℝ)*p)-(145513/100000 : ℝ)*(1/1 : ℝ))/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell3,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e219 x = (x 0*(1-x 0))*(aPoint x+priceLambda 3 (x 0)*(HStar (yPoint x)-HStar (aPoint x)-HStar (capPoint x))+priceTau 3 (x 0)*psiStar (rPoint x)+(0)-(0)) := by
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
    (hL : lambdaStar (x 0) = priceLambda 3 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 3 (x 0)) :
    (1)*eval e219 x = (x 0*(1-x 0))*(internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,if_pos hA,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (49/102400 : ℚ) (343/512000 : ℚ)) x → eval e219 x ≤ 0)
    (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((49/102400 : ℚ) : ℝ) < p ∧ p ≤ ((343/512000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 3 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 3 p)
    (hk0 : ((343/512000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((49/102400 : ℚ) : ℝ))
    (hk1 : ((343/512000 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((49/102400 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r) :
    internalResidual (0 : Fin 9) a p A r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxA,hxr⟩ := h3 (49/102400 : ℚ) (343/512000 : ℚ) ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ) p a A r hpcell hk0 hk1 hr ha hap hpA hAr
  have hcut : ((343/512000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) := by norm_num [bStar]
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxa
  have hAx : capPoint x = A := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxA
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 3 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 3 (x 0) := by simpa only [hxp] using hT
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
.const (2445636991/1310720000000000 : ℚ),
.const (18604273589/3200000000 : ℚ),
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
private noncomputable def ssaQVals : Fin 16 → ℚ := ![(1/1 : ℚ),(49/100 : ℚ),(390189/5000000 : ℚ),(1085/4818 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(4818/3733 : ℚ),(2445636991/1310720000000000 : ℚ),(18604273589/3200000000 : ℚ),(145513/100000 : ℚ),(145513/25000 : ℚ),(-145513/100000 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ)]
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
private noncomputable def denominator : Int := 15300451241997573257090223897942914383384412160000000000000
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
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨7321504988846495015599814169914089890486681600000000000,10250106984385093021839739837879725846681354240000000000⟩,⟨0,15300451241997573257090223897942914383384412160000000000000⟩,⟨0,15300451241997573257090223897942914383384412160000000000000⟩,⟨0,15300451241997573257090223897942914383384412160000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := splitI ibox0 2 7650225620998786628545111948971457191692206080000000000000 false
private noncomputable def ibox2 : Fin 4 → FixedTape.I := faceI ibox1 3 false
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 0 8785805986615794018719777003896907868584017920000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 1 7650225620998786628545111948971457191692206080000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := faceI ibox4 2 true
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox3 1 7650225620998786628545111948971457191692206080000000000000 true
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox6 0 8053655487731144517159795586905498879535349760000000000 false
private noncomputable def ibox8 : Fin 4 → FixedTape.I := faceI ibox7 1 true
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox6 0 8053655487731144517159795586905498879535349760000000000 true
private noncomputable def ibox10 : Fin 4 → FixedTape.I := faceI ibox9 1 true
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox2 0 8785805986615794018719777003896907868584017920000000000 true
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox11 1 7650225620998786628545111948971457191692206080000000000000 false
private noncomputable def ibox13 : Fin 4 → FixedTape.I := faceI ibox12 2 true
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox11 1 7650225620998786628545111948971457191692206080000000000000 true
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox14 1 11475338431498179942817667923457185787538309120000000000000 false
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox14 1 11475338431498179942817667923457185787538309120000000000000 true
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox16 0 9517956485500443520279758420888316857632686080000000000 false
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox16 0 9517956485500443520279758420888316857632686080000000000 true
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox0 2 7650225620998786628545111948971457191692206080000000000000 true
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox19 0 8785805986615794018719777003896907868584017920000000000 false
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox20 2 11475338431498179942817667923457185787538309120000000000000 false
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox21 0 8053655487731144517159795586905498879535349760000000000 false
private noncomputable def ibox23 : Fin 4 → FixedTape.I := faceI ibox22 3 false
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox23 1 7650225620998786628545111948971457191692206080000000000000 false
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox23 1 7650225620998786628545111948971457191692206080000000000000 true
private noncomputable def ibox26 : Fin 4 → FixedTape.I := splitI ibox21 0 8053655487731144517159795586905498879535349760000000000 true
private noncomputable def ibox27 : Fin 4 → FixedTape.I := faceI ibox26 3 false
private noncomputable def ibox28 : Fin 4 → FixedTape.I := splitI ibox27 1 7650225620998786628545111948971457191692206080000000000000 false
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox27 1 7650225620998786628545111948971457191692206080000000000000 true
private noncomputable def ibox30 : Fin 4 → FixedTape.I := splitI ibox20 2 11475338431498179942817667923457185787538309120000000000000 true
private noncomputable def ibox31 : Fin 4 → FixedTape.I := splitI ibox30 1 7650225620998786628545111948971457191692206080000000000000 false
private noncomputable def ibox32 : Fin 4 → FixedTape.I := faceI ibox31 2 true
private noncomputable def ibox33 : Fin 4 → FixedTape.I := splitI ibox32 1 3825112810499393314272555974485728595846103040000000000000 false
private noncomputable def ibox34 : Fin 4 → FixedTape.I := splitI ibox33 1 1912556405249696657136277987242864297923051520000000000000 false
private noncomputable def ibox35 : Fin 4 → FixedTape.I := splitI ibox34 0 8053655487731144517159795586905498879535349760000000000 false
private noncomputable def ibox36 : Fin 4 → FixedTape.I := faceI ibox35 1 false
private noncomputable def ibox37 : Fin 4 → FixedTape.I := splitI ibox36 3 7650225620998786628545111948971457191692206080000000000000 false
private noncomputable def ibox38 : Fin 4 → FixedTape.I := splitI ibox37 3 3825112810499393314272555974485728595846103040000000000000 false
private noncomputable def ibox39 : Fin 4 → FixedTape.I := splitI ibox38 0 7687580238288819766379804878409794385011015680000000000 false
private noncomputable def ibox40 : Fin 4 → FixedTape.I := splitI ibox39 0 7504542613567657390989809524161942137748848640000000000 false
private noncomputable def ibox41 : Fin 4 → FixedTape.I := splitI ibox40 3 1912556405249696657136277987242864297923051520000000000000 false
private noncomputable def ibox42 : Fin 4 → FixedTape.I := splitI ibox41 0 7413023801207076203294811847038016014117765120000000000 false
private noncomputable def ibox43 : Fin 4 → FixedTape.I := splitI ibox42 3 956278202624848328568138993621432148961525760000000000000 false
private noncomputable def ibox44 : Fin 4 → FixedTape.I := splitI ibox42 3 956278202624848328568138993621432148961525760000000000000 true
private noncomputable def ibox45 : Fin 4 → FixedTape.I := splitI ibox41 0 7413023801207076203294811847038016014117765120000000000 true
private noncomputable def ibox46 : Fin 4 → FixedTape.I := splitI ibox45 3 956278202624848328568138993621432148961525760000000000000 false
private noncomputable def ibox47 : Fin 4 → FixedTape.I := splitI ibox45 3 956278202624848328568138993621432148961525760000000000000 true
private noncomputable def ibox48 : Fin 4 → FixedTape.I := splitI ibox40 3 1912556405249696657136277987242864297923051520000000000000 true
private noncomputable def ibox49 : Fin 4 → FixedTape.I := splitI ibox48 0 7413023801207076203294811847038016014117765120000000000 false
private noncomputable def ibox50 : Fin 4 → FixedTape.I := splitI ibox49 3 2868834607874544985704416980864296446884577280000000000000 false
private noncomputable def ibox51 : Fin 4 → FixedTape.I := splitI ibox49 3 2868834607874544985704416980864296446884577280000000000000 true
private noncomputable def ibox52 : Fin 4 → FixedTape.I := splitI ibox48 0 7413023801207076203294811847038016014117765120000000000 true
private noncomputable def ibox53 : Fin 4 → FixedTape.I := splitI ibox52 3 2868834607874544985704416980864296446884577280000000000000 false
private noncomputable def ibox54 : Fin 4 → FixedTape.I := splitI ibox52 3 2868834607874544985704416980864296446884577280000000000000 true
private noncomputable def ibox55 : Fin 4 → FixedTape.I := splitI ibox39 0 7504542613567657390989809524161942137748848640000000000 true
private noncomputable def ibox56 : Fin 4 → FixedTape.I := splitI ibox55 3 1912556405249696657136277987242864297923051520000000000000 false
private noncomputable def ibox57 : Fin 4 → FixedTape.I := splitI ibox56 0 7596061425928238578684807201285868261379932160000000000 false
private noncomputable def ibox58 : Fin 4 → FixedTape.I := splitI ibox57 3 956278202624848328568138993621432148961525760000000000000 false
private noncomputable def ibox59 : Fin 4 → FixedTape.I := splitI ibox57 3 956278202624848328568138993621432148961525760000000000000 true
private noncomputable def ibox60 : Fin 4 → FixedTape.I := splitI ibox56 0 7596061425928238578684807201285868261379932160000000000 true
private noncomputable def ibox61 : Fin 4 → FixedTape.I := splitI ibox60 3 956278202624848328568138993621432148961525760000000000000 false
private noncomputable def ibox62 : Fin 4 → FixedTape.I := splitI ibox60 3 956278202624848328568138993621432148961525760000000000000 true
private noncomputable def ibox63 : Fin 4 → FixedTape.I := splitI ibox55 3 1912556405249696657136277987242864297923051520000000000000 true
private noncomputable def ibox64 : Fin 4 → FixedTape.I := splitI ibox63 0 7596061425928238578684807201285868261379932160000000000 false
private noncomputable def ibox65 : Fin 4 → FixedTape.I := splitI ibox64 3 2868834607874544985704416980864296446884577280000000000000 false
private noncomputable def ibox66 : Fin 4 → FixedTape.I := splitI ibox64 3 2868834607874544985704416980864296446884577280000000000000 true
private noncomputable def ibox67 : Fin 4 → FixedTape.I := splitI ibox63 0 7596061425928238578684807201285868261379932160000000000 true
private noncomputable def ibox68 : Fin 4 → FixedTape.I := splitI ibox67 3 2868834607874544985704416980864296446884577280000000000000 false
private noncomputable def ibox69 : Fin 4 → FixedTape.I := splitI ibox67 3 2868834607874544985704416980864296446884577280000000000000 true
private noncomputable def ibox70 : Fin 4 → FixedTape.I := splitI ibox38 0 7687580238288819766379804878409794385011015680000000000 true
private noncomputable def ibox71 : Fin 4 → FixedTape.I := splitI ibox70 3 1912556405249696657136277987242864297923051520000000000000 false
private noncomputable def ibox72 : Fin 4 → FixedTape.I := splitI ibox71 0 7870617863009982141769800232657646632273182720000000000 false
private noncomputable def ibox73 : Fin 4 → FixedTape.I := splitI ibox72 0 7779099050649400954074802555533720508642099200000000000 false
private noncomputable def ibox74 : Fin 4 → FixedTape.I := splitI ibox73 3 956278202624848328568138993621432148961525760000000000000 false
private noncomputable def ibox75 : Fin 4 → FixedTape.I := splitI ibox73 3 956278202624848328568138993621432148961525760000000000000 true
private noncomputable def ibox76 : Fin 4 → FixedTape.I := splitI ibox72 0 7779099050649400954074802555533720508642099200000000000 true
private noncomputable def ibox77 : Fin 4 → FixedTape.I := splitI ibox76 3 956278202624848328568138993621432148961525760000000000000 false
private noncomputable def ibox78 : Fin 4 → FixedTape.I := splitI ibox76 3 956278202624848328568138993621432148961525760000000000000 true
private noncomputable def ibox79 : Fin 4 → FixedTape.I := splitI ibox71 0 7870617863009982141769800232657646632273182720000000000 true
private noncomputable def ibox80 : Fin 4 → FixedTape.I := splitI ibox79 0 7962136675370563329464797909781572755904266240000000000 false
private noncomputable def ibox81 : Fin 4 → FixedTape.I := splitI ibox80 3 956278202624848328568138993621432148961525760000000000000 false
private noncomputable def ibox82 : Fin 4 → FixedTape.I := splitI ibox80 3 956278202624848328568138993621432148961525760000000000000 true
private noncomputable def ibox83 : Fin 4 → FixedTape.I := splitI ibox79 0 7962136675370563329464797909781572755904266240000000000 true
private noncomputable def ibox84 : Fin 4 → FixedTape.I := splitI ibox83 3 956278202624848328568138993621432148961525760000000000000 false
private noncomputable def ibox85 : Fin 4 → FixedTape.I := splitI ibox83 3 956278202624848328568138993621432148961525760000000000000 true
private noncomputable def ibox86 : Fin 4 → FixedTape.I := splitI ibox70 3 1912556405249696657136277987242864297923051520000000000000 true
private noncomputable def ibox87 : Fin 4 → FixedTape.I := splitI ibox86 0 7870617863009982141769800232657646632273182720000000000 false
private noncomputable def ibox88 : Fin 4 → FixedTape.I := splitI ibox87 3 2868834607874544985704416980864296446884577280000000000000 false
private noncomputable def ibox89 : Fin 4 → FixedTape.I := splitI ibox88 0 7779099050649400954074802555533720508642099200000000000 false
private noncomputable def ibox90 : Fin 4 → FixedTape.I := splitI ibox88 0 7779099050649400954074802555533720508642099200000000000 true
private noncomputable def ibox91 : Fin 4 → FixedTape.I := splitI ibox87 3 2868834607874544985704416980864296446884577280000000000000 true
private noncomputable def ibox92 : Fin 4 → FixedTape.I := splitI ibox91 0 7779099050649400954074802555533720508642099200000000000 false
private noncomputable def ibox93 : Fin 4 → FixedTape.I := splitI ibox91 0 7779099050649400954074802555533720508642099200000000000 true
private noncomputable def ibox94 : Fin 4 → FixedTape.I := splitI ibox86 0 7870617863009982141769800232657646632273182720000000000 true
private noncomputable def ibox95 : Fin 4 → FixedTape.I := splitI ibox94 3 2868834607874544985704416980864296446884577280000000000000 false
private noncomputable def ibox96 : Fin 4 → FixedTape.I := splitI ibox95 0 7962136675370563329464797909781572755904266240000000000 false
private noncomputable def ibox97 : Fin 4 → FixedTape.I := splitI ibox95 0 7962136675370563329464797909781572755904266240000000000 true
private noncomputable def ibox98 : Fin 4 → FixedTape.I := splitI ibox94 3 2868834607874544985704416980864296446884577280000000000000 true
private noncomputable def ibox99 : Fin 4 → FixedTape.I := splitI ibox98 0 7962136675370563329464797909781572755904266240000000000 false
private noncomputable def ibox100 : Fin 4 → FixedTape.I := splitI ibox98 0 7962136675370563329464797909781572755904266240000000000 true
private noncomputable def ibox101 : Fin 4 → FixedTape.I := splitI ibox37 3 3825112810499393314272555974485728595846103040000000000000 true
private noncomputable def ibox102 : Fin 4 → FixedTape.I := splitI ibox101 0 7687580238288819766379804878409794385011015680000000000 false
private noncomputable def ibox103 : Fin 4 → FixedTape.I := splitI ibox102 3 5737669215749089971408833961728592893769154560000000000000 false
private noncomputable def ibox104 : Fin 4 → FixedTape.I := splitI ibox103 0 7504542613567657390989809524161942137748848640000000000 false
private noncomputable def ibox105 : Fin 4 → FixedTape.I := splitI ibox104 3 4781391013124241642840694968107160744807628800000000000000 false
private noncomputable def ibox106 : Fin 4 → FixedTape.I := splitI ibox105 0 7413023801207076203294811847038016014117765120000000000 false
private noncomputable def ibox107 : Fin 4 → FixedTape.I := splitI ibox105 0 7413023801207076203294811847038016014117765120000000000 true
private noncomputable def ibox108 : Fin 4 → FixedTape.I := splitI ibox104 3 4781391013124241642840694968107160744807628800000000000000 true
private noncomputable def ibox109 : Fin 4 → FixedTape.I := splitI ibox108 0 7413023801207076203294811847038016014117765120000000000 false
private noncomputable def ibox110 : Fin 4 → FixedTape.I := splitI ibox108 0 7413023801207076203294811847038016014117765120000000000 true
private noncomputable def ibox111 : Fin 4 → FixedTape.I := splitI ibox103 0 7504542613567657390989809524161942137748848640000000000 true
private noncomputable def ibox112 : Fin 4 → FixedTape.I := splitI ibox111 3 4781391013124241642840694968107160744807628800000000000000 false
private noncomputable def ibox113 : Fin 4 → FixedTape.I := splitI ibox112 0 7596061425928238578684807201285868261379932160000000000 false
private noncomputable def ibox114 : Fin 4 → FixedTape.I := splitI ibox112 0 7596061425928238578684807201285868261379932160000000000 true
private noncomputable def ibox115 : Fin 4 → FixedTape.I := splitI ibox111 3 4781391013124241642840694968107160744807628800000000000000 true
private noncomputable def ibox116 : Fin 4 → FixedTape.I := splitI ibox115 0 7596061425928238578684807201285868261379932160000000000 false
private noncomputable def ibox117 : Fin 4 → FixedTape.I := splitI ibox115 0 7596061425928238578684807201285868261379932160000000000 true
private noncomputable def ibox118 : Fin 4 → FixedTape.I := splitI ibox102 3 5737669215749089971408833961728592893769154560000000000000 true
private noncomputable def ibox119 : Fin 4 → FixedTape.I := splitI ibox118 0 7504542613567657390989809524161942137748848640000000000 false
private noncomputable def ibox120 : Fin 4 → FixedTape.I := splitI ibox119 3 6693947418373938299976972955350025042730680320000000000000 false
private noncomputable def ibox121 : Fin 4 → FixedTape.I := splitI ibox120 0 7413023801207076203294811847038016014117765120000000000 false
private noncomputable def ibox122 : Fin 4 → FixedTape.I := splitI ibox120 0 7413023801207076203294811847038016014117765120000000000 true
private noncomputable def ibox123 : Fin 4 → FixedTape.I := splitI ibox119 3 6693947418373938299976972955350025042730680320000000000000 true
private noncomputable def ibox124 : Fin 4 → FixedTape.I := splitI ibox123 0 7413023801207076203294811847038016014117765120000000000 false
private noncomputable def ibox125 : Fin 4 → FixedTape.I := splitI ibox123 0 7413023801207076203294811847038016014117765120000000000 true
private noncomputable def ibox126 : Fin 4 → FixedTape.I := splitI ibox118 0 7504542613567657390989809524161942137748848640000000000 true
private noncomputable def ibox127 : Fin 4 → FixedTape.I := splitI ibox126 3 6693947418373938299976972955350025042730680320000000000000 false
private noncomputable def ibox128 : Fin 4 → FixedTape.I := splitI ibox127 0 7596061425928238578684807201285868261379932160000000000 false
private noncomputable def ibox129 : Fin 4 → FixedTape.I := splitI ibox127 0 7596061425928238578684807201285868261379932160000000000 true
private noncomputable def ibox130 : Fin 4 → FixedTape.I := splitI ibox126 3 6693947418373938299976972955350025042730680320000000000000 true
private noncomputable def ibox131 : Fin 4 → FixedTape.I := splitI ibox130 0 7596061425928238578684807201285868261379932160000000000 false
private noncomputable def ibox132 : Fin 4 → FixedTape.I := splitI ibox130 0 7596061425928238578684807201285868261379932160000000000 true
private noncomputable def ibox133 : Fin 4 → FixedTape.I := splitI ibox101 0 7687580238288819766379804878409794385011015680000000000 true
private noncomputable def ibox134 : Fin 4 → FixedTape.I := splitI ibox133 3 5737669215749089971408833961728592893769154560000000000000 false
private noncomputable def ibox135 : Fin 4 → FixedTape.I := splitI ibox134 0 7870617863009982141769800232657646632273182720000000000 false
private noncomputable def ibox136 : Fin 4 → FixedTape.I := splitI ibox135 3 4781391013124241642840694968107160744807628800000000000000 false
private noncomputable def ibox137 : Fin 4 → FixedTape.I := splitI ibox136 0 7779099050649400954074802555533720508642099200000000000 false
private noncomputable def ibox138 : Fin 4 → FixedTape.I := splitI ibox136 0 7779099050649400954074802555533720508642099200000000000 true
private noncomputable def ibox139 : Fin 4 → FixedTape.I := splitI ibox135 3 4781391013124241642840694968107160744807628800000000000000 true
private noncomputable def ibox140 : Fin 4 → FixedTape.I := splitI ibox139 0 7779099050649400954074802555533720508642099200000000000 false
private noncomputable def ibox141 : Fin 4 → FixedTape.I := splitI ibox139 0 7779099050649400954074802555533720508642099200000000000 true
private noncomputable def ibox142 : Fin 4 → FixedTape.I := splitI ibox134 0 7870617863009982141769800232657646632273182720000000000 true
private noncomputable def ibox143 : Fin 4 → FixedTape.I := splitI ibox142 3 4781391013124241642840694968107160744807628800000000000000 false
private noncomputable def ibox144 : Fin 4 → FixedTape.I := splitI ibox143 0 7962136675370563329464797909781572755904266240000000000 false
private noncomputable def ibox145 : Fin 4 → FixedTape.I := splitI ibox143 0 7962136675370563329464797909781572755904266240000000000 true
private noncomputable def ibox146 : Fin 4 → FixedTape.I := splitI ibox142 3 4781391013124241642840694968107160744807628800000000000000 true
private noncomputable def ibox147 : Fin 4 → FixedTape.I := splitI ibox146 0 7962136675370563329464797909781572755904266240000000000 false
private noncomputable def ibox148 : Fin 4 → FixedTape.I := splitI ibox146 0 7962136675370563329464797909781572755904266240000000000 true
private noncomputable def ibox149 : Fin 4 → FixedTape.I := splitI ibox133 3 5737669215749089971408833961728592893769154560000000000000 true
private noncomputable def ibox150 : Fin 4 → FixedTape.I := splitI ibox149 0 7870617863009982141769800232657646632273182720000000000 false
private noncomputable def ibox151 : Fin 4 → FixedTape.I := splitI ibox150 3 6693947418373938299976972955350025042730680320000000000000 false
private noncomputable def ibox152 : Fin 4 → FixedTape.I := splitI ibox151 0 7779099050649400954074802555533720508642099200000000000 false
private noncomputable def ibox153 : Fin 4 → FixedTape.I := splitI ibox151 0 7779099050649400954074802555533720508642099200000000000 true
private noncomputable def ibox154 : Fin 4 → FixedTape.I := splitI ibox150 3 6693947418373938299976972955350025042730680320000000000000 true
private noncomputable def ibox155 : Fin 4 → FixedTape.I := splitI ibox154 0 7779099050649400954074802555533720508642099200000000000 false
private noncomputable def ibox156 : Fin 4 → FixedTape.I := splitI ibox154 0 7779099050649400954074802555533720508642099200000000000 true
private noncomputable def ibox157 : Fin 4 → FixedTape.I := splitI ibox149 0 7870617863009982141769800232657646632273182720000000000 true
private noncomputable def ibox158 : Fin 4 → FixedTape.I := splitI ibox157 3 6693947418373938299976972955350025042730680320000000000000 false
private noncomputable def ibox159 : Fin 4 → FixedTape.I := splitI ibox158 0 7962136675370563329464797909781572755904266240000000000 false
private noncomputable def ibox160 : Fin 4 → FixedTape.I := splitI ibox158 0 7962136675370563329464797909781572755904266240000000000 true
private noncomputable def ibox161 : Fin 4 → FixedTape.I := splitI ibox157 3 6693947418373938299976972955350025042730680320000000000000 true
private noncomputable def ibox162 : Fin 4 → FixedTape.I := splitI ibox161 0 7962136675370563329464797909781572755904266240000000000 false
private noncomputable def ibox163 : Fin 4 → FixedTape.I := splitI ibox161 0 7962136675370563329464797909781572755904266240000000000 true
private noncomputable def ibox164 : Fin 4 → FixedTape.I := splitI ibox36 3 7650225620998786628545111948971457191692206080000000000000 true
private noncomputable def ibox165 : Fin 4 → FixedTape.I := splitI ibox164 3 11475338431498179942817667923457185787538309120000000000000 false
private noncomputable def ibox166 : Fin 4 → FixedTape.I := splitI ibox165 0 7687580238288819766379804878409794385011015680000000000 false
private noncomputable def ibox167 : Fin 4 → FixedTape.I := splitI ibox166 3 9562782026248483285681389936214321489615257600000000000000 false
private noncomputable def ibox168 : Fin 4 → FixedTape.I := splitI ibox167 0 7504542613567657390989809524161942137748848640000000000 false
private noncomputable def ibox169 : Fin 4 → FixedTape.I := splitI ibox168 3 8606503823623634957113250942592889340653731840000000000000 false
private noncomputable def ibox170 : Fin 4 → FixedTape.I := splitI ibox169 0 7413023801207076203294811847038016014117765120000000000 false
private noncomputable def ibox171 : Fin 4 → FixedTape.I := splitI ibox169 0 7413023801207076203294811847038016014117765120000000000 true
private noncomputable def ibox172 : Fin 4 → FixedTape.I := splitI ibox168 3 8606503823623634957113250942592889340653731840000000000000 true
private noncomputable def ibox173 : Fin 4 → FixedTape.I := splitI ibox172 0 7413023801207076203294811847038016014117765120000000000 false
private noncomputable def ibox174 : Fin 4 → FixedTape.I := splitI ibox172 0 7413023801207076203294811847038016014117765120000000000 true
private noncomputable def ibox175 : Fin 4 → FixedTape.I := splitI ibox167 0 7504542613567657390989809524161942137748848640000000000 true
private noncomputable def ibox176 : Fin 4 → FixedTape.I := splitI ibox175 3 8606503823623634957113250942592889340653731840000000000000 false
private noncomputable def ibox177 : Fin 4 → FixedTape.I := splitI ibox176 0 7596061425928238578684807201285868261379932160000000000 false
private noncomputable def ibox178 : Fin 4 → FixedTape.I := splitI ibox176 0 7596061425928238578684807201285868261379932160000000000 true
private noncomputable def ibox179 : Fin 4 → FixedTape.I := splitI ibox175 3 8606503823623634957113250942592889340653731840000000000000 true
private noncomputable def ibox180 : Fin 4 → FixedTape.I := splitI ibox179 0 7596061425928238578684807201285868261379932160000000000 false
private noncomputable def ibox181 : Fin 4 → FixedTape.I := splitI ibox179 0 7596061425928238578684807201285868261379932160000000000 true
private noncomputable def ibox182 : Fin 4 → FixedTape.I := splitI ibox166 3 9562782026248483285681389936214321489615257600000000000000 true
private noncomputable def ibox183 : Fin 4 → FixedTape.I := splitI ibox182 0 7504542613567657390989809524161942137748848640000000000 false
private noncomputable def ibox184 : Fin 4 → FixedTape.I := splitI ibox183 3 10519060228873331614249528929835753638576783360000000000000 false
private noncomputable def ibox185 : Fin 4 → FixedTape.I := splitI ibox184 0 7413023801207076203294811847038016014117765120000000000 false
private noncomputable def ibox186 : Fin 4 → FixedTape.I := splitI ibox184 0 7413023801207076203294811847038016014117765120000000000 true
private noncomputable def ibox187 : Fin 4 → FixedTape.I := splitI ibox183 3 10519060228873331614249528929835753638576783360000000000000 true
private noncomputable def ibox188 : Fin 4 → FixedTape.I := splitI ibox187 0 7413023801207076203294811847038016014117765120000000000 false
private noncomputable def ibox189 : Fin 4 → FixedTape.I := splitI ibox187 0 7413023801207076203294811847038016014117765120000000000 true
private noncomputable def ibox190 : Fin 4 → FixedTape.I := splitI ibox182 0 7504542613567657390989809524161942137748848640000000000 true
private noncomputable def ibox191 : Fin 4 → FixedTape.I := splitI ibox190 3 10519060228873331614249528929835753638576783360000000000000 false
private noncomputable def ibox192 : Fin 4 → FixedTape.I := splitI ibox191 0 7596061425928238578684807201285868261379932160000000000 false
private noncomputable def ibox193 : Fin 4 → FixedTape.I := splitI ibox191 0 7596061425928238578684807201285868261379932160000000000 true
private noncomputable def ibox194 : Fin 4 → FixedTape.I := splitI ibox190 3 10519060228873331614249528929835753638576783360000000000000 true
private noncomputable def ibox195 : Fin 4 → FixedTape.I := splitI ibox194 0 7596061425928238578684807201285868261379932160000000000 false
private noncomputable def ibox196 : Fin 4 → FixedTape.I := splitI ibox194 0 7596061425928238578684807201285868261379932160000000000 true
private noncomputable def ibox197 : Fin 4 → FixedTape.I := splitI ibox165 0 7687580238288819766379804878409794385011015680000000000 true
private noncomputable def ibox198 : Fin 4 → FixedTape.I := splitI ibox197 3 9562782026248483285681389936214321489615257600000000000000 false
private noncomputable def ibox199 : Fin 4 → FixedTape.I := splitI ibox198 0 7870617863009982141769800232657646632273182720000000000 false
private noncomputable def ibox200 : Fin 4 → FixedTape.I := splitI ibox199 3 8606503823623634957113250942592889340653731840000000000000 false
private noncomputable def ibox201 : Fin 4 → FixedTape.I := splitI ibox200 0 7779099050649400954074802555533720508642099200000000000 false
private noncomputable def ibox202 : Fin 4 → FixedTape.I := splitI ibox200 0 7779099050649400954074802555533720508642099200000000000 true
private noncomputable def ibox203 : Fin 4 → FixedTape.I := splitI ibox199 3 8606503823623634957113250942592889340653731840000000000000 true
private noncomputable def ibox204 : Fin 4 → FixedTape.I := splitI ibox203 0 7779099050649400954074802555533720508642099200000000000 false
private noncomputable def ibox205 : Fin 4 → FixedTape.I := splitI ibox203 0 7779099050649400954074802555533720508642099200000000000 true
private noncomputable def ibox206 : Fin 4 → FixedTape.I := splitI ibox198 0 7870617863009982141769800232657646632273182720000000000 true
private noncomputable def ibox207 : Fin 4 → FixedTape.I := splitI ibox206 3 8606503823623634957113250942592889340653731840000000000000 false
private noncomputable def ibox208 : Fin 4 → FixedTape.I := splitI ibox207 0 7962136675370563329464797909781572755904266240000000000 false
private noncomputable def ibox209 : Fin 4 → FixedTape.I := splitI ibox207 0 7962136675370563329464797909781572755904266240000000000 true
private noncomputable def ibox210 : Fin 4 → FixedTape.I := splitI ibox206 3 8606503823623634957113250942592889340653731840000000000000 true
private noncomputable def ibox211 : Fin 4 → FixedTape.I := splitI ibox210 0 7962136675370563329464797909781572755904266240000000000 false
private noncomputable def ibox212 : Fin 4 → FixedTape.I := splitI ibox210 0 7962136675370563329464797909781572755904266240000000000 true
private noncomputable def ibox213 : Fin 4 → FixedTape.I := splitI ibox197 3 9562782026248483285681389936214321489615257600000000000000 true
private noncomputable def ibox214 : Fin 4 → FixedTape.I := splitI ibox213 0 7870617863009982141769800232657646632273182720000000000 false
private noncomputable def ibox215 : Fin 4 → FixedTape.I := splitI ibox214 3 10519060228873331614249528929835753638576783360000000000000 false
private noncomputable def ibox216 : Fin 4 → FixedTape.I := splitI ibox215 0 7779099050649400954074802555533720508642099200000000000 false
private noncomputable def ibox217 : Fin 4 → FixedTape.I := splitI ibox215 0 7779099050649400954074802555533720508642099200000000000 true
private noncomputable def ibox218 : Fin 4 → FixedTape.I := splitI ibox214 3 10519060228873331614249528929835753638576783360000000000000 true
private noncomputable def ibox219 : Fin 4 → FixedTape.I := splitI ibox218 0 7779099050649400954074802555533720508642099200000000000 false
private noncomputable def ibox220 : Fin 4 → FixedTape.I := splitI ibox218 0 7779099050649400954074802555533720508642099200000000000 true
private noncomputable def ibox221 : Fin 4 → FixedTape.I := splitI ibox213 0 7870617863009982141769800232657646632273182720000000000 true
private noncomputable def ibox222 : Fin 4 → FixedTape.I := splitI ibox221 3 10519060228873331614249528929835753638576783360000000000000 false
private noncomputable def ibox223 : Fin 4 → FixedTape.I := splitI ibox221 3 10519060228873331614249528929835753638576783360000000000000 true
private noncomputable def ibox224 : Fin 4 → FixedTape.I := splitI ibox164 3 11475338431498179942817667923457185787538309120000000000000 true
private noncomputable def ibox225 : Fin 4 → FixedTape.I := splitI ibox224 3 13387894836747876599953945910700050085461360640000000000000 false
private noncomputable def ibox226 : Fin 4 → FixedTape.I := splitI ibox225 0 7687580238288819766379804878409794385011015680000000000 false
private noncomputable def ibox227 : Fin 4 → FixedTape.I := splitI ibox226 0 7504542613567657390989809524161942137748848640000000000 false
private noncomputable def ibox228 : Fin 4 → FixedTape.I := splitI ibox227 3 12431616634123028271385806917078617936499834880000000000000 false
private noncomputable def ibox229 : Fin 4 → FixedTape.I := splitI ibox228 0 7413023801207076203294811847038016014117765120000000000 false
private noncomputable def ibox230 : Fin 4 → FixedTape.I := splitI ibox228 0 7413023801207076203294811847038016014117765120000000000 true
private noncomputable def ibox231 : Fin 4 → FixedTape.I := splitI ibox227 3 12431616634123028271385806917078617936499834880000000000000 true
private noncomputable def ibox232 : Fin 4 → FixedTape.I := splitI ibox231 0 7413023801207076203294811847038016014117765120000000000 false
private noncomputable def ibox233 : Fin 4 → FixedTape.I := splitI ibox231 0 7413023801207076203294811847038016014117765120000000000 true
private noncomputable def ibox234 : Fin 4 → FixedTape.I := splitI ibox226 0 7504542613567657390989809524161942137748848640000000000 true
private noncomputable def ibox235 : Fin 4 → FixedTape.I := splitI ibox234 3 12431616634123028271385806917078617936499834880000000000000 false
private noncomputable def ibox236 : Fin 4 → FixedTape.I := splitI ibox235 0 7596061425928238578684807201285868261379932160000000000 false
private noncomputable def ibox237 : Fin 4 → FixedTape.I := splitI ibox235 0 7596061425928238578684807201285868261379932160000000000 true
private noncomputable def ibox238 : Fin 4 → FixedTape.I := splitI ibox234 3 12431616634123028271385806917078617936499834880000000000000 true
private noncomputable def ibox239 : Fin 4 → FixedTape.I := splitI ibox238 0 7596061425928238578684807201285868261379932160000000000 false
private noncomputable def ibox240 : Fin 4 → FixedTape.I := splitI ibox238 0 7596061425928238578684807201285868261379932160000000000 true
private noncomputable def ibox241 : Fin 4 → FixedTape.I := splitI ibox225 0 7687580238288819766379804878409794385011015680000000000 true
private noncomputable def ibox242 : Fin 4 → FixedTape.I := splitI ibox241 0 7870617863009982141769800232657646632273182720000000000 false
private noncomputable def ibox243 : Fin 4 → FixedTape.I := splitI ibox242 3 12431616634123028271385806917078617936499834880000000000000 false
private noncomputable def ibox244 : Fin 4 → FixedTape.I := splitI ibox243 0 7779099050649400954074802555533720508642099200000000000 false
private noncomputable def ibox245 : Fin 4 → FixedTape.I := splitI ibox243 0 7779099050649400954074802555533720508642099200000000000 true
private noncomputable def ibox246 : Fin 4 → FixedTape.I := splitI ibox242 3 12431616634123028271385806917078617936499834880000000000000 true
private noncomputable def ibox247 : Fin 4 → FixedTape.I := splitI ibox246 0 7779099050649400954074802555533720508642099200000000000 false
private noncomputable def ibox248 : Fin 4 → FixedTape.I := splitI ibox246 0 7779099050649400954074802555533720508642099200000000000 true
private noncomputable def ibox249 : Fin 4 → FixedTape.I := splitI ibox241 0 7870617863009982141769800232657646632273182720000000000 true
private noncomputable def ibox250 : Fin 4 → FixedTape.I := splitI ibox249 3 12431616634123028271385806917078617936499834880000000000000 false
private noncomputable def ibox251 : Fin 4 → FixedTape.I := splitI ibox249 3 12431616634123028271385806917078617936499834880000000000000 true
private noncomputable def ibox252 : Fin 4 → FixedTape.I := splitI ibox224 3 13387894836747876599953945910700050085461360640000000000000 true
private noncomputable def ibox253 : Fin 4 → FixedTape.I := splitI ibox252 0 7687580238288819766379804878409794385011015680000000000 false
private noncomputable def ibox254 : Fin 4 → FixedTape.I := splitI ibox253 3 14344173039372724928522084904321482234422886400000000000000 false
private noncomputable def ibox255 : Fin 4 → FixedTape.I := splitI ibox254 0 7504542613567657390989809524161942137748848640000000000 false
private noncomputable def ibox256 : Fin 4 → FixedTape.I := splitI ibox255 0 7413023801207076203294811847038016014117765120000000000 false
private noncomputable def ibox257 : Fin 4 → FixedTape.I := splitI ibox255 0 7413023801207076203294811847038016014117765120000000000 true
private noncomputable def ibox258 : Fin 4 → FixedTape.I := splitI ibox254 0 7504542613567657390989809524161942137748848640000000000 true
private noncomputable def ibox259 : Fin 4 → FixedTape.I := splitI ibox258 0 7596061425928238578684807201285868261379932160000000000 false
private noncomputable def ibox260 : Fin 4 → FixedTape.I := splitI ibox258 0 7596061425928238578684807201285868261379932160000000000 true
private noncomputable def ibox261 : Fin 4 → FixedTape.I := splitI ibox253 3 14344173039372724928522084904321482234422886400000000000000 true
private noncomputable def ibox262 : Fin 4 → FixedTape.I := splitI ibox261 0 7504542613567657390989809524161942137748848640000000000 false
private noncomputable def ibox263 : Fin 4 → FixedTape.I := splitI ibox262 3 14822312140685149092806154401132198308903649280000000000000 false
private noncomputable def ibox264 : Fin 4 → FixedTape.I := splitI ibox262 3 14822312140685149092806154401132198308903649280000000000000 true
private noncomputable def ibox265 : Fin 4 → FixedTape.I := splitI ibox261 0 7504542613567657390989809524161942137748848640000000000 true
private noncomputable def ibox266 : Fin 4 → FixedTape.I := splitI ibox265 3 14822312140685149092806154401132198308903649280000000000000 false
private noncomputable def ibox267 : Fin 4 → FixedTape.I := splitI ibox265 3 14822312140685149092806154401132198308903649280000000000000 true
private noncomputable def ibox268 : Fin 4 → FixedTape.I := splitI ibox252 0 7687580238288819766379804878409794385011015680000000000 true
private noncomputable def ibox269 : Fin 4 → FixedTape.I := splitI ibox268 3 14344173039372724928522084904321482234422886400000000000000 false
private noncomputable def ibox270 : Fin 4 → FixedTape.I := splitI ibox269 0 7870617863009982141769800232657646632273182720000000000 false
private noncomputable def ibox271 : Fin 4 → FixedTape.I := splitI ibox270 0 7779099050649400954074802555533720508642099200000000000 false
private noncomputable def ibox272 : Fin 4 → FixedTape.I := splitI ibox270 0 7779099050649400954074802555533720508642099200000000000 true
private noncomputable def ibox273 : Fin 4 → FixedTape.I := splitI ibox269 0 7870617863009982141769800232657646632273182720000000000 true
private noncomputable def ibox274 : Fin 4 → FixedTape.I := splitI ibox268 3 14344173039372724928522084904321482234422886400000000000000 true
private noncomputable def ibox275 : Fin 4 → FixedTape.I := splitI ibox274 0 7870617863009982141769800232657646632273182720000000000 false
private noncomputable def ibox276 : Fin 4 → FixedTape.I := splitI ibox274 0 7870617863009982141769800232657646632273182720000000000 true
private noncomputable def ibox277 : Fin 4 → FixedTape.I := splitI ibox34 0 8053655487731144517159795586905498879535349760000000000 true
private noncomputable def ibox278 : Fin 4 → FixedTape.I := faceI ibox277 1 false
private noncomputable def ibox279 : Fin 4 → FixedTape.I := splitI ibox278 3 7650225620998786628545111948971457191692206080000000000000 false
private noncomputable def ibox280 : Fin 4 → FixedTape.I := splitI ibox279 3 3825112810499393314272555974485728595846103040000000000000 false
private noncomputable def ibox281 : Fin 4 → FixedTape.I := splitI ibox280 0 8419730737173469267939786295401203374059683840000000000 false
private noncomputable def ibox282 : Fin 4 → FixedTape.I := splitI ibox281 3 1912556405249696657136277987242864297923051520000000000000 false
private noncomputable def ibox283 : Fin 4 → FixedTape.I := splitI ibox282 0 8236693112452306892549790941153351126797516800000000000 false
private noncomputable def ibox284 : Fin 4 → FixedTape.I := splitI ibox283 0 8145174300091725704854793264029425003166433280000000000 false
private noncomputable def ibox285 : Fin 4 → FixedTape.I := splitI ibox284 3 956278202624848328568138993621432148961525760000000000000 false
private noncomputable def ibox286 : Fin 4 → FixedTape.I := splitI ibox284 3 956278202624848328568138993621432148961525760000000000000 true
private noncomputable def ibox287 : Fin 4 → FixedTape.I := splitI ibox283 0 8145174300091725704854793264029425003166433280000000000 true
private noncomputable def ibox288 : Fin 4 → FixedTape.I := splitI ibox287 3 956278202624848328568138993621432148961525760000000000000 false
private noncomputable def ibox289 : Fin 4 → FixedTape.I := splitI ibox287 3 956278202624848328568138993621432148961525760000000000000 true
private noncomputable def ibox290 : Fin 4 → FixedTape.I := splitI ibox282 0 8236693112452306892549790941153351126797516800000000000 true
private noncomputable def ibox291 : Fin 4 → FixedTape.I := splitI ibox290 3 956278202624848328568138993621432148961525760000000000000 false
private noncomputable def ibox292 : Fin 4 → FixedTape.I := splitI ibox291 0 8328211924812888080244788618277277250428600320000000000 false
private noncomputable def ibox293 : Fin 4 → FixedTape.I := splitI ibox291 0 8328211924812888080244788618277277250428600320000000000 true
private noncomputable def ibox294 : Fin 4 → FixedTape.I := splitI ibox290 3 956278202624848328568138993621432148961525760000000000000 true
private noncomputable def ibox295 : Fin 4 → FixedTape.I := splitI ibox294 0 8328211924812888080244788618277277250428600320000000000 false
private noncomputable def ibox296 : Fin 4 → FixedTape.I := splitI ibox294 0 8328211924812888080244788618277277250428600320000000000 true
private noncomputable def ibox297 : Fin 4 → FixedTape.I := splitI ibox281 3 1912556405249696657136277987242864297923051520000000000000 true
private noncomputable def ibox298 : Fin 4 → FixedTape.I := splitI ibox297 0 8236693112452306892549790941153351126797516800000000000 false
private noncomputable def ibox299 : Fin 4 → FixedTape.I := splitI ibox298 3 2868834607874544985704416980864296446884577280000000000000 false
private noncomputable def ibox300 : Fin 4 → FixedTape.I := splitI ibox299 0 8145174300091725704854793264029425003166433280000000000 false
private noncomputable def ibox301 : Fin 4 → FixedTape.I := splitI ibox299 0 8145174300091725704854793264029425003166433280000000000 true
private noncomputable def ibox302 : Fin 4 → FixedTape.I := splitI ibox298 3 2868834607874544985704416980864296446884577280000000000000 true
private noncomputable def ibox303 : Fin 4 → FixedTape.I := splitI ibox302 0 8145174300091725704854793264029425003166433280000000000 false
private noncomputable def ibox304 : Fin 4 → FixedTape.I := splitI ibox302 0 8145174300091725704854793264029425003166433280000000000 true
private noncomputable def ibox305 : Fin 4 → FixedTape.I := splitI ibox297 0 8236693112452306892549790941153351126797516800000000000 true
private noncomputable def ibox306 : Fin 4 → FixedTape.I := splitI ibox305 3 2868834607874544985704416980864296446884577280000000000000 false
private noncomputable def ibox307 : Fin 4 → FixedTape.I := splitI ibox305 3 2868834607874544985704416980864296446884577280000000000000 true
private noncomputable def ibox308 : Fin 4 → FixedTape.I := splitI ibox280 0 8419730737173469267939786295401203374059683840000000000 true
private noncomputable def ibox309 : Fin 4 → FixedTape.I := splitI ibox308 3 1912556405249696657136277987242864297923051520000000000000 false
private noncomputable def ibox310 : Fin 4 → FixedTape.I := splitI ibox309 0 8602768361894631643329781649649055621321850880000000000 false
private noncomputable def ibox311 : Fin 4 → FixedTape.I := splitI ibox310 3 956278202624848328568138993621432148961525760000000000000 false
private noncomputable def ibox312 : Fin 4 → FixedTape.I := splitI ibox310 3 956278202624848328568138993621432148961525760000000000000 true
private noncomputable def ibox313 : Fin 4 → FixedTape.I := splitI ibox309 0 8602768361894631643329781649649055621321850880000000000 true
private noncomputable def ibox314 : Fin 4 → FixedTape.I := splitI ibox313 3 956278202624848328568138993621432148961525760000000000000 false
private noncomputable def ibox315 : Fin 4 → FixedTape.I := splitI ibox313 3 956278202624848328568138993621432148961525760000000000000 true
private noncomputable def ibox316 : Fin 4 → FixedTape.I := splitI ibox308 3 1912556405249696657136277987242864297923051520000000000000 true
private noncomputable def ibox317 : Fin 4 → FixedTape.I := splitI ibox316 0 8602768361894631643329781649649055621321850880000000000 false
private noncomputable def ibox318 : Fin 4 → FixedTape.I := splitI ibox317 3 2868834607874544985704416980864296446884577280000000000000 false
private noncomputable def ibox319 : Fin 4 → FixedTape.I := splitI ibox317 3 2868834607874544985704416980864296446884577280000000000000 true
private noncomputable def ibox320 : Fin 4 → FixedTape.I := splitI ibox316 0 8602768361894631643329781649649055621321850880000000000 true
private noncomputable def ibox321 : Fin 4 → FixedTape.I := splitI ibox320 3 2868834607874544985704416980864296446884577280000000000000 false
private noncomputable def ibox322 : Fin 4 → FixedTape.I := splitI ibox320 3 2868834607874544985704416980864296446884577280000000000000 true
private noncomputable def ibox323 : Fin 4 → FixedTape.I := splitI ibox279 3 3825112810499393314272555974485728595846103040000000000000 true
private noncomputable def ibox324 : Fin 4 → FixedTape.I := splitI ibox323 0 8419730737173469267939786295401203374059683840000000000 false
private noncomputable def ibox325 : Fin 4 → FixedTape.I := splitI ibox324 3 5737669215749089971408833961728592893769154560000000000000 false
private noncomputable def ibox326 : Fin 4 → FixedTape.I := splitI ibox325 0 8236693112452306892549790941153351126797516800000000000 false
private noncomputable def ibox327 : Fin 4 → FixedTape.I := splitI ibox326 3 4781391013124241642840694968107160744807628800000000000000 false
private noncomputable def ibox328 : Fin 4 → FixedTape.I := splitI ibox327 0 8145174300091725704854793264029425003166433280000000000 false
private noncomputable def ibox329 : Fin 4 → FixedTape.I := splitI ibox327 0 8145174300091725704854793264029425003166433280000000000 true
private noncomputable def ibox330 : Fin 4 → FixedTape.I := splitI ibox326 3 4781391013124241642840694968107160744807628800000000000000 true
private noncomputable def ibox331 : Fin 4 → FixedTape.I := splitI ibox330 0 8145174300091725704854793264029425003166433280000000000 false
private noncomputable def ibox332 : Fin 4 → FixedTape.I := splitI ibox330 0 8145174300091725704854793264029425003166433280000000000 true
private noncomputable def ibox333 : Fin 4 → FixedTape.I := splitI ibox325 0 8236693112452306892549790941153351126797516800000000000 true
private noncomputable def ibox334 : Fin 4 → FixedTape.I := splitI ibox333 3 4781391013124241642840694968107160744807628800000000000000 false
private noncomputable def ibox335 : Fin 4 → FixedTape.I := splitI ibox333 3 4781391013124241642840694968107160744807628800000000000000 true
private noncomputable def ibox336 : Fin 4 → FixedTape.I := splitI ibox324 3 5737669215749089971408833961728592893769154560000000000000 true
private noncomputable def ibox337 : Fin 4 → FixedTape.I := splitI ibox336 0 8236693112452306892549790941153351126797516800000000000 false
private noncomputable def ibox338 : Fin 4 → FixedTape.I := splitI ibox337 3 6693947418373938299976972955350025042730680320000000000000 false
private noncomputable def ibox339 : Fin 4 → FixedTape.I := splitI ibox337 3 6693947418373938299976972955350025042730680320000000000000 true
private noncomputable def ibox340 : Fin 4 → FixedTape.I := splitI ibox336 0 8236693112452306892549790941153351126797516800000000000 true
private noncomputable def ibox341 : Fin 4 → FixedTape.I := splitI ibox340 3 6693947418373938299976972955350025042730680320000000000000 false
private noncomputable def ibox342 : Fin 4 → FixedTape.I := splitI ibox340 3 6693947418373938299976972955350025042730680320000000000000 true
private noncomputable def ibox343 : Fin 4 → FixedTape.I := splitI ibox323 0 8419730737173469267939786295401203374059683840000000000 true
private noncomputable def ibox344 : Fin 4 → FixedTape.I := splitI ibox343 3 5737669215749089971408833961728592893769154560000000000000 false
private noncomputable def ibox345 : Fin 4 → FixedTape.I := splitI ibox344 0 8602768361894631643329781649649055621321850880000000000 false
private noncomputable def ibox346 : Fin 4 → FixedTape.I := splitI ibox345 3 4781391013124241642840694968107160744807628800000000000000 false
private noncomputable def ibox347 : Fin 4 → FixedTape.I := splitI ibox345 3 4781391013124241642840694968107160744807628800000000000000 true
private noncomputable def ibox348 : Fin 4 → FixedTape.I := splitI ibox344 0 8602768361894631643329781649649055621321850880000000000 true
private noncomputable def ibox349 : Fin 4 → FixedTape.I := splitI ibox348 3 4781391013124241642840694968107160744807628800000000000000 false
private noncomputable def ibox350 : Fin 4 → FixedTape.I := splitI ibox348 3 4781391013124241642840694968107160744807628800000000000000 true
private noncomputable def ibox351 : Fin 4 → FixedTape.I := splitI ibox343 3 5737669215749089971408833961728592893769154560000000000000 true
private noncomputable def ibox352 : Fin 4 → FixedTape.I := splitI ibox351 0 8602768361894631643329781649649055621321850880000000000 false
private noncomputable def ibox353 : Fin 4 → FixedTape.I := splitI ibox352 3 6693947418373938299976972955350025042730680320000000000000 false
private noncomputable def ibox354 : Fin 4 → FixedTape.I := splitI ibox352 3 6693947418373938299976972955350025042730680320000000000000 true
private noncomputable def ibox355 : Fin 4 → FixedTape.I := splitI ibox351 0 8602768361894631643329781649649055621321850880000000000 true
private noncomputable def ibox356 : Fin 4 → FixedTape.I := splitI ibox355 3 6693947418373938299976972955350025042730680320000000000000 false
private noncomputable def ibox357 : Fin 4 → FixedTape.I := splitI ibox355 3 6693947418373938299976972955350025042730680320000000000000 true
private noncomputable def ibox358 : Fin 4 → FixedTape.I := splitI ibox278 3 7650225620998786628545111948971457191692206080000000000000 true
private noncomputable def ibox359 : Fin 4 → FixedTape.I := splitI ibox358 3 11475338431498179942817667923457185787538309120000000000000 false
private noncomputable def ibox360 : Fin 4 → FixedTape.I := splitI ibox359 0 8419730737173469267939786295401203374059683840000000000 false
private noncomputable def ibox361 : Fin 4 → FixedTape.I := splitI ibox360 3 9562782026248483285681389936214321489615257600000000000000 false
private noncomputable def ibox362 : Fin 4 → FixedTape.I := splitI ibox361 0 8236693112452306892549790941153351126797516800000000000 false
private noncomputable def ibox363 : Fin 4 → FixedTape.I := splitI ibox362 3 8606503823623634957113250942592889340653731840000000000000 false
private noncomputable def ibox364 : Fin 4 → FixedTape.I := splitI ibox362 3 8606503823623634957113250942592889340653731840000000000000 true
private noncomputable def ibox365 : Fin 4 → FixedTape.I := splitI ibox361 0 8236693112452306892549790941153351126797516800000000000 true
private noncomputable def ibox366 : Fin 4 → FixedTape.I := splitI ibox365 3 8606503823623634957113250942592889340653731840000000000000 false
private noncomputable def ibox367 : Fin 4 → FixedTape.I := splitI ibox365 3 8606503823623634957113250942592889340653731840000000000000 true
private noncomputable def ibox368 : Fin 4 → FixedTape.I := splitI ibox360 3 9562782026248483285681389936214321489615257600000000000000 true
private noncomputable def ibox369 : Fin 4 → FixedTape.I := splitI ibox368 0 8236693112452306892549790941153351126797516800000000000 false
private noncomputable def ibox370 : Fin 4 → FixedTape.I := splitI ibox369 3 10519060228873331614249528929835753638576783360000000000000 false
private noncomputable def ibox371 : Fin 4 → FixedTape.I := splitI ibox369 3 10519060228873331614249528929835753638576783360000000000000 true
private noncomputable def ibox372 : Fin 4 → FixedTape.I := splitI ibox368 0 8236693112452306892549790941153351126797516800000000000 true
private noncomputable def ibox373 : Fin 4 → FixedTape.I := splitI ibox372 3 10519060228873331614249528929835753638576783360000000000000 false
private noncomputable def ibox374 : Fin 4 → FixedTape.I := splitI ibox372 3 10519060228873331614249528929835753638576783360000000000000 true
private noncomputable def ibox375 : Fin 4 → FixedTape.I := splitI ibox359 0 8419730737173469267939786295401203374059683840000000000 true
private noncomputable def ibox376 : Fin 4 → FixedTape.I := splitI ibox375 3 9562782026248483285681389936214321489615257600000000000000 false
private noncomputable def ibox377 : Fin 4 → FixedTape.I := splitI ibox376 0 8602768361894631643329781649649055621321850880000000000 false
private noncomputable def ibox378 : Fin 4 → FixedTape.I := splitI ibox377 3 8606503823623634957113250942592889340653731840000000000000 false
private noncomputable def ibox379 : Fin 4 → FixedTape.I := splitI ibox377 3 8606503823623634957113250942592889340653731840000000000000 true
private noncomputable def ibox380 : Fin 4 → FixedTape.I := splitI ibox376 0 8602768361894631643329781649649055621321850880000000000 true
private noncomputable def ibox381 : Fin 4 → FixedTape.I := splitI ibox380 3 8606503823623634957113250942592889340653731840000000000000 false
private noncomputable def ibox382 : Fin 4 → FixedTape.I := splitI ibox380 3 8606503823623634957113250942592889340653731840000000000000 true
private noncomputable def ibox383 : Fin 4 → FixedTape.I := splitI ibox375 3 9562782026248483285681389936214321489615257600000000000000 true
private noncomputable def ibox384 : Fin 4 → FixedTape.I := splitI ibox383 0 8602768361894631643329781649649055621321850880000000000 false
private noncomputable def ibox385 : Fin 4 → FixedTape.I := splitI ibox384 3 10519060228873331614249528929835753638576783360000000000000 false
private noncomputable def ibox386 : Fin 4 → FixedTape.I := splitI ibox384 3 10519060228873331614249528929835753638576783360000000000000 true
private noncomputable def ibox387 : Fin 4 → FixedTape.I := splitI ibox383 0 8602768361894631643329781649649055621321850880000000000 true
private noncomputable def ibox388 : Fin 4 → FixedTape.I := splitI ibox387 3 10519060228873331614249528929835753638576783360000000000000 false
private noncomputable def ibox389 : Fin 4 → FixedTape.I := splitI ibox387 3 10519060228873331614249528929835753638576783360000000000000 true
private noncomputable def ibox390 : Fin 4 → FixedTape.I := splitI ibox358 3 11475338431498179942817667923457185787538309120000000000000 true
private noncomputable def ibox391 : Fin 4 → FixedTape.I := splitI ibox390 3 13387894836747876599953945910700050085461360640000000000000 false
private noncomputable def ibox392 : Fin 4 → FixedTape.I := splitI ibox391 0 8419730737173469267939786295401203374059683840000000000 false
private noncomputable def ibox393 : Fin 4 → FixedTape.I := splitI ibox392 0 8236693112452306892549790941153351126797516800000000000 false
private noncomputable def ibox394 : Fin 4 → FixedTape.I := splitI ibox393 3 12431616634123028271385806917078617936499834880000000000000 false
private noncomputable def ibox395 : Fin 4 → FixedTape.I := splitI ibox393 3 12431616634123028271385806917078617936499834880000000000000 true
private noncomputable def ibox396 : Fin 4 → FixedTape.I := splitI ibox392 0 8236693112452306892549790941153351126797516800000000000 true
private noncomputable def ibox397 : Fin 4 → FixedTape.I := splitI ibox396 3 12431616634123028271385806917078617936499834880000000000000 false
private noncomputable def ibox398 : Fin 4 → FixedTape.I := splitI ibox396 3 12431616634123028271385806917078617936499834880000000000000 true
private noncomputable def ibox399 : Fin 4 → FixedTape.I := splitI ibox391 0 8419730737173469267939786295401203374059683840000000000 true
private noncomputable def ibox400 : Fin 4 → FixedTape.I := splitI ibox399 0 8602768361894631643329781649649055621321850880000000000 false
private noncomputable def ibox401 : Fin 4 → FixedTape.I := splitI ibox400 3 12431616634123028271385806917078617936499834880000000000000 false
private noncomputable def ibox402 : Fin 4 → FixedTape.I := splitI ibox400 3 12431616634123028271385806917078617936499834880000000000000 true
private noncomputable def ibox403 : Fin 4 → FixedTape.I := splitI ibox399 0 8602768361894631643329781649649055621321850880000000000 true
private noncomputable def ibox404 : Fin 4 → FixedTape.I := splitI ibox403 3 12431616634123028271385806917078617936499834880000000000000 false
private noncomputable def ibox405 : Fin 4 → FixedTape.I := splitI ibox403 3 12431616634123028271385806917078617936499834880000000000000 true
private noncomputable def ibox406 : Fin 4 → FixedTape.I := splitI ibox390 3 13387894836747876599953945910700050085461360640000000000000 true
private noncomputable def ibox407 : Fin 4 → FixedTape.I := splitI ibox406 0 8419730737173469267939786295401203374059683840000000000 false
private noncomputable def ibox408 : Fin 4 → FixedTape.I := splitI ibox407 3 14344173039372724928522084904321482234422886400000000000000 false
private noncomputable def ibox409 : Fin 4 → FixedTape.I := splitI ibox408 0 8236693112452306892549790941153351126797516800000000000 false
private noncomputable def ibox410 : Fin 4 → FixedTape.I := splitI ibox408 0 8236693112452306892549790941153351126797516800000000000 true
private noncomputable def ibox411 : Fin 4 → FixedTape.I := splitI ibox407 3 14344173039372724928522084904321482234422886400000000000000 true
private noncomputable def ibox412 : Fin 4 → FixedTape.I := splitI ibox411 0 8236693112452306892549790941153351126797516800000000000 false
private noncomputable def ibox413 : Fin 4 → FixedTape.I := splitI ibox411 0 8236693112452306892549790941153351126797516800000000000 true
private noncomputable def ibox414 : Fin 4 → FixedTape.I := splitI ibox406 0 8419730737173469267939786295401203374059683840000000000 true
private noncomputable def ibox415 : Fin 4 → FixedTape.I := splitI ibox414 3 14344173039372724928522084904321482234422886400000000000000 false
private noncomputable def ibox416 : Fin 4 → FixedTape.I := splitI ibox415 0 8602768361894631643329781649649055621321850880000000000 false
private noncomputable def ibox417 : Fin 4 → FixedTape.I := splitI ibox415 0 8602768361894631643329781649649055621321850880000000000 true
private noncomputable def ibox418 : Fin 4 → FixedTape.I := splitI ibox414 3 14344173039372724928522084904321482234422886400000000000000 true
private noncomputable def ibox419 : Fin 4 → FixedTape.I := splitI ibox418 0 8602768361894631643329781649649055621321850880000000000 false
private noncomputable def ibox420 : Fin 4 → FixedTape.I := splitI ibox418 0 8602768361894631643329781649649055621321850880000000000 true
private noncomputable def ibox421 : Fin 4 → FixedTape.I := splitI ibox33 1 1912556405249696657136277987242864297923051520000000000000 true
private noncomputable def ibox422 : Fin 4 → FixedTape.I := splitI ibox421 0 8053655487731144517159795586905498879535349760000000000 false
private noncomputable def ibox423 : Fin 4 → FixedTape.I := faceI ibox422 1 false
private noncomputable def ibox424 : Fin 4 → FixedTape.I := splitI ibox423 3 7650225620998786628545111948971457191692206080000000000000 false
private noncomputable def ibox425 : Fin 4 → FixedTape.I := splitI ibox423 3 7650225620998786628545111948971457191692206080000000000000 true
private noncomputable def ibox426 : Fin 4 → FixedTape.I := splitI ibox421 0 8053655487731144517159795586905498879535349760000000000 true
private noncomputable def ibox427 : Fin 4 → FixedTape.I := faceI ibox426 1 false
private noncomputable def ibox428 : Fin 4 → FixedTape.I := splitI ibox427 3 7650225620998786628545111948971457191692206080000000000000 false
private noncomputable def ibox429 : Fin 4 → FixedTape.I := splitI ibox427 3 7650225620998786628545111948971457191692206080000000000000 true
private noncomputable def ibox430 : Fin 4 → FixedTape.I := splitI ibox32 1 3825112810499393314272555974485728595846103040000000000000 true
private noncomputable def ibox431 : Fin 4 → FixedTape.I := splitI ibox430 0 8053655487731144517159795586905498879535349760000000000 false
private noncomputable def ibox432 : Fin 4 → FixedTape.I := faceI ibox431 1 false
private noncomputable def ibox433 : Fin 4 → FixedTape.I := splitI ibox430 0 8053655487731144517159795586905498879535349760000000000 true
private noncomputable def ibox434 : Fin 4 → FixedTape.I := faceI ibox433 1 false
private noncomputable def ibox435 : Fin 4 → FixedTape.I := splitI ibox30 1 7650225620998786628545111948971457191692206080000000000000 true
private noncomputable def ibox436 : Fin 4 → FixedTape.I := faceI ibox435 3 false
private noncomputable def ibox437 : Fin 4 → FixedTape.I := splitI ibox436 0 8053655487731144517159795586905498879535349760000000000 false
private noncomputable def ibox438 : Fin 4 → FixedTape.I := splitI ibox437 1 11475338431498179942817667923457185787538309120000000000000 false
private noncomputable def ibox439 : Fin 4 → FixedTape.I := splitI ibox437 1 11475338431498179942817667923457185787538309120000000000000 true
private noncomputable def ibox440 : Fin 4 → FixedTape.I := splitI ibox436 0 8053655487731144517159795586905498879535349760000000000 true
private noncomputable def ibox441 : Fin 4 → FixedTape.I := splitI ibox440 1 11475338431498179942817667923457185787538309120000000000000 false
private noncomputable def ibox442 : Fin 4 → FixedTape.I := splitI ibox440 1 11475338431498179942817667923457185787538309120000000000000 true
private noncomputable def ibox443 : Fin 4 → FixedTape.I := splitI ibox19 0 8785805986615794018719777003896907868584017920000000000 true
private noncomputable def ibox444 : Fin 4 → FixedTape.I := splitI ibox443 2 11475338431498179942817667923457185787538309120000000000000 false
private noncomputable def ibox445 : Fin 4 → FixedTape.I := faceI ibox444 3 false
private noncomputable def ibox446 : Fin 4 → FixedTape.I := splitI ibox445 0 9517956485500443520279758420888316857632686080000000000 false
private noncomputable def ibox447 : Fin 4 → FixedTape.I := splitI ibox446 1 7650225620998786628545111948971457191692206080000000000000 false
private noncomputable def ibox448 : Fin 4 → FixedTape.I := splitI ibox446 1 7650225620998786628545111948971457191692206080000000000000 true
private noncomputable def ibox449 : Fin 4 → FixedTape.I := splitI ibox445 0 9517956485500443520279758420888316857632686080000000000 true
private noncomputable def ibox450 : Fin 4 → FixedTape.I := splitI ibox449 1 7650225620998786628545111948971457191692206080000000000000 false
private noncomputable def ibox451 : Fin 4 → FixedTape.I := splitI ibox449 1 7650225620998786628545111948971457191692206080000000000000 true
private noncomputable def ibox452 : Fin 4 → FixedTape.I := splitI ibox443 2 11475338431498179942817667923457185787538309120000000000000 true
private noncomputable def ibox453 : Fin 4 → FixedTape.I := splitI ibox452 1 7650225620998786628545111948971457191692206080000000000000 false
private noncomputable def ibox454 : Fin 4 → FixedTape.I := faceI ibox453 2 true
private noncomputable def ibox455 : Fin 4 → FixedTape.I := splitI ibox454 1 3825112810499393314272555974485728595846103040000000000000 false
private noncomputable def ibox456 : Fin 4 → FixedTape.I := splitI ibox455 1 1912556405249696657136277987242864297923051520000000000000 false
private noncomputable def ibox457 : Fin 4 → FixedTape.I := splitI ibox456 0 9517956485500443520279758420888316857632686080000000000 false
private noncomputable def ibox458 : Fin 4 → FixedTape.I := faceI ibox457 1 false
private noncomputable def ibox459 : Fin 4 → FixedTape.I := splitI ibox458 3 7650225620998786628545111948971457191692206080000000000000 false
private noncomputable def ibox460 : Fin 4 → FixedTape.I := splitI ibox459 3 3825112810499393314272555974485728595846103040000000000000 false
private noncomputable def ibox461 : Fin 4 → FixedTape.I := splitI ibox460 0 9151881236058118769499767712392612363108352000000000000 false
private noncomputable def ibox462 : Fin 4 → FixedTape.I := splitI ibox461 3 1912556405249696657136277987242864297923051520000000000000 false
private noncomputable def ibox463 : Fin 4 → FixedTape.I := splitI ibox462 0 8968843611336956394109772358144760115846184960000000000 false
private noncomputable def ibox464 : Fin 4 → FixedTape.I := splitI ibox463 3 956278202624848328568138993621432148961525760000000000000 false
private noncomputable def ibox465 : Fin 4 → FixedTape.I := splitI ibox463 3 956278202624848328568138993621432148961525760000000000000 true
private noncomputable def ibox466 : Fin 4 → FixedTape.I := splitI ibox462 0 8968843611336956394109772358144760115846184960000000000 true
private noncomputable def ibox467 : Fin 4 → FixedTape.I := splitI ibox466 3 956278202624848328568138993621432148961525760000000000000 false
private noncomputable def ibox468 : Fin 4 → FixedTape.I := splitI ibox466 3 956278202624848328568138993621432148961525760000000000000 true
private noncomputable def ibox469 : Fin 4 → FixedTape.I := splitI ibox461 3 1912556405249696657136277987242864297923051520000000000000 true
private noncomputable def ibox470 : Fin 4 → FixedTape.I := splitI ibox469 0 8968843611336956394109772358144760115846184960000000000 false
private noncomputable def ibox471 : Fin 4 → FixedTape.I := splitI ibox470 3 2868834607874544985704416980864296446884577280000000000000 false
private noncomputable def ibox472 : Fin 4 → FixedTape.I := splitI ibox470 3 2868834607874544985704416980864296446884577280000000000000 true
private noncomputable def ibox473 : Fin 4 → FixedTape.I := splitI ibox469 0 8968843611336956394109772358144760115846184960000000000 true
private noncomputable def ibox474 : Fin 4 → FixedTape.I := splitI ibox473 3 2868834607874544985704416980864296446884577280000000000000 false
private noncomputable def ibox475 : Fin 4 → FixedTape.I := splitI ibox473 3 2868834607874544985704416980864296446884577280000000000000 true
private noncomputable def ibox476 : Fin 4 → FixedTape.I := splitI ibox460 0 9151881236058118769499767712392612363108352000000000000 true
private noncomputable def ibox477 : Fin 4 → FixedTape.I := splitI ibox476 3 1912556405249696657136277987242864297923051520000000000000 false
private noncomputable def ibox478 : Fin 4 → FixedTape.I := splitI ibox477 0 9334918860779281144889763066640464610370519040000000000 false
private noncomputable def ibox479 : Fin 4 → FixedTape.I := splitI ibox478 3 956278202624848328568138993621432148961525760000000000000 false
private noncomputable def ibox480 : Fin 4 → FixedTape.I := splitI ibox478 3 956278202624848328568138993621432148961525760000000000000 true
private noncomputable def ibox481 : Fin 4 → FixedTape.I := splitI ibox477 0 9334918860779281144889763066640464610370519040000000000 true
private noncomputable def ibox482 : Fin 4 → FixedTape.I := splitI ibox481 3 956278202624848328568138993621432148961525760000000000000 false
private noncomputable def ibox483 : Fin 4 → FixedTape.I := splitI ibox481 3 956278202624848328568138993621432148961525760000000000000 true
private noncomputable def ibox484 : Fin 4 → FixedTape.I := splitI ibox476 3 1912556405249696657136277987242864297923051520000000000000 true
private noncomputable def ibox485 : Fin 4 → FixedTape.I := splitI ibox484 0 9334918860779281144889763066640464610370519040000000000 false
private noncomputable def ibox486 : Fin 4 → FixedTape.I := splitI ibox485 3 2868834607874544985704416980864296446884577280000000000000 false
private noncomputable def ibox487 : Fin 4 → FixedTape.I := splitI ibox485 3 2868834607874544985704416980864296446884577280000000000000 true
private noncomputable def ibox488 : Fin 4 → FixedTape.I := splitI ibox484 0 9334918860779281144889763066640464610370519040000000000 true
private noncomputable def ibox489 : Fin 4 → FixedTape.I := splitI ibox488 3 2868834607874544985704416980864296446884577280000000000000 false
private noncomputable def ibox490 : Fin 4 → FixedTape.I := splitI ibox488 3 2868834607874544985704416980864296446884577280000000000000 true
private noncomputable def ibox491 : Fin 4 → FixedTape.I := splitI ibox459 3 3825112810499393314272555974485728595846103040000000000000 true
private noncomputable def ibox492 : Fin 4 → FixedTape.I := splitI ibox491 0 9151881236058118769499767712392612363108352000000000000 false
private noncomputable def ibox493 : Fin 4 → FixedTape.I := splitI ibox492 3 5737669215749089971408833961728592893769154560000000000000 false
private noncomputable def ibox494 : Fin 4 → FixedTape.I := splitI ibox493 0 8968843611336956394109772358144760115846184960000000000 false
private noncomputable def ibox495 : Fin 4 → FixedTape.I := splitI ibox494 3 4781391013124241642840694968107160744807628800000000000000 false
private noncomputable def ibox496 : Fin 4 → FixedTape.I := splitI ibox494 3 4781391013124241642840694968107160744807628800000000000000 true
private noncomputable def ibox497 : Fin 4 → FixedTape.I := splitI ibox493 0 8968843611336956394109772358144760115846184960000000000 true
private noncomputable def ibox498 : Fin 4 → FixedTape.I := splitI ibox497 3 4781391013124241642840694968107160744807628800000000000000 false
private noncomputable def ibox499 : Fin 4 → FixedTape.I := splitI ibox497 3 4781391013124241642840694968107160744807628800000000000000 true
private noncomputable def ibox500 : Fin 4 → FixedTape.I := splitI ibox492 3 5737669215749089971408833961728592893769154560000000000000 true
private noncomputable def ibox501 : Fin 4 → FixedTape.I := splitI ibox500 0 8968843611336956394109772358144760115846184960000000000 false
private noncomputable def ibox502 : Fin 4 → FixedTape.I := splitI ibox501 3 6693947418373938299976972955350025042730680320000000000000 false
private noncomputable def ibox503 : Fin 4 → FixedTape.I := splitI ibox501 3 6693947418373938299976972955350025042730680320000000000000 true
private noncomputable def ibox504 : Fin 4 → FixedTape.I := splitI ibox500 0 8968843611336956394109772358144760115846184960000000000 true
private noncomputable def ibox505 : Fin 4 → FixedTape.I := splitI ibox504 3 6693947418373938299976972955350025042730680320000000000000 false
private noncomputable def ibox506 : Fin 4 → FixedTape.I := splitI ibox504 3 6693947418373938299976972955350025042730680320000000000000 true
private noncomputable def ibox507 : Fin 4 → FixedTape.I := splitI ibox491 0 9151881236058118769499767712392612363108352000000000000 true
private noncomputable def ibox508 : Fin 4 → FixedTape.I := splitI ibox507 3 5737669215749089971408833961728592893769154560000000000000 false
private noncomputable def ibox509 : Fin 4 → FixedTape.I := splitI ibox508 0 9334918860779281144889763066640464610370519040000000000 false
private noncomputable def ibox510 : Fin 4 → FixedTape.I := splitI ibox509 3 4781391013124241642840694968107160744807628800000000000000 false
private noncomputable def ibox511 : Fin 4 → FixedTape.I := splitI ibox509 3 4781391013124241642840694968107160744807628800000000000000 true
private noncomputable def ibox512 : Fin 4 → FixedTape.I := splitI ibox508 0 9334918860779281144889763066640464610370519040000000000 true
private noncomputable def ibox513 : Fin 4 → FixedTape.I := splitI ibox512 3 4781391013124241642840694968107160744807628800000000000000 false
private noncomputable def ibox514 : Fin 4 → FixedTape.I := splitI ibox512 3 4781391013124241642840694968107160744807628800000000000000 true
private noncomputable def ibox515 : Fin 4 → FixedTape.I := splitI ibox507 3 5737669215749089971408833961728592893769154560000000000000 true
private noncomputable def ibox516 : Fin 4 → FixedTape.I := splitI ibox515 0 9334918860779281144889763066640464610370519040000000000 false
private noncomputable def ibox517 : Fin 4 → FixedTape.I := splitI ibox516 3 6693947418373938299976972955350025042730680320000000000000 false
private noncomputable def ibox518 : Fin 4 → FixedTape.I := splitI ibox516 3 6693947418373938299976972955350025042730680320000000000000 true
private noncomputable def ibox519 : Fin 4 → FixedTape.I := splitI ibox515 0 9334918860779281144889763066640464610370519040000000000 true
private noncomputable def ibox520 : Fin 4 → FixedTape.I := splitI ibox519 3 6693947418373938299976972955350025042730680320000000000000 false
private noncomputable def ibox521 : Fin 4 → FixedTape.I := splitI ibox519 3 6693947418373938299976972955350025042730680320000000000000 true
private noncomputable def ibox522 : Fin 4 → FixedTape.I := splitI ibox458 3 7650225620998786628545111948971457191692206080000000000000 true
private noncomputable def ibox523 : Fin 4 → FixedTape.I := splitI ibox522 3 11475338431498179942817667923457185787538309120000000000000 false
private noncomputable def ibox524 : Fin 4 → FixedTape.I := splitI ibox523 0 9151881236058118769499767712392612363108352000000000000 false
private noncomputable def ibox525 : Fin 4 → FixedTape.I := splitI ibox524 3 9562782026248483285681389936214321489615257600000000000000 false
private noncomputable def ibox526 : Fin 4 → FixedTape.I := splitI ibox525 0 8968843611336956394109772358144760115846184960000000000 false
private noncomputable def ibox527 : Fin 4 → FixedTape.I := splitI ibox526 3 8606503823623634957113250942592889340653731840000000000000 false
private noncomputable def ibox528 : Fin 4 → FixedTape.I := splitI ibox526 3 8606503823623634957113250942592889340653731840000000000000 true
private noncomputable def ibox529 : Fin 4 → FixedTape.I := splitI ibox525 0 8968843611336956394109772358144760115846184960000000000 true
private noncomputable def ibox530 : Fin 4 → FixedTape.I := splitI ibox529 3 8606503823623634957113250942592889340653731840000000000000 false
private noncomputable def ibox531 : Fin 4 → FixedTape.I := splitI ibox529 3 8606503823623634957113250942592889340653731840000000000000 true
private noncomputable def ibox532 : Fin 4 → FixedTape.I := splitI ibox524 3 9562782026248483285681389936214321489615257600000000000000 true
private noncomputable def ibox533 : Fin 4 → FixedTape.I := splitI ibox532 0 8968843611336956394109772358144760115846184960000000000 false
private noncomputable def ibox534 : Fin 4 → FixedTape.I := splitI ibox533 3 10519060228873331614249528929835753638576783360000000000000 false
private noncomputable def ibox535 : Fin 4 → FixedTape.I := splitI ibox533 3 10519060228873331614249528929835753638576783360000000000000 true
private noncomputable def ibox536 : Fin 4 → FixedTape.I := splitI ibox532 0 8968843611336956394109772358144760115846184960000000000 true
private noncomputable def ibox537 : Fin 4 → FixedTape.I := splitI ibox536 3 10519060228873331614249528929835753638576783360000000000000 false
private noncomputable def ibox538 : Fin 4 → FixedTape.I := splitI ibox536 3 10519060228873331614249528929835753638576783360000000000000 true
private noncomputable def ibox539 : Fin 4 → FixedTape.I := splitI ibox523 0 9151881236058118769499767712392612363108352000000000000 true
private noncomputable def ibox540 : Fin 4 → FixedTape.I := splitI ibox539 3 9562782026248483285681389936214321489615257600000000000000 false
private noncomputable def ibox541 : Fin 4 → FixedTape.I := splitI ibox540 0 9334918860779281144889763066640464610370519040000000000 false
private noncomputable def ibox542 : Fin 4 → FixedTape.I := splitI ibox541 3 8606503823623634957113250942592889340653731840000000000000 false
private noncomputable def ibox543 : Fin 4 → FixedTape.I := splitI ibox541 3 8606503823623634957113250942592889340653731840000000000000 true
private noncomputable def ibox544 : Fin 4 → FixedTape.I := splitI ibox540 0 9334918860779281144889763066640464610370519040000000000 true
private noncomputable def ibox545 : Fin 4 → FixedTape.I := splitI ibox544 3 8606503823623634957113250942592889340653731840000000000000 false
private noncomputable def ibox546 : Fin 4 → FixedTape.I := splitI ibox544 3 8606503823623634957113250942592889340653731840000000000000 true
private noncomputable def ibox547 : Fin 4 → FixedTape.I := splitI ibox539 3 9562782026248483285681389936214321489615257600000000000000 true
private noncomputable def ibox548 : Fin 4 → FixedTape.I := splitI ibox547 0 9334918860779281144889763066640464610370519040000000000 false
private noncomputable def ibox549 : Fin 4 → FixedTape.I := splitI ibox548 3 10519060228873331614249528929835753638576783360000000000000 false
private noncomputable def ibox550 : Fin 4 → FixedTape.I := splitI ibox548 3 10519060228873331614249528929835753638576783360000000000000 true
private noncomputable def ibox551 : Fin 4 → FixedTape.I := splitI ibox547 0 9334918860779281144889763066640464610370519040000000000 true
private noncomputable def ibox552 : Fin 4 → FixedTape.I := splitI ibox551 3 10519060228873331614249528929835753638576783360000000000000 false
private noncomputable def ibox553 : Fin 4 → FixedTape.I := splitI ibox551 3 10519060228873331614249528929835753638576783360000000000000 true
private noncomputable def ibox554 : Fin 4 → FixedTape.I := splitI ibox522 3 11475338431498179942817667923457185787538309120000000000000 true
private noncomputable def ibox555 : Fin 4 → FixedTape.I := splitI ibox554 3 13387894836747876599953945910700050085461360640000000000000 false
private noncomputable def ibox556 : Fin 4 → FixedTape.I := splitI ibox555 0 9151881236058118769499767712392612363108352000000000000 false
private noncomputable def ibox557 : Fin 4 → FixedTape.I := splitI ibox556 3 12431616634123028271385806917078617936499834880000000000000 false
private noncomputable def ibox558 : Fin 4 → FixedTape.I := splitI ibox557 0 8968843611336956394109772358144760115846184960000000000 false
private noncomputable def ibox559 : Fin 4 → FixedTape.I := splitI ibox557 0 8968843611336956394109772358144760115846184960000000000 true
private noncomputable def ibox560 : Fin 4 → FixedTape.I := splitI ibox556 3 12431616634123028271385806917078617936499834880000000000000 true
private noncomputable def ibox561 : Fin 4 → FixedTape.I := splitI ibox560 0 8968843611336956394109772358144760115846184960000000000 false
private noncomputable def ibox562 : Fin 4 → FixedTape.I := splitI ibox560 0 8968843611336956394109772358144760115846184960000000000 true
private noncomputable def ibox563 : Fin 4 → FixedTape.I := splitI ibox555 0 9151881236058118769499767712392612363108352000000000000 true
private noncomputable def ibox564 : Fin 4 → FixedTape.I := splitI ibox563 3 12431616634123028271385806917078617936499834880000000000000 false
private noncomputable def ibox565 : Fin 4 → FixedTape.I := splitI ibox564 0 9334918860779281144889763066640464610370519040000000000 false
private noncomputable def ibox566 : Fin 4 → FixedTape.I := splitI ibox564 0 9334918860779281144889763066640464610370519040000000000 true
private noncomputable def ibox567 : Fin 4 → FixedTape.I := splitI ibox563 3 12431616634123028271385806917078617936499834880000000000000 true
private noncomputable def ibox568 : Fin 4 → FixedTape.I := splitI ibox567 0 9334918860779281144889763066640464610370519040000000000 false
private noncomputable def ibox569 : Fin 4 → FixedTape.I := splitI ibox567 0 9334918860779281144889763066640464610370519040000000000 true
private noncomputable def ibox570 : Fin 4 → FixedTape.I := splitI ibox554 3 13387894836747876599953945910700050085461360640000000000000 true
private noncomputable def ibox571 : Fin 4 → FixedTape.I := splitI ibox570 0 9151881236058118769499767712392612363108352000000000000 false
private noncomputable def ibox572 : Fin 4 → FixedTape.I := splitI ibox571 3 14344173039372724928522084904321482234422886400000000000000 false
private noncomputable def ibox573 : Fin 4 → FixedTape.I := splitI ibox572 0 8968843611336956394109772358144760115846184960000000000 false
private noncomputable def ibox574 : Fin 4 → FixedTape.I := splitI ibox572 0 8968843611336956394109772358144760115846184960000000000 true
private noncomputable def ibox575 : Fin 4 → FixedTape.I := splitI ibox571 3 14344173039372724928522084904321482234422886400000000000000 true
private noncomputable def ibox576 : Fin 4 → FixedTape.I := splitI ibox575 0 8968843611336956394109772358144760115846184960000000000 false
private noncomputable def ibox577 : Fin 4 → FixedTape.I := splitI ibox575 0 8968843611336956394109772358144760115846184960000000000 true
private noncomputable def ibox578 : Fin 4 → FixedTape.I := splitI ibox570 0 9151881236058118769499767712392612363108352000000000000 true
private noncomputable def ibox579 : Fin 4 → FixedTape.I := splitI ibox578 3 14344173039372724928522084904321482234422886400000000000000 false
private noncomputable def ibox580 : Fin 4 → FixedTape.I := splitI ibox579 0 9334918860779281144889763066640464610370519040000000000 false
private noncomputable def ibox581 : Fin 4 → FixedTape.I := splitI ibox579 0 9334918860779281144889763066640464610370519040000000000 true
private noncomputable def ibox582 : Fin 4 → FixedTape.I := splitI ibox578 3 14344173039372724928522084904321482234422886400000000000000 true
private noncomputable def ibox583 : Fin 4 → FixedTape.I := splitI ibox582 0 9334918860779281144889763066640464610370519040000000000 false
private noncomputable def ibox584 : Fin 4 → FixedTape.I := splitI ibox582 0 9334918860779281144889763066640464610370519040000000000 true
private noncomputable def ibox585 : Fin 4 → FixedTape.I := splitI ibox456 0 9517956485500443520279758420888316857632686080000000000 true
private noncomputable def ibox586 : Fin 4 → FixedTape.I := faceI ibox585 1 false
private noncomputable def ibox587 : Fin 4 → FixedTape.I := splitI ibox586 3 7650225620998786628545111948971457191692206080000000000000 false
private noncomputable def ibox588 : Fin 4 → FixedTape.I := splitI ibox587 3 3825112810499393314272555974485728595846103040000000000000 false
private noncomputable def ibox589 : Fin 4 → FixedTape.I := splitI ibox588 0 9884031734942768271059749129384021352157020160000000000 false
private noncomputable def ibox590 : Fin 4 → FixedTape.I := splitI ibox589 3 1912556405249696657136277987242864297923051520000000000000 false
private noncomputable def ibox591 : Fin 4 → FixedTape.I := splitI ibox590 0 9700994110221605895669753775136169104894853120000000000 false
private noncomputable def ibox592 : Fin 4 → FixedTape.I := splitI ibox591 3 956278202624848328568138993621432148961525760000000000000 false
private noncomputable def ibox593 : Fin 4 → FixedTape.I := splitI ibox591 3 956278202624848328568138993621432148961525760000000000000 true
private noncomputable def ibox594 : Fin 4 → FixedTape.I := splitI ibox590 0 9700994110221605895669753775136169104894853120000000000 true
private noncomputable def ibox595 : Fin 4 → FixedTape.I := splitI ibox594 3 956278202624848328568138993621432148961525760000000000000 false
private noncomputable def ibox596 : Fin 4 → FixedTape.I := splitI ibox594 3 956278202624848328568138993621432148961525760000000000000 true
private noncomputable def ibox597 : Fin 4 → FixedTape.I := splitI ibox589 3 1912556405249696657136277987242864297923051520000000000000 true
private noncomputable def ibox598 : Fin 4 → FixedTape.I := splitI ibox597 0 9700994110221605895669753775136169104894853120000000000 false
private noncomputable def ibox599 : Fin 4 → FixedTape.I := splitI ibox598 3 2868834607874544985704416980864296446884577280000000000000 false
private noncomputable def ibox600 : Fin 4 → FixedTape.I := splitI ibox598 3 2868834607874544985704416980864296446884577280000000000000 true
private noncomputable def ibox601 : Fin 4 → FixedTape.I := splitI ibox597 0 9700994110221605895669753775136169104894853120000000000 true
private noncomputable def ibox602 : Fin 4 → FixedTape.I := splitI ibox601 3 2868834607874544985704416980864296446884577280000000000000 false
private noncomputable def ibox603 : Fin 4 → FixedTape.I := splitI ibox601 3 2868834607874544985704416980864296446884577280000000000000 true
private noncomputable def ibox604 : Fin 4 → FixedTape.I := splitI ibox588 0 9884031734942768271059749129384021352157020160000000000 true
private noncomputable def ibox605 : Fin 4 → FixedTape.I := splitI ibox604 3 1912556405249696657136277987242864297923051520000000000000 false
private noncomputable def ibox606 : Fin 4 → FixedTape.I := splitI ibox605 0 10067069359663930646449744483631873599419187200000000000 false
private noncomputable def ibox607 : Fin 4 → FixedTape.I := splitI ibox606 3 956278202624848328568138993621432148961525760000000000000 false
private noncomputable def ibox608 : Fin 4 → FixedTape.I := splitI ibox606 3 956278202624848328568138993621432148961525760000000000000 true
private noncomputable def ibox609 : Fin 4 → FixedTape.I := splitI ibox605 0 10067069359663930646449744483631873599419187200000000000 true
private noncomputable def ibox610 : Fin 4 → FixedTape.I := splitI ibox609 3 956278202624848328568138993621432148961525760000000000000 false
private noncomputable def ibox611 : Fin 4 → FixedTape.I := splitI ibox609 3 956278202624848328568138993621432148961525760000000000000 true
private noncomputable def ibox612 : Fin 4 → FixedTape.I := splitI ibox604 3 1912556405249696657136277987242864297923051520000000000000 true
private noncomputable def ibox613 : Fin 4 → FixedTape.I := splitI ibox612 0 10067069359663930646449744483631873599419187200000000000 false
private noncomputable def ibox614 : Fin 4 → FixedTape.I := splitI ibox613 3 2868834607874544985704416980864296446884577280000000000000 false
private noncomputable def ibox615 : Fin 4 → FixedTape.I := splitI ibox613 3 2868834607874544985704416980864296446884577280000000000000 true
private noncomputable def ibox616 : Fin 4 → FixedTape.I := splitI ibox612 0 10067069359663930646449744483631873599419187200000000000 true
private noncomputable def ibox617 : Fin 4 → FixedTape.I := splitI ibox616 3 2868834607874544985704416980864296446884577280000000000000 false
private noncomputable def ibox618 : Fin 4 → FixedTape.I := splitI ibox616 3 2868834607874544985704416980864296446884577280000000000000 true
private noncomputable def ibox619 : Fin 4 → FixedTape.I := splitI ibox587 3 3825112810499393314272555974485728595846103040000000000000 true
private noncomputable def ibox620 : Fin 4 → FixedTape.I := splitI ibox619 0 9884031734942768271059749129384021352157020160000000000 false
private noncomputable def ibox621 : Fin 4 → FixedTape.I := splitI ibox620 3 5737669215749089971408833961728592893769154560000000000000 false
private noncomputable def ibox622 : Fin 4 → FixedTape.I := splitI ibox621 0 9700994110221605895669753775136169104894853120000000000 false
private noncomputable def ibox623 : Fin 4 → FixedTape.I := splitI ibox622 3 4781391013124241642840694968107160744807628800000000000000 false
private noncomputable def ibox624 : Fin 4 → FixedTape.I := splitI ibox622 3 4781391013124241642840694968107160744807628800000000000000 true
private noncomputable def ibox625 : Fin 4 → FixedTape.I := splitI ibox621 0 9700994110221605895669753775136169104894853120000000000 true
private noncomputable def ibox626 : Fin 4 → FixedTape.I := splitI ibox625 3 4781391013124241642840694968107160744807628800000000000000 false
private noncomputable def ibox627 : Fin 4 → FixedTape.I := splitI ibox625 3 4781391013124241642840694968107160744807628800000000000000 true
private noncomputable def ibox628 : Fin 4 → FixedTape.I := splitI ibox620 3 5737669215749089971408833961728592893769154560000000000000 true
private noncomputable def ibox629 : Fin 4 → FixedTape.I := splitI ibox628 0 9700994110221605895669753775136169104894853120000000000 false
private noncomputable def ibox630 : Fin 4 → FixedTape.I := splitI ibox629 3 6693947418373938299976972955350025042730680320000000000000 false
private noncomputable def ibox631 : Fin 4 → FixedTape.I := splitI ibox629 3 6693947418373938299976972955350025042730680320000000000000 true
private noncomputable def ibox632 : Fin 4 → FixedTape.I := splitI ibox628 0 9700994110221605895669753775136169104894853120000000000 true
private noncomputable def ibox633 : Fin 4 → FixedTape.I := splitI ibox632 3 6693947418373938299976972955350025042730680320000000000000 false
private noncomputable def ibox634 : Fin 4 → FixedTape.I := splitI ibox632 3 6693947418373938299976972955350025042730680320000000000000 true
private noncomputable def ibox635 : Fin 4 → FixedTape.I := splitI ibox619 0 9884031734942768271059749129384021352157020160000000000 true
private noncomputable def ibox636 : Fin 4 → FixedTape.I := splitI ibox635 3 5737669215749089971408833961728592893769154560000000000000 false
private noncomputable def ibox637 : Fin 4 → FixedTape.I := splitI ibox636 0 10067069359663930646449744483631873599419187200000000000 false
private noncomputable def ibox638 : Fin 4 → FixedTape.I := splitI ibox637 3 4781391013124241642840694968107160744807628800000000000000 false
private noncomputable def ibox639 : Fin 4 → FixedTape.I := splitI ibox637 3 4781391013124241642840694968107160744807628800000000000000 true
private noncomputable def ibox640 : Fin 4 → FixedTape.I := splitI ibox636 0 10067069359663930646449744483631873599419187200000000000 true
private noncomputable def ibox641 : Fin 4 → FixedTape.I := splitI ibox640 3 4781391013124241642840694968107160744807628800000000000000 false
private noncomputable def ibox642 : Fin 4 → FixedTape.I := splitI ibox640 3 4781391013124241642840694968107160744807628800000000000000 true
private noncomputable def ibox643 : Fin 4 → FixedTape.I := splitI ibox635 3 5737669215749089971408833961728592893769154560000000000000 true
private noncomputable def ibox644 : Fin 4 → FixedTape.I := splitI ibox643 0 10067069359663930646449744483631873599419187200000000000 false
private noncomputable def ibox645 : Fin 4 → FixedTape.I := splitI ibox644 3 6693947418373938299976972955350025042730680320000000000000 false
private noncomputable def ibox646 : Fin 4 → FixedTape.I := splitI ibox644 3 6693947418373938299976972955350025042730680320000000000000 true
private noncomputable def ibox647 : Fin 4 → FixedTape.I := splitI ibox643 0 10067069359663930646449744483631873599419187200000000000 true
private noncomputable def ibox648 : Fin 4 → FixedTape.I := splitI ibox647 3 6693947418373938299976972955350025042730680320000000000000 false
private noncomputable def ibox649 : Fin 4 → FixedTape.I := splitI ibox647 3 6693947418373938299976972955350025042730680320000000000000 true
private noncomputable def ibox650 : Fin 4 → FixedTape.I := splitI ibox586 3 7650225620998786628545111948971457191692206080000000000000 true
private noncomputable def ibox651 : Fin 4 → FixedTape.I := splitI ibox650 3 11475338431498179942817667923457185787538309120000000000000 false
private noncomputable def ibox652 : Fin 4 → FixedTape.I := splitI ibox651 0 9884031734942768271059749129384021352157020160000000000 false
private noncomputable def ibox653 : Fin 4 → FixedTape.I := splitI ibox652 3 9562782026248483285681389936214321489615257600000000000000 false
private noncomputable def ibox654 : Fin 4 → FixedTape.I := splitI ibox653 0 9700994110221605895669753775136169104894853120000000000 false
private noncomputable def ibox655 : Fin 4 → FixedTape.I := splitI ibox654 3 8606503823623634957113250942592889340653731840000000000000 false
private noncomputable def ibox656 : Fin 4 → FixedTape.I := splitI ibox654 3 8606503823623634957113250942592889340653731840000000000000 true
private noncomputable def ibox657 : Fin 4 → FixedTape.I := splitI ibox653 0 9700994110221605895669753775136169104894853120000000000 true
private noncomputable def ibox658 : Fin 4 → FixedTape.I := splitI ibox657 3 8606503823623634957113250942592889340653731840000000000000 false
private noncomputable def ibox659 : Fin 4 → FixedTape.I := splitI ibox657 3 8606503823623634957113250942592889340653731840000000000000 true
private noncomputable def ibox660 : Fin 4 → FixedTape.I := splitI ibox652 3 9562782026248483285681389936214321489615257600000000000000 true
private noncomputable def ibox661 : Fin 4 → FixedTape.I := splitI ibox660 0 9700994110221605895669753775136169104894853120000000000 false
private noncomputable def ibox662 : Fin 4 → FixedTape.I := splitI ibox661 3 10519060228873331614249528929835753638576783360000000000000 false
private noncomputable def ibox663 : Fin 4 → FixedTape.I := splitI ibox661 3 10519060228873331614249528929835753638576783360000000000000 true
private noncomputable def ibox664 : Fin 4 → FixedTape.I := splitI ibox660 0 9700994110221605895669753775136169104894853120000000000 true
private noncomputable def ibox665 : Fin 4 → FixedTape.I := splitI ibox664 3 10519060228873331614249528929835753638576783360000000000000 false
private noncomputable def ibox666 : Fin 4 → FixedTape.I := splitI ibox664 3 10519060228873331614249528929835753638576783360000000000000 true
private noncomputable def ibox667 : Fin 4 → FixedTape.I := splitI ibox651 0 9884031734942768271059749129384021352157020160000000000 true
private noncomputable def ibox668 : Fin 4 → FixedTape.I := splitI ibox667 3 9562782026248483285681389936214321489615257600000000000000 false
private noncomputable def ibox669 : Fin 4 → FixedTape.I := splitI ibox668 0 10067069359663930646449744483631873599419187200000000000 false
private noncomputable def ibox670 : Fin 4 → FixedTape.I := splitI ibox669 3 8606503823623634957113250942592889340653731840000000000000 false
private noncomputable def ibox671 : Fin 4 → FixedTape.I := splitI ibox669 3 8606503823623634957113250942592889340653731840000000000000 true
private noncomputable def ibox672 : Fin 4 → FixedTape.I := splitI ibox668 0 10067069359663930646449744483631873599419187200000000000 true
private noncomputable def ibox673 : Fin 4 → FixedTape.I := splitI ibox672 3 8606503823623634957113250942592889340653731840000000000000 false
private noncomputable def ibox674 : Fin 4 → FixedTape.I := splitI ibox672 3 8606503823623634957113250942592889340653731840000000000000 true
private noncomputable def ibox675 : Fin 4 → FixedTape.I := splitI ibox667 3 9562782026248483285681389936214321489615257600000000000000 true
private noncomputable def ibox676 : Fin 4 → FixedTape.I := splitI ibox675 0 10067069359663930646449744483631873599419187200000000000 false
private noncomputable def ibox677 : Fin 4 → FixedTape.I := splitI ibox676 3 10519060228873331614249528929835753638576783360000000000000 false
private noncomputable def ibox678 : Fin 4 → FixedTape.I := splitI ibox676 3 10519060228873331614249528929835753638576783360000000000000 true
private noncomputable def ibox679 : Fin 4 → FixedTape.I := splitI ibox675 0 10067069359663930646449744483631873599419187200000000000 true
private noncomputable def ibox680 : Fin 4 → FixedTape.I := splitI ibox679 3 10519060228873331614249528929835753638576783360000000000000 false
private noncomputable def ibox681 : Fin 4 → FixedTape.I := splitI ibox679 3 10519060228873331614249528929835753638576783360000000000000 true
private noncomputable def ibox682 : Fin 4 → FixedTape.I := splitI ibox650 3 11475338431498179942817667923457185787538309120000000000000 true
private noncomputable def ibox683 : Fin 4 → FixedTape.I := splitI ibox682 3 13387894836747876599953945910700050085461360640000000000000 false
private noncomputable def ibox684 : Fin 4 → FixedTape.I := splitI ibox683 0 9884031734942768271059749129384021352157020160000000000 false
private noncomputable def ibox685 : Fin 4 → FixedTape.I := splitI ibox684 3 12431616634123028271385806917078617936499834880000000000000 false
private noncomputable def ibox686 : Fin 4 → FixedTape.I := splitI ibox685 0 9700994110221605895669753775136169104894853120000000000 false
private noncomputable def ibox687 : Fin 4 → FixedTape.I := splitI ibox685 0 9700994110221605895669753775136169104894853120000000000 true
private noncomputable def ibox688 : Fin 4 → FixedTape.I := splitI ibox684 3 12431616634123028271385806917078617936499834880000000000000 true
private noncomputable def ibox689 : Fin 4 → FixedTape.I := splitI ibox688 0 9700994110221605895669753775136169104894853120000000000 false
private noncomputable def ibox690 : Fin 4 → FixedTape.I := splitI ibox688 0 9700994110221605895669753775136169104894853120000000000 true
private noncomputable def ibox691 : Fin 4 → FixedTape.I := splitI ibox683 0 9884031734942768271059749129384021352157020160000000000 true
private noncomputable def ibox692 : Fin 4 → FixedTape.I := splitI ibox691 3 12431616634123028271385806917078617936499834880000000000000 false
private noncomputable def ibox693 : Fin 4 → FixedTape.I := splitI ibox692 0 10067069359663930646449744483631873599419187200000000000 false
private noncomputable def ibox694 : Fin 4 → FixedTape.I := splitI ibox692 0 10067069359663930646449744483631873599419187200000000000 true
private noncomputable def ibox695 : Fin 4 → FixedTape.I := splitI ibox691 3 12431616634123028271385806917078617936499834880000000000000 true
private noncomputable def ibox696 : Fin 4 → FixedTape.I := splitI ibox695 0 10067069359663930646449744483631873599419187200000000000 false
private noncomputable def ibox697 : Fin 4 → FixedTape.I := splitI ibox695 0 10067069359663930646449744483631873599419187200000000000 true
private noncomputable def ibox698 : Fin 4 → FixedTape.I := splitI ibox682 3 13387894836747876599953945910700050085461360640000000000000 true
private noncomputable def ibox699 : Fin 4 → FixedTape.I := splitI ibox698 0 9884031734942768271059749129384021352157020160000000000 false
private noncomputable def ibox700 : Fin 4 → FixedTape.I := splitI ibox699 3 14344173039372724928522084904321482234422886400000000000000 false
private noncomputable def ibox701 : Fin 4 → FixedTape.I := splitI ibox700 0 9700994110221605895669753775136169104894853120000000000 false
private noncomputable def ibox702 : Fin 4 → FixedTape.I := splitI ibox700 0 9700994110221605895669753775136169104894853120000000000 true
private noncomputable def ibox703 : Fin 4 → FixedTape.I := splitI ibox699 3 14344173039372724928522084904321482234422886400000000000000 true
private noncomputable def ibox704 : Fin 4 → FixedTape.I := splitI ibox703 0 9700994110221605895669753775136169104894853120000000000 false
private noncomputable def ibox705 : Fin 4 → FixedTape.I := splitI ibox703 0 9700994110221605895669753775136169104894853120000000000 true
private noncomputable def ibox706 : Fin 4 → FixedTape.I := splitI ibox698 0 9884031734942768271059749129384021352157020160000000000 true
private noncomputable def ibox707 : Fin 4 → FixedTape.I := splitI ibox706 3 14344173039372724928522084904321482234422886400000000000000 false
private noncomputable def ibox708 : Fin 4 → FixedTape.I := splitI ibox707 0 10067069359663930646449744483631873599419187200000000000 false
private noncomputable def ibox709 : Fin 4 → FixedTape.I := splitI ibox707 0 10067069359663930646449744483631873599419187200000000000 true
private noncomputable def ibox710 : Fin 4 → FixedTape.I := splitI ibox706 3 14344173039372724928522084904321482234422886400000000000000 true
private noncomputable def ibox711 : Fin 4 → FixedTape.I := splitI ibox710 0 10067069359663930646449744483631873599419187200000000000 false
private noncomputable def ibox712 : Fin 4 → FixedTape.I := splitI ibox710 0 10067069359663930646449744483631873599419187200000000000 true
private noncomputable def ibox713 : Fin 4 → FixedTape.I := splitI ibox455 1 1912556405249696657136277987242864297923051520000000000000 true
private noncomputable def ibox714 : Fin 4 → FixedTape.I := splitI ibox713 0 9517956485500443520279758420888316857632686080000000000 false
private noncomputable def ibox715 : Fin 4 → FixedTape.I := faceI ibox714 1 false
private noncomputable def ibox716 : Fin 4 → FixedTape.I := splitI ibox715 3 7650225620998786628545111948971457191692206080000000000000 false
private noncomputable def ibox717 : Fin 4 → FixedTape.I := splitI ibox715 3 7650225620998786628545111948971457191692206080000000000000 true
private noncomputable def ibox718 : Fin 4 → FixedTape.I := splitI ibox713 0 9517956485500443520279758420888316857632686080000000000 true
private noncomputable def ibox719 : Fin 4 → FixedTape.I := faceI ibox718 1 false
private noncomputable def ibox720 : Fin 4 → FixedTape.I := splitI ibox719 3 7650225620998786628545111948971457191692206080000000000000 false
private noncomputable def ibox721 : Fin 4 → FixedTape.I := splitI ibox719 3 7650225620998786628545111948971457191692206080000000000000 true
private noncomputable def ibox722 : Fin 4 → FixedTape.I := splitI ibox454 1 3825112810499393314272555974485728595846103040000000000000 true
private noncomputable def ibox723 : Fin 4 → FixedTape.I := splitI ibox722 0 9517956485500443520279758420888316857632686080000000000 false
private noncomputable def ibox724 : Fin 4 → FixedTape.I := faceI ibox723 1 false
private noncomputable def ibox725 : Fin 4 → FixedTape.I := splitI ibox722 0 9517956485500443520279758420888316857632686080000000000 true
private noncomputable def ibox726 : Fin 4 → FixedTape.I := faceI ibox725 1 false
private noncomputable def ibox727 : Fin 4 → FixedTape.I := splitI ibox452 1 7650225620998786628545111948971457191692206080000000000000 true
private noncomputable def ibox728 : Fin 4 → FixedTape.I := faceI ibox727 3 false
private noncomputable def ibox729 : Fin 4 → FixedTape.I := splitI ibox728 0 9517956485500443520279758420888316857632686080000000000 false
private noncomputable def ibox730 : Fin 4 → FixedTape.I := splitI ibox729 1 11475338431498179942817667923457185787538309120000000000000 false
private noncomputable def ibox731 : Fin 4 → FixedTape.I := splitI ibox729 1 11475338431498179942817667923457185787538309120000000000000 true
private noncomputable def ibox732 : Fin 4 → FixedTape.I := splitI ibox728 0 9517956485500443520279758420888316857632686080000000000 true
private noncomputable def ibox733 : Fin 4 → FixedTape.I := splitI ibox732 1 11475338431498179942817667923457185787538309120000000000000 false
private noncomputable def ibox734 : Fin 4 → FixedTape.I := splitI ibox732 1 11475338431498179942817667923457185787538309120000000000000 true
private noncomputable def tree734 : TapeTree := .centered (candidateRows ibox734) (candidateRows (FixedTape.midBox ibox734))
attribute [irreducible] tree734
private theorem sign_734 : 2*denominator*(computed denominator (FixedTape.midBox ibox734)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox734).gradient k).lo.natAbs ((computed denominator ibox734).gradient k).hi.natAbs : Int)*((ibox734 k).hi-(ibox734 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox734
    (computed denominator ibox734) (computed denominator (FixedTape.midBox ibox734))
    (by decide +kernel)
private theorem midpoint_even_734 : ∀ k, 2 ∣ (ibox734 k).lo+(ibox734 k).hi := by decide +kernel
private theorem accepted_734 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox734) tree734 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox734 midpoint_even_734
  simp only [tree734,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox734,candidate_valid h (FixedTape.midBox ibox734),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox734 212 (FixedTape.rowsAux denominator ibox734 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox734) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_734
private noncomputable def tree733 : TapeTree := .centered (candidateRows ibox733) (candidateRows (FixedTape.midBox ibox733))
attribute [irreducible] tree733
private theorem sign_733 : 2*denominator*(computed denominator (FixedTape.midBox ibox733)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox733).gradient k).lo.natAbs ((computed denominator ibox733).gradient k).hi.natAbs : Int)*((ibox733 k).hi-(ibox733 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox733
    (computed denominator ibox733) (computed denominator (FixedTape.midBox ibox733))
    (by decide +kernel)
private theorem midpoint_even_733 : ∀ k, 2 ∣ (ibox733 k).lo+(ibox733 k).hi := by decide +kernel
private theorem accepted_733 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox733) tree733 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox733 midpoint_even_733
  simp only [tree733,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox733,candidate_valid h (FixedTape.midBox ibox733),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox733 212 (FixedTape.rowsAux denominator ibox733 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox733) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_733
private noncomputable def tree732 : TapeTree := .split 1 (((11475338431498179942817667923457185787538309120000000000000 : Int) : ℚ)/(denominator : ℚ)) tree733 tree734
attribute [irreducible] tree732
private theorem accepted_732 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox732) tree732 = true := by
  simp only [tree732,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox732 1 (11475338431498179942817667923457185787538309120000000000000 : Int) false,decode_split denominator ibox732 1 (11475338431498179942817667923457185787538309120000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_733 h,accepted_734 h⟩
private noncomputable def tree731 : TapeTree := .centered (candidateRows ibox731) (candidateRows (FixedTape.midBox ibox731))
attribute [irreducible] tree731
private theorem sign_731 : 2*denominator*(computed denominator (FixedTape.midBox ibox731)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox731).gradient k).lo.natAbs ((computed denominator ibox731).gradient k).hi.natAbs : Int)*((ibox731 k).hi-(ibox731 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox731
    (computed denominator ibox731) (computed denominator (FixedTape.midBox ibox731))
    (by decide +kernel)
private theorem midpoint_even_731 : ∀ k, 2 ∣ (ibox731 k).lo+(ibox731 k).hi := by decide +kernel
private theorem accepted_731 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox731) tree731 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox731 midpoint_even_731
  simp only [tree731,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox731,candidate_valid h (FixedTape.midBox ibox731),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox731 212 (FixedTape.rowsAux denominator ibox731 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox731) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_731
private noncomputable def tree730 : TapeTree := .centered (candidateRows ibox730) (candidateRows (FixedTape.midBox ibox730))
attribute [irreducible] tree730
private theorem sign_730 : 2*denominator*(computed denominator (FixedTape.midBox ibox730)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox730).gradient k).lo.natAbs ((computed denominator ibox730).gradient k).hi.natAbs : Int)*((ibox730 k).hi-(ibox730 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox730
    (computed denominator ibox730) (computed denominator (FixedTape.midBox ibox730))
    (by decide +kernel)
private theorem midpoint_even_730 : ∀ k, 2 ∣ (ibox730 k).lo+(ibox730 k).hi := by decide +kernel
private theorem accepted_730 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox730) tree730 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox730 midpoint_even_730
  simp only [tree730,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox730,candidate_valid h (FixedTape.midBox ibox730),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox730 212 (FixedTape.rowsAux denominator ibox730 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox730) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_730
private noncomputable def tree729 : TapeTree := .split 1 (((11475338431498179942817667923457185787538309120000000000000 : Int) : ℚ)/(denominator : ℚ)) tree730 tree731
attribute [irreducible] tree729
private theorem accepted_729 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox729) tree729 = true := by
  simp only [tree729,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox729 1 (11475338431498179942817667923457185787538309120000000000000 : Int) false,decode_split denominator ibox729 1 (11475338431498179942817667923457185787538309120000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_730 h,accepted_731 h⟩
private noncomputable def tree728 : TapeTree := .split 0 (((9517956485500443520279758420888316857632686080000000000 : Int) : ℚ)/(denominator : ℚ)) tree729 tree732
attribute [irreducible] tree728
private theorem accepted_728 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox728) tree728 = true := by
  simp only [tree728,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox728 0 (9517956485500443520279758420888316857632686080000000000 : Int) false,decode_split denominator ibox728 0 (9517956485500443520279758420888316857632686080000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_729 h,accepted_732 h⟩
private noncomputable def tree727 : TapeTree := .face 3 false (candidateRows ibox727) tree728
attribute [irreducible] tree727
private theorem sign_727 : ((computed denominator ibox727).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_727 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox727) tree727 = true := by
  simp only [tree727,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox727,?_,accepted_728 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox727)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox727).gradient 3).hi) denominator_positive).1 sign_727
private noncomputable def tree726 : TapeTree := .centered (candidateRows ibox726) (candidateRows (FixedTape.midBox ibox726))
attribute [irreducible] tree726
private theorem sign_726 : 2*denominator*(computed denominator (FixedTape.midBox ibox726)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox726).gradient k).lo.natAbs ((computed denominator ibox726).gradient k).hi.natAbs : Int)*((ibox726 k).hi-(ibox726 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox726
    (computed denominator ibox726) (computed denominator (FixedTape.midBox ibox726))
    (by decide +kernel)
private theorem midpoint_even_726 : ∀ k, 2 ∣ (ibox726 k).lo+(ibox726 k).hi := by decide +kernel
private theorem accepted_726 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox726) tree726 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox726 midpoint_even_726
  simp only [tree726,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox726,candidate_valid h (FixedTape.midBox ibox726),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox726 212 (FixedTape.rowsAux denominator ibox726 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox726) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_726
private noncomputable def tree725 : TapeTree := .face 1 false (candidateRows ibox725) tree726
attribute [irreducible] tree725
private theorem sign_725 : ((computed denominator ibox725).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_725 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox725) tree725 = true := by
  simp only [tree725,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox725,?_,accepted_726 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox725)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox725).gradient 1).hi) denominator_positive).1 sign_725
private noncomputable def tree724 : TapeTree := .centered (candidateRows ibox724) (candidateRows (FixedTape.midBox ibox724))
attribute [irreducible] tree724
private theorem sign_724 : 2*denominator*(computed denominator (FixedTape.midBox ibox724)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox724).gradient k).lo.natAbs ((computed denominator ibox724).gradient k).hi.natAbs : Int)*((ibox724 k).hi-(ibox724 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox724
    (computed denominator ibox724) (computed denominator (FixedTape.midBox ibox724))
    (by decide +kernel)
private theorem midpoint_even_724 : ∀ k, 2 ∣ (ibox724 k).lo+(ibox724 k).hi := by decide +kernel
private theorem accepted_724 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox724) tree724 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox724 midpoint_even_724
  simp only [tree724,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox724,candidate_valid h (FixedTape.midBox ibox724),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox724 212 (FixedTape.rowsAux denominator ibox724 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox724) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_724
private noncomputable def tree723 : TapeTree := .face 1 false (candidateRows ibox723) tree724
attribute [irreducible] tree723
private theorem sign_723 : ((computed denominator ibox723).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_723 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox723) tree723 = true := by
  simp only [tree723,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox723,?_,accepted_724 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox723)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox723).gradient 1).hi) denominator_positive).1 sign_723
private noncomputable def tree722 : TapeTree := .split 0 (((9517956485500443520279758420888316857632686080000000000 : Int) : ℚ)/(denominator : ℚ)) tree723 tree725
attribute [irreducible] tree722
private theorem accepted_722 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox722) tree722 = true := by
  simp only [tree722,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox722 0 (9517956485500443520279758420888316857632686080000000000 : Int) false,decode_split denominator ibox722 0 (9517956485500443520279758420888316857632686080000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_723 h,accepted_725 h⟩
private noncomputable def tree721 : TapeTree := .centered (candidateRows ibox721) (candidateRows (FixedTape.midBox ibox721))
attribute [irreducible] tree721
private theorem sign_721 : 2*denominator*(computed denominator (FixedTape.midBox ibox721)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox721).gradient k).lo.natAbs ((computed denominator ibox721).gradient k).hi.natAbs : Int)*((ibox721 k).hi-(ibox721 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox721
    (computed denominator ibox721) (computed denominator (FixedTape.midBox ibox721))
    (by decide +kernel)
private theorem midpoint_even_721 : ∀ k, 2 ∣ (ibox721 k).lo+(ibox721 k).hi := by decide +kernel
private theorem accepted_721 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox721) tree721 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox721 midpoint_even_721
  simp only [tree721,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox721,candidate_valid h (FixedTape.midBox ibox721),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox721 212 (FixedTape.rowsAux denominator ibox721 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox721) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_721
private noncomputable def tree720 : TapeTree := .centered (candidateRows ibox720) (candidateRows (FixedTape.midBox ibox720))
attribute [irreducible] tree720
private theorem sign_720 : 2*denominator*(computed denominator (FixedTape.midBox ibox720)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox720).gradient k).lo.natAbs ((computed denominator ibox720).gradient k).hi.natAbs : Int)*((ibox720 k).hi-(ibox720 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox720
    (computed denominator ibox720) (computed denominator (FixedTape.midBox ibox720))
    (by decide +kernel)
private theorem midpoint_even_720 : ∀ k, 2 ∣ (ibox720 k).lo+(ibox720 k).hi := by decide +kernel
private theorem accepted_720 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox720) tree720 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox720 midpoint_even_720
  simp only [tree720,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox720,candidate_valid h (FixedTape.midBox ibox720),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox720 212 (FixedTape.rowsAux denominator ibox720 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox720) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_720
private noncomputable def tree719 : TapeTree := .split 3 (((7650225620998786628545111948971457191692206080000000000000 : Int) : ℚ)/(denominator : ℚ)) tree720 tree721
attribute [irreducible] tree719
private theorem accepted_719 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox719) tree719 = true := by
  simp only [tree719,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox719 3 (7650225620998786628545111948971457191692206080000000000000 : Int) false,decode_split denominator ibox719 3 (7650225620998786628545111948971457191692206080000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_720 h,accepted_721 h⟩
private noncomputable def tree718 : TapeTree := .face 1 false (candidateRows ibox718) tree719
attribute [irreducible] tree718
private theorem sign_718 : ((computed denominator ibox718).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_718 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox718) tree718 = true := by
  simp only [tree718,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox718,?_,accepted_719 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox718)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox718).gradient 1).hi) denominator_positive).1 sign_718
private noncomputable def tree717 : TapeTree := .centered (candidateRows ibox717) (candidateRows (FixedTape.midBox ibox717))
attribute [irreducible] tree717
private theorem sign_717 : 2*denominator*(computed denominator (FixedTape.midBox ibox717)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox717).gradient k).lo.natAbs ((computed denominator ibox717).gradient k).hi.natAbs : Int)*((ibox717 k).hi-(ibox717 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox717
    (computed denominator ibox717) (computed denominator (FixedTape.midBox ibox717))
    (by decide +kernel)
private theorem midpoint_even_717 : ∀ k, 2 ∣ (ibox717 k).lo+(ibox717 k).hi := by decide +kernel
private theorem accepted_717 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox717) tree717 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox717 midpoint_even_717
  simp only [tree717,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox717,candidate_valid h (FixedTape.midBox ibox717),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox717 212 (FixedTape.rowsAux denominator ibox717 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox717) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_717
private noncomputable def tree716 : TapeTree := .centered (candidateRows ibox716) (candidateRows (FixedTape.midBox ibox716))
attribute [irreducible] tree716
private theorem sign_716 : 2*denominator*(computed denominator (FixedTape.midBox ibox716)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox716).gradient k).lo.natAbs ((computed denominator ibox716).gradient k).hi.natAbs : Int)*((ibox716 k).hi-(ibox716 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox716
    (computed denominator ibox716) (computed denominator (FixedTape.midBox ibox716))
    (by decide +kernel)
private theorem midpoint_even_716 : ∀ k, 2 ∣ (ibox716 k).lo+(ibox716 k).hi := by decide +kernel
private theorem accepted_716 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox716) tree716 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox716 midpoint_even_716
  simp only [tree716,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox716,candidate_valid h (FixedTape.midBox ibox716),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox716 212 (FixedTape.rowsAux denominator ibox716 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox716) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_716
private noncomputable def tree715 : TapeTree := .split 3 (((7650225620998786628545111948971457191692206080000000000000 : Int) : ℚ)/(denominator : ℚ)) tree716 tree717
attribute [irreducible] tree715
private theorem accepted_715 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox715) tree715 = true := by
  simp only [tree715,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox715 3 (7650225620998786628545111948971457191692206080000000000000 : Int) false,decode_split denominator ibox715 3 (7650225620998786628545111948971457191692206080000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_716 h,accepted_717 h⟩
private noncomputable def tree714 : TapeTree := .face 1 false (candidateRows ibox714) tree715
attribute [irreducible] tree714
private theorem sign_714 : ((computed denominator ibox714).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_714 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox714) tree714 = true := by
  simp only [tree714,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox714,?_,accepted_715 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox714)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox714).gradient 1).hi) denominator_positive).1 sign_714
private noncomputable def tree713 : TapeTree := .split 0 (((9517956485500443520279758420888316857632686080000000000 : Int) : ℚ)/(denominator : ℚ)) tree714 tree718
attribute [irreducible] tree713
private theorem accepted_713 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox713) tree713 = true := by
  simp only [tree713,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox713 0 (9517956485500443520279758420888316857632686080000000000 : Int) false,decode_split denominator ibox713 0 (9517956485500443520279758420888316857632686080000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_714 h,accepted_718 h⟩
private noncomputable def tree712 : TapeTree := .centered (candidateRows ibox712) (candidateRows (FixedTape.midBox ibox712))
attribute [irreducible] tree712
private theorem sign_712 : 2*denominator*(computed denominator (FixedTape.midBox ibox712)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox712).gradient k).lo.natAbs ((computed denominator ibox712).gradient k).hi.natAbs : Int)*((ibox712 k).hi-(ibox712 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox712
    (computed denominator ibox712) (computed denominator (FixedTape.midBox ibox712))
    (by decide +kernel)
private theorem midpoint_even_712 : ∀ k, 2 ∣ (ibox712 k).lo+(ibox712 k).hi := by decide +kernel
private theorem accepted_712 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox712) tree712 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox712 midpoint_even_712
  simp only [tree712,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox712,candidate_valid h (FixedTape.midBox ibox712),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox712 212 (FixedTape.rowsAux denominator ibox712 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox712) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_712
private noncomputable def tree711 : TapeTree := .centered (candidateRows ibox711) (candidateRows (FixedTape.midBox ibox711))
attribute [irreducible] tree711
private theorem sign_711 : 2*denominator*(computed denominator (FixedTape.midBox ibox711)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox711).gradient k).lo.natAbs ((computed denominator ibox711).gradient k).hi.natAbs : Int)*((ibox711 k).hi-(ibox711 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox711
    (computed denominator ibox711) (computed denominator (FixedTape.midBox ibox711))
    (by decide +kernel)
private theorem midpoint_even_711 : ∀ k, 2 ∣ (ibox711 k).lo+(ibox711 k).hi := by decide +kernel
private theorem accepted_711 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox711) tree711 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox711 midpoint_even_711
  simp only [tree711,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox711,candidate_valid h (FixedTape.midBox ibox711),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox711 212 (FixedTape.rowsAux denominator ibox711 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox711) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_711
private noncomputable def tree710 : TapeTree := .split 0 (((10067069359663930646449744483631873599419187200000000000 : Int) : ℚ)/(denominator : ℚ)) tree711 tree712
attribute [irreducible] tree710
private theorem accepted_710 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox710) tree710 = true := by
  simp only [tree710,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox710 0 (10067069359663930646449744483631873599419187200000000000 : Int) false,decode_split denominator ibox710 0 (10067069359663930646449744483631873599419187200000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_711 h,accepted_712 h⟩
private noncomputable def tree709 : TapeTree := .centered (candidateRows ibox709) (candidateRows (FixedTape.midBox ibox709))
attribute [irreducible] tree709
private theorem sign_709 : 2*denominator*(computed denominator (FixedTape.midBox ibox709)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox709).gradient k).lo.natAbs ((computed denominator ibox709).gradient k).hi.natAbs : Int)*((ibox709 k).hi-(ibox709 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox709
    (computed denominator ibox709) (computed denominator (FixedTape.midBox ibox709))
    (by decide +kernel)
private theorem midpoint_even_709 : ∀ k, 2 ∣ (ibox709 k).lo+(ibox709 k).hi := by decide +kernel
private theorem accepted_709 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox709) tree709 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox709 midpoint_even_709
  simp only [tree709,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox709,candidate_valid h (FixedTape.midBox ibox709),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox709 212 (FixedTape.rowsAux denominator ibox709 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox709) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_709
private noncomputable def tree708 : TapeTree := .centered (candidateRows ibox708) (candidateRows (FixedTape.midBox ibox708))
attribute [irreducible] tree708
private theorem sign_708 : 2*denominator*(computed denominator (FixedTape.midBox ibox708)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox708).gradient k).lo.natAbs ((computed denominator ibox708).gradient k).hi.natAbs : Int)*((ibox708 k).hi-(ibox708 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox708
    (computed denominator ibox708) (computed denominator (FixedTape.midBox ibox708))
    (by decide +kernel)
private theorem midpoint_even_708 : ∀ k, 2 ∣ (ibox708 k).lo+(ibox708 k).hi := by decide +kernel
private theorem accepted_708 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox708) tree708 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox708 midpoint_even_708
  simp only [tree708,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox708,candidate_valid h (FixedTape.midBox ibox708),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox708 212 (FixedTape.rowsAux denominator ibox708 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox708) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_708
private noncomputable def tree707 : TapeTree := .split 0 (((10067069359663930646449744483631873599419187200000000000 : Int) : ℚ)/(denominator : ℚ)) tree708 tree709
attribute [irreducible] tree707
private theorem accepted_707 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox707) tree707 = true := by
  simp only [tree707,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox707 0 (10067069359663930646449744483631873599419187200000000000 : Int) false,decode_split denominator ibox707 0 (10067069359663930646449744483631873599419187200000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_708 h,accepted_709 h⟩
private noncomputable def tree706 : TapeTree := .split 3 (((14344173039372724928522084904321482234422886400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree707 tree710
attribute [irreducible] tree706
private theorem accepted_706 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox706) tree706 = true := by
  simp only [tree706,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox706 3 (14344173039372724928522084904321482234422886400000000000000 : Int) false,decode_split denominator ibox706 3 (14344173039372724928522084904321482234422886400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_707 h,accepted_710 h⟩
private noncomputable def tree705 : TapeTree := .centered (candidateRows ibox705) (candidateRows (FixedTape.midBox ibox705))
attribute [irreducible] tree705
private theorem sign_705 : 2*denominator*(computed denominator (FixedTape.midBox ibox705)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox705).gradient k).lo.natAbs ((computed denominator ibox705).gradient k).hi.natAbs : Int)*((ibox705 k).hi-(ibox705 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox705
    (computed denominator ibox705) (computed denominator (FixedTape.midBox ibox705))
    (by decide +kernel)
private theorem midpoint_even_705 : ∀ k, 2 ∣ (ibox705 k).lo+(ibox705 k).hi := by decide +kernel
private theorem accepted_705 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox705) tree705 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox705 midpoint_even_705
  simp only [tree705,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox705,candidate_valid h (FixedTape.midBox ibox705),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox705 212 (FixedTape.rowsAux denominator ibox705 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox705) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_705
private noncomputable def tree704 : TapeTree := .centered (candidateRows ibox704) (candidateRows (FixedTape.midBox ibox704))
attribute [irreducible] tree704
private theorem sign_704 : 2*denominator*(computed denominator (FixedTape.midBox ibox704)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox704).gradient k).lo.natAbs ((computed denominator ibox704).gradient k).hi.natAbs : Int)*((ibox704 k).hi-(ibox704 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox704
    (computed denominator ibox704) (computed denominator (FixedTape.midBox ibox704))
    (by decide +kernel)
private theorem midpoint_even_704 : ∀ k, 2 ∣ (ibox704 k).lo+(ibox704 k).hi := by decide +kernel
private theorem accepted_704 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox704) tree704 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox704 midpoint_even_704
  simp only [tree704,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox704,candidate_valid h (FixedTape.midBox ibox704),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox704 212 (FixedTape.rowsAux denominator ibox704 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox704) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_704
private noncomputable def tree703 : TapeTree := .split 0 (((9700994110221605895669753775136169104894853120000000000 : Int) : ℚ)/(denominator : ℚ)) tree704 tree705
attribute [irreducible] tree703
private theorem accepted_703 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox703) tree703 = true := by
  simp only [tree703,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox703 0 (9700994110221605895669753775136169104894853120000000000 : Int) false,decode_split denominator ibox703 0 (9700994110221605895669753775136169104894853120000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_704 h,accepted_705 h⟩
private noncomputable def tree702 : TapeTree := .centered (candidateRows ibox702) (candidateRows (FixedTape.midBox ibox702))
attribute [irreducible] tree702
private theorem sign_702 : 2*denominator*(computed denominator (FixedTape.midBox ibox702)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox702).gradient k).lo.natAbs ((computed denominator ibox702).gradient k).hi.natAbs : Int)*((ibox702 k).hi-(ibox702 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox702
    (computed denominator ibox702) (computed denominator (FixedTape.midBox ibox702))
    (by decide +kernel)
private theorem midpoint_even_702 : ∀ k, 2 ∣ (ibox702 k).lo+(ibox702 k).hi := by decide +kernel
private theorem accepted_702 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox702) tree702 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox702 midpoint_even_702
  simp only [tree702,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox702,candidate_valid h (FixedTape.midBox ibox702),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox702 212 (FixedTape.rowsAux denominator ibox702 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox702) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_702
private noncomputable def tree701 : TapeTree := .centered (candidateRows ibox701) (candidateRows (FixedTape.midBox ibox701))
attribute [irreducible] tree701
private theorem sign_701 : 2*denominator*(computed denominator (FixedTape.midBox ibox701)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox701).gradient k).lo.natAbs ((computed denominator ibox701).gradient k).hi.natAbs : Int)*((ibox701 k).hi-(ibox701 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox701
    (computed denominator ibox701) (computed denominator (FixedTape.midBox ibox701))
    (by decide +kernel)
private theorem midpoint_even_701 : ∀ k, 2 ∣ (ibox701 k).lo+(ibox701 k).hi := by decide +kernel
private theorem accepted_701 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox701) tree701 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox701 midpoint_even_701
  simp only [tree701,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox701,candidate_valid h (FixedTape.midBox ibox701),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox701 212 (FixedTape.rowsAux denominator ibox701 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox701) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_701
private noncomputable def tree700 : TapeTree := .split 0 (((9700994110221605895669753775136169104894853120000000000 : Int) : ℚ)/(denominator : ℚ)) tree701 tree702
attribute [irreducible] tree700
private theorem accepted_700 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox700) tree700 = true := by
  simp only [tree700,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox700 0 (9700994110221605895669753775136169104894853120000000000 : Int) false,decode_split denominator ibox700 0 (9700994110221605895669753775136169104894853120000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_701 h,accepted_702 h⟩
private noncomputable def tree699 : TapeTree := .split 3 (((14344173039372724928522084904321482234422886400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree700 tree703
attribute [irreducible] tree699
private theorem accepted_699 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox699) tree699 = true := by
  simp only [tree699,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox699 3 (14344173039372724928522084904321482234422886400000000000000 : Int) false,decode_split denominator ibox699 3 (14344173039372724928522084904321482234422886400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_700 h,accepted_703 h⟩
private noncomputable def tree698 : TapeTree := .split 0 (((9884031734942768271059749129384021352157020160000000000 : Int) : ℚ)/(denominator : ℚ)) tree699 tree706
attribute [irreducible] tree698
private theorem accepted_698 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox698) tree698 = true := by
  simp only [tree698,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox698 0 (9884031734942768271059749129384021352157020160000000000 : Int) false,decode_split denominator ibox698 0 (9884031734942768271059749129384021352157020160000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_699 h,accepted_706 h⟩
private noncomputable def tree697 : TapeTree := .centered (candidateRows ibox697) (candidateRows (FixedTape.midBox ibox697))
attribute [irreducible] tree697
private theorem sign_697 : 2*denominator*(computed denominator (FixedTape.midBox ibox697)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox697).gradient k).lo.natAbs ((computed denominator ibox697).gradient k).hi.natAbs : Int)*((ibox697 k).hi-(ibox697 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox697
    (computed denominator ibox697) (computed denominator (FixedTape.midBox ibox697))
    (by decide +kernel)
private theorem midpoint_even_697 : ∀ k, 2 ∣ (ibox697 k).lo+(ibox697 k).hi := by decide +kernel
private theorem accepted_697 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox697) tree697 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox697 midpoint_even_697
  simp only [tree697,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox697,candidate_valid h (FixedTape.midBox ibox697),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox697 212 (FixedTape.rowsAux denominator ibox697 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox697) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_697
private noncomputable def tree696 : TapeTree := .centered (candidateRows ibox696) (candidateRows (FixedTape.midBox ibox696))
attribute [irreducible] tree696
private theorem sign_696 : 2*denominator*(computed denominator (FixedTape.midBox ibox696)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox696).gradient k).lo.natAbs ((computed denominator ibox696).gradient k).hi.natAbs : Int)*((ibox696 k).hi-(ibox696 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox696
    (computed denominator ibox696) (computed denominator (FixedTape.midBox ibox696))
    (by decide +kernel)
private theorem midpoint_even_696 : ∀ k, 2 ∣ (ibox696 k).lo+(ibox696 k).hi := by decide +kernel
private theorem accepted_696 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox696) tree696 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox696 midpoint_even_696
  simp only [tree696,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox696,candidate_valid h (FixedTape.midBox ibox696),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox696 212 (FixedTape.rowsAux denominator ibox696 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox696) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_696
private noncomputable def tree695 : TapeTree := .split 0 (((10067069359663930646449744483631873599419187200000000000 : Int) : ℚ)/(denominator : ℚ)) tree696 tree697
attribute [irreducible] tree695
private theorem accepted_695 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox695) tree695 = true := by
  simp only [tree695,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox695 0 (10067069359663930646449744483631873599419187200000000000 : Int) false,decode_split denominator ibox695 0 (10067069359663930646449744483631873599419187200000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_696 h,accepted_697 h⟩
private noncomputable def tree694 : TapeTree := .centered (candidateRows ibox694) (candidateRows (FixedTape.midBox ibox694))
attribute [irreducible] tree694
private theorem sign_694 : 2*denominator*(computed denominator (FixedTape.midBox ibox694)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox694).gradient k).lo.natAbs ((computed denominator ibox694).gradient k).hi.natAbs : Int)*((ibox694 k).hi-(ibox694 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox694
    (computed denominator ibox694) (computed denominator (FixedTape.midBox ibox694))
    (by decide +kernel)
private theorem midpoint_even_694 : ∀ k, 2 ∣ (ibox694 k).lo+(ibox694 k).hi := by decide +kernel
private theorem accepted_694 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox694) tree694 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox694 midpoint_even_694
  simp only [tree694,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox694,candidate_valid h (FixedTape.midBox ibox694),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox694 212 (FixedTape.rowsAux denominator ibox694 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox694) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_694
private noncomputable def tree693 : TapeTree := .centered (candidateRows ibox693) (candidateRows (FixedTape.midBox ibox693))
attribute [irreducible] tree693
private theorem sign_693 : 2*denominator*(computed denominator (FixedTape.midBox ibox693)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox693).gradient k).lo.natAbs ((computed denominator ibox693).gradient k).hi.natAbs : Int)*((ibox693 k).hi-(ibox693 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox693
    (computed denominator ibox693) (computed denominator (FixedTape.midBox ibox693))
    (by decide +kernel)
private theorem midpoint_even_693 : ∀ k, 2 ∣ (ibox693 k).lo+(ibox693 k).hi := by decide +kernel
private theorem accepted_693 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox693) tree693 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox693 midpoint_even_693
  simp only [tree693,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox693,candidate_valid h (FixedTape.midBox ibox693),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox693 212 (FixedTape.rowsAux denominator ibox693 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox693) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_693
private noncomputable def tree692 : TapeTree := .split 0 (((10067069359663930646449744483631873599419187200000000000 : Int) : ℚ)/(denominator : ℚ)) tree693 tree694
attribute [irreducible] tree692
private theorem accepted_692 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox692) tree692 = true := by
  simp only [tree692,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox692 0 (10067069359663930646449744483631873599419187200000000000 : Int) false,decode_split denominator ibox692 0 (10067069359663930646449744483631873599419187200000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_693 h,accepted_694 h⟩
private noncomputable def tree691 : TapeTree := .split 3 (((12431616634123028271385806917078617936499834880000000000000 : Int) : ℚ)/(denominator : ℚ)) tree692 tree695
attribute [irreducible] tree691
private theorem accepted_691 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox691) tree691 = true := by
  simp only [tree691,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox691 3 (12431616634123028271385806917078617936499834880000000000000 : Int) false,decode_split denominator ibox691 3 (12431616634123028271385806917078617936499834880000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_692 h,accepted_695 h⟩
private noncomputable def tree690 : TapeTree := .centered (candidateRows ibox690) (candidateRows (FixedTape.midBox ibox690))
attribute [irreducible] tree690
private theorem sign_690 : 2*denominator*(computed denominator (FixedTape.midBox ibox690)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox690).gradient k).lo.natAbs ((computed denominator ibox690).gradient k).hi.natAbs : Int)*((ibox690 k).hi-(ibox690 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox690
    (computed denominator ibox690) (computed denominator (FixedTape.midBox ibox690))
    (by decide +kernel)
private theorem midpoint_even_690 : ∀ k, 2 ∣ (ibox690 k).lo+(ibox690 k).hi := by decide +kernel
private theorem accepted_690 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox690) tree690 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox690 midpoint_even_690
  simp only [tree690,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox690,candidate_valid h (FixedTape.midBox ibox690),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox690 212 (FixedTape.rowsAux denominator ibox690 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox690) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_690
private noncomputable def tree689 : TapeTree := .centered (candidateRows ibox689) (candidateRows (FixedTape.midBox ibox689))
attribute [irreducible] tree689
private theorem sign_689 : 2*denominator*(computed denominator (FixedTape.midBox ibox689)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox689).gradient k).lo.natAbs ((computed denominator ibox689).gradient k).hi.natAbs : Int)*((ibox689 k).hi-(ibox689 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox689
    (computed denominator ibox689) (computed denominator (FixedTape.midBox ibox689))
    (by decide +kernel)
private theorem midpoint_even_689 : ∀ k, 2 ∣ (ibox689 k).lo+(ibox689 k).hi := by decide +kernel
private theorem accepted_689 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox689) tree689 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox689 midpoint_even_689
  simp only [tree689,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox689,candidate_valid h (FixedTape.midBox ibox689),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox689 212 (FixedTape.rowsAux denominator ibox689 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox689) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_689
private noncomputable def tree688 : TapeTree := .split 0 (((9700994110221605895669753775136169104894853120000000000 : Int) : ℚ)/(denominator : ℚ)) tree689 tree690
attribute [irreducible] tree688
private theorem accepted_688 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox688) tree688 = true := by
  simp only [tree688,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox688 0 (9700994110221605895669753775136169104894853120000000000 : Int) false,decode_split denominator ibox688 0 (9700994110221605895669753775136169104894853120000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_689 h,accepted_690 h⟩
private noncomputable def tree687 : TapeTree := .centered (candidateRows ibox687) (candidateRows (FixedTape.midBox ibox687))
attribute [irreducible] tree687
private theorem sign_687 : 2*denominator*(computed denominator (FixedTape.midBox ibox687)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox687).gradient k).lo.natAbs ((computed denominator ibox687).gradient k).hi.natAbs : Int)*((ibox687 k).hi-(ibox687 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox687
    (computed denominator ibox687) (computed denominator (FixedTape.midBox ibox687))
    (by decide +kernel)
private theorem midpoint_even_687 : ∀ k, 2 ∣ (ibox687 k).lo+(ibox687 k).hi := by decide +kernel
private theorem accepted_687 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox687) tree687 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox687 midpoint_even_687
  simp only [tree687,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox687,candidate_valid h (FixedTape.midBox ibox687),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox687 212 (FixedTape.rowsAux denominator ibox687 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox687) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_687
private noncomputable def tree686 : TapeTree := .centered (candidateRows ibox686) (candidateRows (FixedTape.midBox ibox686))
attribute [irreducible] tree686
private theorem sign_686 : 2*denominator*(computed denominator (FixedTape.midBox ibox686)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox686).gradient k).lo.natAbs ((computed denominator ibox686).gradient k).hi.natAbs : Int)*((ibox686 k).hi-(ibox686 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox686
    (computed denominator ibox686) (computed denominator (FixedTape.midBox ibox686))
    (by decide +kernel)
private theorem midpoint_even_686 : ∀ k, 2 ∣ (ibox686 k).lo+(ibox686 k).hi := by decide +kernel
private theorem accepted_686 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox686) tree686 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox686 midpoint_even_686
  simp only [tree686,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox686,candidate_valid h (FixedTape.midBox ibox686),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox686 212 (FixedTape.rowsAux denominator ibox686 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox686) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_686
private noncomputable def tree685 : TapeTree := .split 0 (((9700994110221605895669753775136169104894853120000000000 : Int) : ℚ)/(denominator : ℚ)) tree686 tree687
attribute [irreducible] tree685
private theorem accepted_685 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox685) tree685 = true := by
  simp only [tree685,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox685 0 (9700994110221605895669753775136169104894853120000000000 : Int) false,decode_split denominator ibox685 0 (9700994110221605895669753775136169104894853120000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_686 h,accepted_687 h⟩
private noncomputable def tree684 : TapeTree := .split 3 (((12431616634123028271385806917078617936499834880000000000000 : Int) : ℚ)/(denominator : ℚ)) tree685 tree688
attribute [irreducible] tree684
private theorem accepted_684 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox684) tree684 = true := by
  simp only [tree684,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox684 3 (12431616634123028271385806917078617936499834880000000000000 : Int) false,decode_split denominator ibox684 3 (12431616634123028271385806917078617936499834880000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_685 h,accepted_688 h⟩
private noncomputable def tree683 : TapeTree := .split 0 (((9884031734942768271059749129384021352157020160000000000 : Int) : ℚ)/(denominator : ℚ)) tree684 tree691
attribute [irreducible] tree683
private theorem accepted_683 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox683) tree683 = true := by
  simp only [tree683,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox683 0 (9884031734942768271059749129384021352157020160000000000 : Int) false,decode_split denominator ibox683 0 (9884031734942768271059749129384021352157020160000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_684 h,accepted_691 h⟩
private noncomputable def tree682 : TapeTree := .split 3 (((13387894836747876599953945910700050085461360640000000000000 : Int) : ℚ)/(denominator : ℚ)) tree683 tree698
attribute [irreducible] tree682
private theorem accepted_682 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox682) tree682 = true := by
  simp only [tree682,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox682 3 (13387894836747876599953945910700050085461360640000000000000 : Int) false,decode_split denominator ibox682 3 (13387894836747876599953945910700050085461360640000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_683 h,accepted_698 h⟩
private noncomputable def tree681 : TapeTree := .centered (candidateRows ibox681) (candidateRows (FixedTape.midBox ibox681))
attribute [irreducible] tree681
private theorem sign_681 : 2*denominator*(computed denominator (FixedTape.midBox ibox681)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox681).gradient k).lo.natAbs ((computed denominator ibox681).gradient k).hi.natAbs : Int)*((ibox681 k).hi-(ibox681 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox681
    (computed denominator ibox681) (computed denominator (FixedTape.midBox ibox681))
    (by decide +kernel)
private theorem midpoint_even_681 : ∀ k, 2 ∣ (ibox681 k).lo+(ibox681 k).hi := by decide +kernel
private theorem accepted_681 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox681) tree681 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox681 midpoint_even_681
  simp only [tree681,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox681,candidate_valid h (FixedTape.midBox ibox681),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox681 212 (FixedTape.rowsAux denominator ibox681 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox681) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_681
private noncomputable def tree680 : TapeTree := .centered (candidateRows ibox680) (candidateRows (FixedTape.midBox ibox680))
attribute [irreducible] tree680
private theorem sign_680 : 2*denominator*(computed denominator (FixedTape.midBox ibox680)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox680).gradient k).lo.natAbs ((computed denominator ibox680).gradient k).hi.natAbs : Int)*((ibox680 k).hi-(ibox680 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox680
    (computed denominator ibox680) (computed denominator (FixedTape.midBox ibox680))
    (by decide +kernel)
private theorem midpoint_even_680 : ∀ k, 2 ∣ (ibox680 k).lo+(ibox680 k).hi := by decide +kernel
private theorem accepted_680 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox680) tree680 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox680 midpoint_even_680
  simp only [tree680,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox680,candidate_valid h (FixedTape.midBox ibox680),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox680 212 (FixedTape.rowsAux denominator ibox680 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox680) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_680
private noncomputable def tree679 : TapeTree := .split 3 (((10519060228873331614249528929835753638576783360000000000000 : Int) : ℚ)/(denominator : ℚ)) tree680 tree681
attribute [irreducible] tree679
private theorem accepted_679 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox679) tree679 = true := by
  simp only [tree679,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox679 3 (10519060228873331614249528929835753638576783360000000000000 : Int) false,decode_split denominator ibox679 3 (10519060228873331614249528929835753638576783360000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_680 h,accepted_681 h⟩
private noncomputable def tree678 : TapeTree := .centered (candidateRows ibox678) (candidateRows (FixedTape.midBox ibox678))
attribute [irreducible] tree678
private theorem sign_678 : 2*denominator*(computed denominator (FixedTape.midBox ibox678)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox678).gradient k).lo.natAbs ((computed denominator ibox678).gradient k).hi.natAbs : Int)*((ibox678 k).hi-(ibox678 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox678
    (computed denominator ibox678) (computed denominator (FixedTape.midBox ibox678))
    (by decide +kernel)
private theorem midpoint_even_678 : ∀ k, 2 ∣ (ibox678 k).lo+(ibox678 k).hi := by decide +kernel
private theorem accepted_678 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox678) tree678 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox678 midpoint_even_678
  simp only [tree678,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox678,candidate_valid h (FixedTape.midBox ibox678),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox678 212 (FixedTape.rowsAux denominator ibox678 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox678) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_678
private noncomputable def tree677 : TapeTree := .centered (candidateRows ibox677) (candidateRows (FixedTape.midBox ibox677))
attribute [irreducible] tree677
private theorem sign_677 : 2*denominator*(computed denominator (FixedTape.midBox ibox677)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox677).gradient k).lo.natAbs ((computed denominator ibox677).gradient k).hi.natAbs : Int)*((ibox677 k).hi-(ibox677 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox677
    (computed denominator ibox677) (computed denominator (FixedTape.midBox ibox677))
    (by decide +kernel)
private theorem midpoint_even_677 : ∀ k, 2 ∣ (ibox677 k).lo+(ibox677 k).hi := by decide +kernel
private theorem accepted_677 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox677) tree677 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox677 midpoint_even_677
  simp only [tree677,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox677,candidate_valid h (FixedTape.midBox ibox677),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox677 212 (FixedTape.rowsAux denominator ibox677 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox677) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_677
private noncomputable def tree676 : TapeTree := .split 3 (((10519060228873331614249528929835753638576783360000000000000 : Int) : ℚ)/(denominator : ℚ)) tree677 tree678
attribute [irreducible] tree676
private theorem accepted_676 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox676) tree676 = true := by
  simp only [tree676,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox676 3 (10519060228873331614249528929835753638576783360000000000000 : Int) false,decode_split denominator ibox676 3 (10519060228873331614249528929835753638576783360000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_677 h,accepted_678 h⟩
private noncomputable def tree675 : TapeTree := .split 0 (((10067069359663930646449744483631873599419187200000000000 : Int) : ℚ)/(denominator : ℚ)) tree676 tree679
attribute [irreducible] tree675
private theorem accepted_675 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox675) tree675 = true := by
  simp only [tree675,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox675 0 (10067069359663930646449744483631873599419187200000000000 : Int) false,decode_split denominator ibox675 0 (10067069359663930646449744483631873599419187200000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_676 h,accepted_679 h⟩
private noncomputable def tree674 : TapeTree := .centered (candidateRows ibox674) (candidateRows (FixedTape.midBox ibox674))
attribute [irreducible] tree674
private theorem sign_674 : 2*denominator*(computed denominator (FixedTape.midBox ibox674)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox674).gradient k).lo.natAbs ((computed denominator ibox674).gradient k).hi.natAbs : Int)*((ibox674 k).hi-(ibox674 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox674
    (computed denominator ibox674) (computed denominator (FixedTape.midBox ibox674))
    (by decide +kernel)
private theorem midpoint_even_674 : ∀ k, 2 ∣ (ibox674 k).lo+(ibox674 k).hi := by decide +kernel
private theorem accepted_674 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox674) tree674 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox674 midpoint_even_674
  simp only [tree674,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox674,candidate_valid h (FixedTape.midBox ibox674),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox674 212 (FixedTape.rowsAux denominator ibox674 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox674) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_674
private noncomputable def tree673 : TapeTree := .centered (candidateRows ibox673) (candidateRows (FixedTape.midBox ibox673))
attribute [irreducible] tree673
private theorem sign_673 : 2*denominator*(computed denominator (FixedTape.midBox ibox673)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox673).gradient k).lo.natAbs ((computed denominator ibox673).gradient k).hi.natAbs : Int)*((ibox673 k).hi-(ibox673 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox673
    (computed denominator ibox673) (computed denominator (FixedTape.midBox ibox673))
    (by decide +kernel)
private theorem midpoint_even_673 : ∀ k, 2 ∣ (ibox673 k).lo+(ibox673 k).hi := by decide +kernel
private theorem accepted_673 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox673) tree673 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox673 midpoint_even_673
  simp only [tree673,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox673,candidate_valid h (FixedTape.midBox ibox673),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox673 212 (FixedTape.rowsAux denominator ibox673 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox673) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_673
private noncomputable def tree672 : TapeTree := .split 3 (((8606503823623634957113250942592889340653731840000000000000 : Int) : ℚ)/(denominator : ℚ)) tree673 tree674
attribute [irreducible] tree672
private theorem accepted_672 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox672) tree672 = true := by
  simp only [tree672,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox672 3 (8606503823623634957113250942592889340653731840000000000000 : Int) false,decode_split denominator ibox672 3 (8606503823623634957113250942592889340653731840000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_673 h,accepted_674 h⟩
private noncomputable def tree671 : TapeTree := .centered (candidateRows ibox671) (candidateRows (FixedTape.midBox ibox671))
attribute [irreducible] tree671
private theorem sign_671 : 2*denominator*(computed denominator (FixedTape.midBox ibox671)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox671).gradient k).lo.natAbs ((computed denominator ibox671).gradient k).hi.natAbs : Int)*((ibox671 k).hi-(ibox671 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox671
    (computed denominator ibox671) (computed denominator (FixedTape.midBox ibox671))
    (by decide +kernel)
private theorem midpoint_even_671 : ∀ k, 2 ∣ (ibox671 k).lo+(ibox671 k).hi := by decide +kernel
private theorem accepted_671 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox671) tree671 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox671 midpoint_even_671
  simp only [tree671,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox671,candidate_valid h (FixedTape.midBox ibox671),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox671 212 (FixedTape.rowsAux denominator ibox671 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox671) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_671
private noncomputable def tree670 : TapeTree := .centered (candidateRows ibox670) (candidateRows (FixedTape.midBox ibox670))
attribute [irreducible] tree670
private theorem sign_670 : 2*denominator*(computed denominator (FixedTape.midBox ibox670)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox670).gradient k).lo.natAbs ((computed denominator ibox670).gradient k).hi.natAbs : Int)*((ibox670 k).hi-(ibox670 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox670
    (computed denominator ibox670) (computed denominator (FixedTape.midBox ibox670))
    (by decide +kernel)
private theorem midpoint_even_670 : ∀ k, 2 ∣ (ibox670 k).lo+(ibox670 k).hi := by decide +kernel
private theorem accepted_670 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox670) tree670 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox670 midpoint_even_670
  simp only [tree670,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox670,candidate_valid h (FixedTape.midBox ibox670),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox670 212 (FixedTape.rowsAux denominator ibox670 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox670) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_670
private noncomputable def tree669 : TapeTree := .split 3 (((8606503823623634957113250942592889340653731840000000000000 : Int) : ℚ)/(denominator : ℚ)) tree670 tree671
attribute [irreducible] tree669
private theorem accepted_669 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox669) tree669 = true := by
  simp only [tree669,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox669 3 (8606503823623634957113250942592889340653731840000000000000 : Int) false,decode_split denominator ibox669 3 (8606503823623634957113250942592889340653731840000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_670 h,accepted_671 h⟩
private noncomputable def tree668 : TapeTree := .split 0 (((10067069359663930646449744483631873599419187200000000000 : Int) : ℚ)/(denominator : ℚ)) tree669 tree672
attribute [irreducible] tree668
private theorem accepted_668 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox668) tree668 = true := by
  simp only [tree668,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox668 0 (10067069359663930646449744483631873599419187200000000000 : Int) false,decode_split denominator ibox668 0 (10067069359663930646449744483631873599419187200000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_669 h,accepted_672 h⟩
private noncomputable def tree667 : TapeTree := .split 3 (((9562782026248483285681389936214321489615257600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree668 tree675
attribute [irreducible] tree667
private theorem accepted_667 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox667) tree667 = true := by
  simp only [tree667,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox667 3 (9562782026248483285681389936214321489615257600000000000000 : Int) false,decode_split denominator ibox667 3 (9562782026248483285681389936214321489615257600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_668 h,accepted_675 h⟩
private noncomputable def tree666 : TapeTree := .centered (candidateRows ibox666) (candidateRows (FixedTape.midBox ibox666))
attribute [irreducible] tree666
private theorem sign_666 : 2*denominator*(computed denominator (FixedTape.midBox ibox666)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox666).gradient k).lo.natAbs ((computed denominator ibox666).gradient k).hi.natAbs : Int)*((ibox666 k).hi-(ibox666 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox666
    (computed denominator ibox666) (computed denominator (FixedTape.midBox ibox666))
    (by decide +kernel)
private theorem midpoint_even_666 : ∀ k, 2 ∣ (ibox666 k).lo+(ibox666 k).hi := by decide +kernel
private theorem accepted_666 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox666) tree666 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox666 midpoint_even_666
  simp only [tree666,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox666,candidate_valid h (FixedTape.midBox ibox666),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox666 212 (FixedTape.rowsAux denominator ibox666 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox666) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_666
private noncomputable def tree665 : TapeTree := .centered (candidateRows ibox665) (candidateRows (FixedTape.midBox ibox665))
attribute [irreducible] tree665
private theorem sign_665 : 2*denominator*(computed denominator (FixedTape.midBox ibox665)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox665).gradient k).lo.natAbs ((computed denominator ibox665).gradient k).hi.natAbs : Int)*((ibox665 k).hi-(ibox665 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox665
    (computed denominator ibox665) (computed denominator (FixedTape.midBox ibox665))
    (by decide +kernel)
private theorem midpoint_even_665 : ∀ k, 2 ∣ (ibox665 k).lo+(ibox665 k).hi := by decide +kernel
private theorem accepted_665 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox665) tree665 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox665 midpoint_even_665
  simp only [tree665,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox665,candidate_valid h (FixedTape.midBox ibox665),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox665 212 (FixedTape.rowsAux denominator ibox665 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox665) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_665
private noncomputable def tree664 : TapeTree := .split 3 (((10519060228873331614249528929835753638576783360000000000000 : Int) : ℚ)/(denominator : ℚ)) tree665 tree666
attribute [irreducible] tree664
private theorem accepted_664 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox664) tree664 = true := by
  simp only [tree664,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox664 3 (10519060228873331614249528929835753638576783360000000000000 : Int) false,decode_split denominator ibox664 3 (10519060228873331614249528929835753638576783360000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_665 h,accepted_666 h⟩
private noncomputable def tree663 : TapeTree := .centered (candidateRows ibox663) (candidateRows (FixedTape.midBox ibox663))
attribute [irreducible] tree663
private theorem sign_663 : 2*denominator*(computed denominator (FixedTape.midBox ibox663)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox663).gradient k).lo.natAbs ((computed denominator ibox663).gradient k).hi.natAbs : Int)*((ibox663 k).hi-(ibox663 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox663
    (computed denominator ibox663) (computed denominator (FixedTape.midBox ibox663))
    (by decide +kernel)
private theorem midpoint_even_663 : ∀ k, 2 ∣ (ibox663 k).lo+(ibox663 k).hi := by decide +kernel
private theorem accepted_663 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox663) tree663 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox663 midpoint_even_663
  simp only [tree663,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox663,candidate_valid h (FixedTape.midBox ibox663),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox663 212 (FixedTape.rowsAux denominator ibox663 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox663) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_663
private noncomputable def tree662 : TapeTree := .centered (candidateRows ibox662) (candidateRows (FixedTape.midBox ibox662))
attribute [irreducible] tree662
private theorem sign_662 : 2*denominator*(computed denominator (FixedTape.midBox ibox662)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox662).gradient k).lo.natAbs ((computed denominator ibox662).gradient k).hi.natAbs : Int)*((ibox662 k).hi-(ibox662 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox662
    (computed denominator ibox662) (computed denominator (FixedTape.midBox ibox662))
    (by decide +kernel)
private theorem midpoint_even_662 : ∀ k, 2 ∣ (ibox662 k).lo+(ibox662 k).hi := by decide +kernel
private theorem accepted_662 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox662) tree662 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox662 midpoint_even_662
  simp only [tree662,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox662,candidate_valid h (FixedTape.midBox ibox662),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox662 212 (FixedTape.rowsAux denominator ibox662 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox662) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_662
private noncomputable def tree661 : TapeTree := .split 3 (((10519060228873331614249528929835753638576783360000000000000 : Int) : ℚ)/(denominator : ℚ)) tree662 tree663
attribute [irreducible] tree661
private theorem accepted_661 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox661) tree661 = true := by
  simp only [tree661,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox661 3 (10519060228873331614249528929835753638576783360000000000000 : Int) false,decode_split denominator ibox661 3 (10519060228873331614249528929835753638576783360000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_662 h,accepted_663 h⟩
private noncomputable def tree660 : TapeTree := .split 0 (((9700994110221605895669753775136169104894853120000000000 : Int) : ℚ)/(denominator : ℚ)) tree661 tree664
attribute [irreducible] tree660
private theorem accepted_660 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox660) tree660 = true := by
  simp only [tree660,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox660 0 (9700994110221605895669753775136169104894853120000000000 : Int) false,decode_split denominator ibox660 0 (9700994110221605895669753775136169104894853120000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_661 h,accepted_664 h⟩
private noncomputable def tree659 : TapeTree := .centered (candidateRows ibox659) (candidateRows (FixedTape.midBox ibox659))
attribute [irreducible] tree659
private theorem sign_659 : 2*denominator*(computed denominator (FixedTape.midBox ibox659)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox659).gradient k).lo.natAbs ((computed denominator ibox659).gradient k).hi.natAbs : Int)*((ibox659 k).hi-(ibox659 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox659
    (computed denominator ibox659) (computed denominator (FixedTape.midBox ibox659))
    (by decide +kernel)
private theorem midpoint_even_659 : ∀ k, 2 ∣ (ibox659 k).lo+(ibox659 k).hi := by decide +kernel
private theorem accepted_659 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox659) tree659 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox659 midpoint_even_659
  simp only [tree659,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox659,candidate_valid h (FixedTape.midBox ibox659),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox659 212 (FixedTape.rowsAux denominator ibox659 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox659) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_659
private noncomputable def tree658 : TapeTree := .centered (candidateRows ibox658) (candidateRows (FixedTape.midBox ibox658))
attribute [irreducible] tree658
private theorem sign_658 : 2*denominator*(computed denominator (FixedTape.midBox ibox658)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox658).gradient k).lo.natAbs ((computed denominator ibox658).gradient k).hi.natAbs : Int)*((ibox658 k).hi-(ibox658 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox658
    (computed denominator ibox658) (computed denominator (FixedTape.midBox ibox658))
    (by decide +kernel)
private theorem midpoint_even_658 : ∀ k, 2 ∣ (ibox658 k).lo+(ibox658 k).hi := by decide +kernel
private theorem accepted_658 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox658) tree658 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox658 midpoint_even_658
  simp only [tree658,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox658,candidate_valid h (FixedTape.midBox ibox658),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox658 212 (FixedTape.rowsAux denominator ibox658 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox658) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_658
private noncomputable def tree657 : TapeTree := .split 3 (((8606503823623634957113250942592889340653731840000000000000 : Int) : ℚ)/(denominator : ℚ)) tree658 tree659
attribute [irreducible] tree657
private theorem accepted_657 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox657) tree657 = true := by
  simp only [tree657,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox657 3 (8606503823623634957113250942592889340653731840000000000000 : Int) false,decode_split denominator ibox657 3 (8606503823623634957113250942592889340653731840000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_658 h,accepted_659 h⟩
private noncomputable def tree656 : TapeTree := .centered (candidateRows ibox656) (candidateRows (FixedTape.midBox ibox656))
attribute [irreducible] tree656
private theorem sign_656 : 2*denominator*(computed denominator (FixedTape.midBox ibox656)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox656).gradient k).lo.natAbs ((computed denominator ibox656).gradient k).hi.natAbs : Int)*((ibox656 k).hi-(ibox656 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox656
    (computed denominator ibox656) (computed denominator (FixedTape.midBox ibox656))
    (by decide +kernel)
private theorem midpoint_even_656 : ∀ k, 2 ∣ (ibox656 k).lo+(ibox656 k).hi := by decide +kernel
private theorem accepted_656 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox656) tree656 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox656 midpoint_even_656
  simp only [tree656,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox656,candidate_valid h (FixedTape.midBox ibox656),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox656 212 (FixedTape.rowsAux denominator ibox656 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox656) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_656
private noncomputable def tree655 : TapeTree := .centered (candidateRows ibox655) (candidateRows (FixedTape.midBox ibox655))
attribute [irreducible] tree655
private theorem sign_655 : 2*denominator*(computed denominator (FixedTape.midBox ibox655)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox655).gradient k).lo.natAbs ((computed denominator ibox655).gradient k).hi.natAbs : Int)*((ibox655 k).hi-(ibox655 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox655
    (computed denominator ibox655) (computed denominator (FixedTape.midBox ibox655))
    (by decide +kernel)
private theorem midpoint_even_655 : ∀ k, 2 ∣ (ibox655 k).lo+(ibox655 k).hi := by decide +kernel
private theorem accepted_655 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox655) tree655 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox655 midpoint_even_655
  simp only [tree655,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox655,candidate_valid h (FixedTape.midBox ibox655),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox655 212 (FixedTape.rowsAux denominator ibox655 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox655) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_655
private noncomputable def tree654 : TapeTree := .split 3 (((8606503823623634957113250942592889340653731840000000000000 : Int) : ℚ)/(denominator : ℚ)) tree655 tree656
attribute [irreducible] tree654
private theorem accepted_654 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox654) tree654 = true := by
  simp only [tree654,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox654 3 (8606503823623634957113250942592889340653731840000000000000 : Int) false,decode_split denominator ibox654 3 (8606503823623634957113250942592889340653731840000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_655 h,accepted_656 h⟩
private noncomputable def tree653 : TapeTree := .split 0 (((9700994110221605895669753775136169104894853120000000000 : Int) : ℚ)/(denominator : ℚ)) tree654 tree657
attribute [irreducible] tree653
private theorem accepted_653 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox653) tree653 = true := by
  simp only [tree653,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox653 0 (9700994110221605895669753775136169104894853120000000000 : Int) false,decode_split denominator ibox653 0 (9700994110221605895669753775136169104894853120000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_654 h,accepted_657 h⟩
private noncomputable def tree652 : TapeTree := .split 3 (((9562782026248483285681389936214321489615257600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree653 tree660
attribute [irreducible] tree652
private theorem accepted_652 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox652) tree652 = true := by
  simp only [tree652,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox652 3 (9562782026248483285681389936214321489615257600000000000000 : Int) false,decode_split denominator ibox652 3 (9562782026248483285681389936214321489615257600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_653 h,accepted_660 h⟩
private noncomputable def tree651 : TapeTree := .split 0 (((9884031734942768271059749129384021352157020160000000000 : Int) : ℚ)/(denominator : ℚ)) tree652 tree667
attribute [irreducible] tree651
private theorem accepted_651 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox651) tree651 = true := by
  simp only [tree651,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox651 0 (9884031734942768271059749129384021352157020160000000000 : Int) false,decode_split denominator ibox651 0 (9884031734942768271059749129384021352157020160000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_652 h,accepted_667 h⟩
private noncomputable def tree650 : TapeTree := .split 3 (((11475338431498179942817667923457185787538309120000000000000 : Int) : ℚ)/(denominator : ℚ)) tree651 tree682
attribute [irreducible] tree650
private theorem accepted_650 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox650) tree650 = true := by
  simp only [tree650,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox650 3 (11475338431498179942817667923457185787538309120000000000000 : Int) false,decode_split denominator ibox650 3 (11475338431498179942817667923457185787538309120000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_651 h,accepted_682 h⟩
private noncomputable def tree649 : TapeTree := .centered (candidateRows ibox649) (candidateRows (FixedTape.midBox ibox649))
attribute [irreducible] tree649
private theorem sign_649 : 2*denominator*(computed denominator (FixedTape.midBox ibox649)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox649).gradient k).lo.natAbs ((computed denominator ibox649).gradient k).hi.natAbs : Int)*((ibox649 k).hi-(ibox649 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox649
    (computed denominator ibox649) (computed denominator (FixedTape.midBox ibox649))
    (by decide +kernel)
private theorem midpoint_even_649 : ∀ k, 2 ∣ (ibox649 k).lo+(ibox649 k).hi := by decide +kernel
private theorem accepted_649 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox649) tree649 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox649 midpoint_even_649
  simp only [tree649,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox649,candidate_valid h (FixedTape.midBox ibox649),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox649 212 (FixedTape.rowsAux denominator ibox649 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox649) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_649
private noncomputable def tree648 : TapeTree := .centered (candidateRows ibox648) (candidateRows (FixedTape.midBox ibox648))
attribute [irreducible] tree648
private theorem sign_648 : 2*denominator*(computed denominator (FixedTape.midBox ibox648)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox648).gradient k).lo.natAbs ((computed denominator ibox648).gradient k).hi.natAbs : Int)*((ibox648 k).hi-(ibox648 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox648
    (computed denominator ibox648) (computed denominator (FixedTape.midBox ibox648))
    (by decide +kernel)
private theorem midpoint_even_648 : ∀ k, 2 ∣ (ibox648 k).lo+(ibox648 k).hi := by decide +kernel
private theorem accepted_648 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox648) tree648 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox648 midpoint_even_648
  simp only [tree648,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox648,candidate_valid h (FixedTape.midBox ibox648),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox648 212 (FixedTape.rowsAux denominator ibox648 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox648) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_648
private noncomputable def tree647 : TapeTree := .split 3 (((6693947418373938299976972955350025042730680320000000000000 : Int) : ℚ)/(denominator : ℚ)) tree648 tree649
attribute [irreducible] tree647
private theorem accepted_647 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox647) tree647 = true := by
  simp only [tree647,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox647 3 (6693947418373938299976972955350025042730680320000000000000 : Int) false,decode_split denominator ibox647 3 (6693947418373938299976972955350025042730680320000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_648 h,accepted_649 h⟩
private noncomputable def tree646 : TapeTree := .centered (candidateRows ibox646) (candidateRows (FixedTape.midBox ibox646))
attribute [irreducible] tree646
private theorem sign_646 : 2*denominator*(computed denominator (FixedTape.midBox ibox646)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox646).gradient k).lo.natAbs ((computed denominator ibox646).gradient k).hi.natAbs : Int)*((ibox646 k).hi-(ibox646 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox646
    (computed denominator ibox646) (computed denominator (FixedTape.midBox ibox646))
    (by decide +kernel)
private theorem midpoint_even_646 : ∀ k, 2 ∣ (ibox646 k).lo+(ibox646 k).hi := by decide +kernel
private theorem accepted_646 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox646) tree646 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox646 midpoint_even_646
  simp only [tree646,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox646,candidate_valid h (FixedTape.midBox ibox646),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox646 212 (FixedTape.rowsAux denominator ibox646 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox646) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_646
private noncomputable def tree645 : TapeTree := .centered (candidateRows ibox645) (candidateRows (FixedTape.midBox ibox645))
attribute [irreducible] tree645
private theorem sign_645 : 2*denominator*(computed denominator (FixedTape.midBox ibox645)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox645).gradient k).lo.natAbs ((computed denominator ibox645).gradient k).hi.natAbs : Int)*((ibox645 k).hi-(ibox645 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox645
    (computed denominator ibox645) (computed denominator (FixedTape.midBox ibox645))
    (by decide +kernel)
private theorem midpoint_even_645 : ∀ k, 2 ∣ (ibox645 k).lo+(ibox645 k).hi := by decide +kernel
private theorem accepted_645 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox645) tree645 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox645 midpoint_even_645
  simp only [tree645,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox645,candidate_valid h (FixedTape.midBox ibox645),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox645 212 (FixedTape.rowsAux denominator ibox645 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox645) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_645
private noncomputable def tree644 : TapeTree := .split 3 (((6693947418373938299976972955350025042730680320000000000000 : Int) : ℚ)/(denominator : ℚ)) tree645 tree646
attribute [irreducible] tree644
private theorem accepted_644 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox644) tree644 = true := by
  simp only [tree644,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox644 3 (6693947418373938299976972955350025042730680320000000000000 : Int) false,decode_split denominator ibox644 3 (6693947418373938299976972955350025042730680320000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_645 h,accepted_646 h⟩
private noncomputable def tree643 : TapeTree := .split 0 (((10067069359663930646449744483631873599419187200000000000 : Int) : ℚ)/(denominator : ℚ)) tree644 tree647
attribute [irreducible] tree643
private theorem accepted_643 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox643) tree643 = true := by
  simp only [tree643,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox643 0 (10067069359663930646449744483631873599419187200000000000 : Int) false,decode_split denominator ibox643 0 (10067069359663930646449744483631873599419187200000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_644 h,accepted_647 h⟩
private noncomputable def tree642 : TapeTree := .centered (candidateRows ibox642) (candidateRows (FixedTape.midBox ibox642))
attribute [irreducible] tree642
private theorem sign_642 : 2*denominator*(computed denominator (FixedTape.midBox ibox642)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox642).gradient k).lo.natAbs ((computed denominator ibox642).gradient k).hi.natAbs : Int)*((ibox642 k).hi-(ibox642 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox642
    (computed denominator ibox642) (computed denominator (FixedTape.midBox ibox642))
    (by decide +kernel)
private theorem midpoint_even_642 : ∀ k, 2 ∣ (ibox642 k).lo+(ibox642 k).hi := by decide +kernel
private theorem accepted_642 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox642) tree642 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox642 midpoint_even_642
  simp only [tree642,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox642,candidate_valid h (FixedTape.midBox ibox642),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox642 212 (FixedTape.rowsAux denominator ibox642 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox642) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_642
private noncomputable def tree641 : TapeTree := .centered (candidateRows ibox641) (candidateRows (FixedTape.midBox ibox641))
attribute [irreducible] tree641
private theorem sign_641 : 2*denominator*(computed denominator (FixedTape.midBox ibox641)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox641).gradient k).lo.natAbs ((computed denominator ibox641).gradient k).hi.natAbs : Int)*((ibox641 k).hi-(ibox641 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox641
    (computed denominator ibox641) (computed denominator (FixedTape.midBox ibox641))
    (by decide +kernel)
private theorem midpoint_even_641 : ∀ k, 2 ∣ (ibox641 k).lo+(ibox641 k).hi := by decide +kernel
private theorem accepted_641 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox641) tree641 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox641 midpoint_even_641
  simp only [tree641,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox641,candidate_valid h (FixedTape.midBox ibox641),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox641 212 (FixedTape.rowsAux denominator ibox641 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox641) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_641
private noncomputable def tree640 : TapeTree := .split 3 (((4781391013124241642840694968107160744807628800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree641 tree642
attribute [irreducible] tree640
private theorem accepted_640 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox640) tree640 = true := by
  simp only [tree640,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox640 3 (4781391013124241642840694968107160744807628800000000000000 : Int) false,decode_split denominator ibox640 3 (4781391013124241642840694968107160744807628800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_641 h,accepted_642 h⟩
private noncomputable def tree639 : TapeTree := .centered (candidateRows ibox639) (candidateRows (FixedTape.midBox ibox639))
attribute [irreducible] tree639
private theorem sign_639 : 2*denominator*(computed denominator (FixedTape.midBox ibox639)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox639).gradient k).lo.natAbs ((computed denominator ibox639).gradient k).hi.natAbs : Int)*((ibox639 k).hi-(ibox639 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox639
    (computed denominator ibox639) (computed denominator (FixedTape.midBox ibox639))
    (by decide +kernel)
private theorem midpoint_even_639 : ∀ k, 2 ∣ (ibox639 k).lo+(ibox639 k).hi := by decide +kernel
private theorem accepted_639 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox639) tree639 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox639 midpoint_even_639
  simp only [tree639,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox639,candidate_valid h (FixedTape.midBox ibox639),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox639 212 (FixedTape.rowsAux denominator ibox639 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox639) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_639
private noncomputable def tree638 : TapeTree := .centered (candidateRows ibox638) (candidateRows (FixedTape.midBox ibox638))
attribute [irreducible] tree638
private theorem sign_638 : 2*denominator*(computed denominator (FixedTape.midBox ibox638)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox638).gradient k).lo.natAbs ((computed denominator ibox638).gradient k).hi.natAbs : Int)*((ibox638 k).hi-(ibox638 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox638
    (computed denominator ibox638) (computed denominator (FixedTape.midBox ibox638))
    (by decide +kernel)
private theorem midpoint_even_638 : ∀ k, 2 ∣ (ibox638 k).lo+(ibox638 k).hi := by decide +kernel
private theorem accepted_638 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox638) tree638 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox638 midpoint_even_638
  simp only [tree638,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox638,candidate_valid h (FixedTape.midBox ibox638),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox638 212 (FixedTape.rowsAux denominator ibox638 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox638) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_638
private noncomputable def tree637 : TapeTree := .split 3 (((4781391013124241642840694968107160744807628800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree638 tree639
attribute [irreducible] tree637
private theorem accepted_637 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox637) tree637 = true := by
  simp only [tree637,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox637 3 (4781391013124241642840694968107160744807628800000000000000 : Int) false,decode_split denominator ibox637 3 (4781391013124241642840694968107160744807628800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_638 h,accepted_639 h⟩
private noncomputable def tree636 : TapeTree := .split 0 (((10067069359663930646449744483631873599419187200000000000 : Int) : ℚ)/(denominator : ℚ)) tree637 tree640
attribute [irreducible] tree636
private theorem accepted_636 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox636) tree636 = true := by
  simp only [tree636,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox636 0 (10067069359663930646449744483631873599419187200000000000 : Int) false,decode_split denominator ibox636 0 (10067069359663930646449744483631873599419187200000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_637 h,accepted_640 h⟩
private noncomputable def tree635 : TapeTree := .split 3 (((5737669215749089971408833961728592893769154560000000000000 : Int) : ℚ)/(denominator : ℚ)) tree636 tree643
attribute [irreducible] tree635
private theorem accepted_635 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox635) tree635 = true := by
  simp only [tree635,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox635 3 (5737669215749089971408833961728592893769154560000000000000 : Int) false,decode_split denominator ibox635 3 (5737669215749089971408833961728592893769154560000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_636 h,accepted_643 h⟩
private noncomputable def tree634 : TapeTree := .centered (candidateRows ibox634) (candidateRows (FixedTape.midBox ibox634))
attribute [irreducible] tree634
private theorem sign_634 : 2*denominator*(computed denominator (FixedTape.midBox ibox634)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox634).gradient k).lo.natAbs ((computed denominator ibox634).gradient k).hi.natAbs : Int)*((ibox634 k).hi-(ibox634 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox634
    (computed denominator ibox634) (computed denominator (FixedTape.midBox ibox634))
    (by decide +kernel)
private theorem midpoint_even_634 : ∀ k, 2 ∣ (ibox634 k).lo+(ibox634 k).hi := by decide +kernel
private theorem accepted_634 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox634) tree634 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox634 midpoint_even_634
  simp only [tree634,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox634,candidate_valid h (FixedTape.midBox ibox634),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox634 212 (FixedTape.rowsAux denominator ibox634 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox634) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_634
private noncomputable def tree633 : TapeTree := .centered (candidateRows ibox633) (candidateRows (FixedTape.midBox ibox633))
attribute [irreducible] tree633
private theorem sign_633 : 2*denominator*(computed denominator (FixedTape.midBox ibox633)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox633).gradient k).lo.natAbs ((computed denominator ibox633).gradient k).hi.natAbs : Int)*((ibox633 k).hi-(ibox633 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox633
    (computed denominator ibox633) (computed denominator (FixedTape.midBox ibox633))
    (by decide +kernel)
private theorem midpoint_even_633 : ∀ k, 2 ∣ (ibox633 k).lo+(ibox633 k).hi := by decide +kernel
private theorem accepted_633 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox633) tree633 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox633 midpoint_even_633
  simp only [tree633,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox633,candidate_valid h (FixedTape.midBox ibox633),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox633 212 (FixedTape.rowsAux denominator ibox633 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox633) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_633
private noncomputable def tree632 : TapeTree := .split 3 (((6693947418373938299976972955350025042730680320000000000000 : Int) : ℚ)/(denominator : ℚ)) tree633 tree634
attribute [irreducible] tree632
private theorem accepted_632 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox632) tree632 = true := by
  simp only [tree632,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox632 3 (6693947418373938299976972955350025042730680320000000000000 : Int) false,decode_split denominator ibox632 3 (6693947418373938299976972955350025042730680320000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_633 h,accepted_634 h⟩
private noncomputable def tree631 : TapeTree := .centered (candidateRows ibox631) (candidateRows (FixedTape.midBox ibox631))
attribute [irreducible] tree631
private theorem sign_631 : 2*denominator*(computed denominator (FixedTape.midBox ibox631)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox631).gradient k).lo.natAbs ((computed denominator ibox631).gradient k).hi.natAbs : Int)*((ibox631 k).hi-(ibox631 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox631
    (computed denominator ibox631) (computed denominator (FixedTape.midBox ibox631))
    (by decide +kernel)
private theorem midpoint_even_631 : ∀ k, 2 ∣ (ibox631 k).lo+(ibox631 k).hi := by decide +kernel
private theorem accepted_631 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox631) tree631 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox631 midpoint_even_631
  simp only [tree631,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox631,candidate_valid h (FixedTape.midBox ibox631),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox631 212 (FixedTape.rowsAux denominator ibox631 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox631) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_631
private noncomputable def tree630 : TapeTree := .centered (candidateRows ibox630) (candidateRows (FixedTape.midBox ibox630))
attribute [irreducible] tree630
private theorem sign_630 : 2*denominator*(computed denominator (FixedTape.midBox ibox630)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox630).gradient k).lo.natAbs ((computed denominator ibox630).gradient k).hi.natAbs : Int)*((ibox630 k).hi-(ibox630 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox630
    (computed denominator ibox630) (computed denominator (FixedTape.midBox ibox630))
    (by decide +kernel)
private theorem midpoint_even_630 : ∀ k, 2 ∣ (ibox630 k).lo+(ibox630 k).hi := by decide +kernel
private theorem accepted_630 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox630) tree630 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox630 midpoint_even_630
  simp only [tree630,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox630,candidate_valid h (FixedTape.midBox ibox630),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox630 212 (FixedTape.rowsAux denominator ibox630 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox630) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_630
private noncomputable def tree629 : TapeTree := .split 3 (((6693947418373938299976972955350025042730680320000000000000 : Int) : ℚ)/(denominator : ℚ)) tree630 tree631
attribute [irreducible] tree629
private theorem accepted_629 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox629) tree629 = true := by
  simp only [tree629,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox629 3 (6693947418373938299976972955350025042730680320000000000000 : Int) false,decode_split denominator ibox629 3 (6693947418373938299976972955350025042730680320000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_630 h,accepted_631 h⟩
private noncomputable def tree628 : TapeTree := .split 0 (((9700994110221605895669753775136169104894853120000000000 : Int) : ℚ)/(denominator : ℚ)) tree629 tree632
attribute [irreducible] tree628
private theorem accepted_628 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox628) tree628 = true := by
  simp only [tree628,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox628 0 (9700994110221605895669753775136169104894853120000000000 : Int) false,decode_split denominator ibox628 0 (9700994110221605895669753775136169104894853120000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_629 h,accepted_632 h⟩
private noncomputable def tree627 : TapeTree := .centered (candidateRows ibox627) (candidateRows (FixedTape.midBox ibox627))
attribute [irreducible] tree627
private theorem sign_627 : 2*denominator*(computed denominator (FixedTape.midBox ibox627)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox627).gradient k).lo.natAbs ((computed denominator ibox627).gradient k).hi.natAbs : Int)*((ibox627 k).hi-(ibox627 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox627
    (computed denominator ibox627) (computed denominator (FixedTape.midBox ibox627))
    (by decide +kernel)
private theorem midpoint_even_627 : ∀ k, 2 ∣ (ibox627 k).lo+(ibox627 k).hi := by decide +kernel
private theorem accepted_627 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox627) tree627 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox627 midpoint_even_627
  simp only [tree627,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox627,candidate_valid h (FixedTape.midBox ibox627),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox627 212 (FixedTape.rowsAux denominator ibox627 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox627) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_627
private noncomputable def tree626 : TapeTree := .centered (candidateRows ibox626) (candidateRows (FixedTape.midBox ibox626))
attribute [irreducible] tree626
private theorem sign_626 : 2*denominator*(computed denominator (FixedTape.midBox ibox626)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox626).gradient k).lo.natAbs ((computed denominator ibox626).gradient k).hi.natAbs : Int)*((ibox626 k).hi-(ibox626 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox626
    (computed denominator ibox626) (computed denominator (FixedTape.midBox ibox626))
    (by decide +kernel)
private theorem midpoint_even_626 : ∀ k, 2 ∣ (ibox626 k).lo+(ibox626 k).hi := by decide +kernel
private theorem accepted_626 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox626) tree626 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox626 midpoint_even_626
  simp only [tree626,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox626,candidate_valid h (FixedTape.midBox ibox626),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox626 212 (FixedTape.rowsAux denominator ibox626 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox626) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_626
private noncomputable def tree625 : TapeTree := .split 3 (((4781391013124241642840694968107160744807628800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree626 tree627
attribute [irreducible] tree625
private theorem accepted_625 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox625) tree625 = true := by
  simp only [tree625,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox625 3 (4781391013124241642840694968107160744807628800000000000000 : Int) false,decode_split denominator ibox625 3 (4781391013124241642840694968107160744807628800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_626 h,accepted_627 h⟩
private noncomputable def tree624 : TapeTree := .centered (candidateRows ibox624) (candidateRows (FixedTape.midBox ibox624))
attribute [irreducible] tree624
private theorem sign_624 : 2*denominator*(computed denominator (FixedTape.midBox ibox624)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox624).gradient k).lo.natAbs ((computed denominator ibox624).gradient k).hi.natAbs : Int)*((ibox624 k).hi-(ibox624 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox624
    (computed denominator ibox624) (computed denominator (FixedTape.midBox ibox624))
    (by decide +kernel)
private theorem midpoint_even_624 : ∀ k, 2 ∣ (ibox624 k).lo+(ibox624 k).hi := by decide +kernel
private theorem accepted_624 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox624) tree624 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox624 midpoint_even_624
  simp only [tree624,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox624,candidate_valid h (FixedTape.midBox ibox624),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox624 212 (FixedTape.rowsAux denominator ibox624 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox624) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_624
private noncomputable def tree623 : TapeTree := .centered (candidateRows ibox623) (candidateRows (FixedTape.midBox ibox623))
attribute [irreducible] tree623
private theorem sign_623 : 2*denominator*(computed denominator (FixedTape.midBox ibox623)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox623).gradient k).lo.natAbs ((computed denominator ibox623).gradient k).hi.natAbs : Int)*((ibox623 k).hi-(ibox623 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox623
    (computed denominator ibox623) (computed denominator (FixedTape.midBox ibox623))
    (by decide +kernel)
private theorem midpoint_even_623 : ∀ k, 2 ∣ (ibox623 k).lo+(ibox623 k).hi := by decide +kernel
private theorem accepted_623 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox623) tree623 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox623 midpoint_even_623
  simp only [tree623,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox623,candidate_valid h (FixedTape.midBox ibox623),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox623 212 (FixedTape.rowsAux denominator ibox623 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox623) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_623
private noncomputable def tree622 : TapeTree := .split 3 (((4781391013124241642840694968107160744807628800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree623 tree624
attribute [irreducible] tree622
private theorem accepted_622 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox622) tree622 = true := by
  simp only [tree622,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox622 3 (4781391013124241642840694968107160744807628800000000000000 : Int) false,decode_split denominator ibox622 3 (4781391013124241642840694968107160744807628800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_623 h,accepted_624 h⟩
private noncomputable def tree621 : TapeTree := .split 0 (((9700994110221605895669753775136169104894853120000000000 : Int) : ℚ)/(denominator : ℚ)) tree622 tree625
attribute [irreducible] tree621
private theorem accepted_621 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox621) tree621 = true := by
  simp only [tree621,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox621 0 (9700994110221605895669753775136169104894853120000000000 : Int) false,decode_split denominator ibox621 0 (9700994110221605895669753775136169104894853120000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_622 h,accepted_625 h⟩
private noncomputable def tree620 : TapeTree := .split 3 (((5737669215749089971408833961728592893769154560000000000000 : Int) : ℚ)/(denominator : ℚ)) tree621 tree628
attribute [irreducible] tree620
private theorem accepted_620 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox620) tree620 = true := by
  simp only [tree620,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox620 3 (5737669215749089971408833961728592893769154560000000000000 : Int) false,decode_split denominator ibox620 3 (5737669215749089971408833961728592893769154560000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_621 h,accepted_628 h⟩
private noncomputable def tree619 : TapeTree := .split 0 (((9884031734942768271059749129384021352157020160000000000 : Int) : ℚ)/(denominator : ℚ)) tree620 tree635
attribute [irreducible] tree619
private theorem accepted_619 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox619) tree619 = true := by
  simp only [tree619,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox619 0 (9884031734942768271059749129384021352157020160000000000 : Int) false,decode_split denominator ibox619 0 (9884031734942768271059749129384021352157020160000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_620 h,accepted_635 h⟩
private noncomputable def tree618 : TapeTree := .centered (candidateRows ibox618) (candidateRows (FixedTape.midBox ibox618))
attribute [irreducible] tree618
private theorem sign_618 : 2*denominator*(computed denominator (FixedTape.midBox ibox618)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox618).gradient k).lo.natAbs ((computed denominator ibox618).gradient k).hi.natAbs : Int)*((ibox618 k).hi-(ibox618 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox618
    (computed denominator ibox618) (computed denominator (FixedTape.midBox ibox618))
    (by decide +kernel)
private theorem midpoint_even_618 : ∀ k, 2 ∣ (ibox618 k).lo+(ibox618 k).hi := by decide +kernel
private theorem accepted_618 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox618) tree618 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox618 midpoint_even_618
  simp only [tree618,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox618,candidate_valid h (FixedTape.midBox ibox618),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox618 212 (FixedTape.rowsAux denominator ibox618 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox618) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_618
private noncomputable def tree617 : TapeTree := .centered (candidateRows ibox617) (candidateRows (FixedTape.midBox ibox617))
attribute [irreducible] tree617
private theorem sign_617 : 2*denominator*(computed denominator (FixedTape.midBox ibox617)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox617).gradient k).lo.natAbs ((computed denominator ibox617).gradient k).hi.natAbs : Int)*((ibox617 k).hi-(ibox617 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox617
    (computed denominator ibox617) (computed denominator (FixedTape.midBox ibox617))
    (by decide +kernel)
private theorem midpoint_even_617 : ∀ k, 2 ∣ (ibox617 k).lo+(ibox617 k).hi := by decide +kernel
private theorem accepted_617 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox617) tree617 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox617 midpoint_even_617
  simp only [tree617,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox617,candidate_valid h (FixedTape.midBox ibox617),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox617 212 (FixedTape.rowsAux denominator ibox617 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox617) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_617
private noncomputable def tree616 : TapeTree := .split 3 (((2868834607874544985704416980864296446884577280000000000000 : Int) : ℚ)/(denominator : ℚ)) tree617 tree618
attribute [irreducible] tree616
private theorem accepted_616 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox616) tree616 = true := by
  simp only [tree616,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox616 3 (2868834607874544985704416980864296446884577280000000000000 : Int) false,decode_split denominator ibox616 3 (2868834607874544985704416980864296446884577280000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_617 h,accepted_618 h⟩
private noncomputable def tree615 : TapeTree := .centered (candidateRows ibox615) (candidateRows (FixedTape.midBox ibox615))
attribute [irreducible] tree615
private theorem sign_615 : 2*denominator*(computed denominator (FixedTape.midBox ibox615)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox615).gradient k).lo.natAbs ((computed denominator ibox615).gradient k).hi.natAbs : Int)*((ibox615 k).hi-(ibox615 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox615
    (computed denominator ibox615) (computed denominator (FixedTape.midBox ibox615))
    (by decide +kernel)
private theorem midpoint_even_615 : ∀ k, 2 ∣ (ibox615 k).lo+(ibox615 k).hi := by decide +kernel
private theorem accepted_615 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox615) tree615 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox615 midpoint_even_615
  simp only [tree615,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox615,candidate_valid h (FixedTape.midBox ibox615),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox615 212 (FixedTape.rowsAux denominator ibox615 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox615) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_615
private noncomputable def tree614 : TapeTree := .centered (candidateRows ibox614) (candidateRows (FixedTape.midBox ibox614))
attribute [irreducible] tree614
private theorem sign_614 : 2*denominator*(computed denominator (FixedTape.midBox ibox614)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox614).gradient k).lo.natAbs ((computed denominator ibox614).gradient k).hi.natAbs : Int)*((ibox614 k).hi-(ibox614 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox614
    (computed denominator ibox614) (computed denominator (FixedTape.midBox ibox614))
    (by decide +kernel)
private theorem midpoint_even_614 : ∀ k, 2 ∣ (ibox614 k).lo+(ibox614 k).hi := by decide +kernel
private theorem accepted_614 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox614) tree614 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox614 midpoint_even_614
  simp only [tree614,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox614,candidate_valid h (FixedTape.midBox ibox614),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox614 212 (FixedTape.rowsAux denominator ibox614 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox614) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_614
private noncomputable def tree613 : TapeTree := .split 3 (((2868834607874544985704416980864296446884577280000000000000 : Int) : ℚ)/(denominator : ℚ)) tree614 tree615
attribute [irreducible] tree613
private theorem accepted_613 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox613) tree613 = true := by
  simp only [tree613,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox613 3 (2868834607874544985704416980864296446884577280000000000000 : Int) false,decode_split denominator ibox613 3 (2868834607874544985704416980864296446884577280000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_614 h,accepted_615 h⟩
private noncomputable def tree612 : TapeTree := .split 0 (((10067069359663930646449744483631873599419187200000000000 : Int) : ℚ)/(denominator : ℚ)) tree613 tree616
attribute [irreducible] tree612
private theorem accepted_612 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox612) tree612 = true := by
  simp only [tree612,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox612 0 (10067069359663930646449744483631873599419187200000000000 : Int) false,decode_split denominator ibox612 0 (10067069359663930646449744483631873599419187200000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_613 h,accepted_616 h⟩
private noncomputable def tree611 : TapeTree := .centered (candidateRows ibox611) (candidateRows (FixedTape.midBox ibox611))
attribute [irreducible] tree611
private theorem sign_611 : 2*denominator*(computed denominator (FixedTape.midBox ibox611)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox611).gradient k).lo.natAbs ((computed denominator ibox611).gradient k).hi.natAbs : Int)*((ibox611 k).hi-(ibox611 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox611
    (computed denominator ibox611) (computed denominator (FixedTape.midBox ibox611))
    (by decide +kernel)
private theorem midpoint_even_611 : ∀ k, 2 ∣ (ibox611 k).lo+(ibox611 k).hi := by decide +kernel
private theorem accepted_611 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox611) tree611 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox611 midpoint_even_611
  simp only [tree611,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox611,candidate_valid h (FixedTape.midBox ibox611),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox611 212 (FixedTape.rowsAux denominator ibox611 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox611) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_611
private noncomputable def tree610 : TapeTree := .centered (candidateRows ibox610) (candidateRows (FixedTape.midBox ibox610))
attribute [irreducible] tree610
private theorem sign_610 : 2*denominator*(computed denominator (FixedTape.midBox ibox610)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox610).gradient k).lo.natAbs ((computed denominator ibox610).gradient k).hi.natAbs : Int)*((ibox610 k).hi-(ibox610 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox610
    (computed denominator ibox610) (computed denominator (FixedTape.midBox ibox610))
    (by decide +kernel)
private theorem midpoint_even_610 : ∀ k, 2 ∣ (ibox610 k).lo+(ibox610 k).hi := by decide +kernel
private theorem accepted_610 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox610) tree610 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox610 midpoint_even_610
  simp only [tree610,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox610,candidate_valid h (FixedTape.midBox ibox610),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox610 212 (FixedTape.rowsAux denominator ibox610 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox610) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_610
private noncomputable def tree609 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree610 tree611
attribute [irreducible] tree609
private theorem accepted_609 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox609) tree609 = true := by
  simp only [tree609,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox609 3 (956278202624848328568138993621432148961525760000000000000 : Int) false,decode_split denominator ibox609 3 (956278202624848328568138993621432148961525760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_610 h,accepted_611 h⟩
private noncomputable def tree608 : TapeTree := .centered (candidateRows ibox608) (candidateRows (FixedTape.midBox ibox608))
attribute [irreducible] tree608
private theorem sign_608 : 2*denominator*(computed denominator (FixedTape.midBox ibox608)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox608).gradient k).lo.natAbs ((computed denominator ibox608).gradient k).hi.natAbs : Int)*((ibox608 k).hi-(ibox608 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox608
    (computed denominator ibox608) (computed denominator (FixedTape.midBox ibox608))
    (by decide +kernel)
private theorem midpoint_even_608 : ∀ k, 2 ∣ (ibox608 k).lo+(ibox608 k).hi := by decide +kernel
private theorem accepted_608 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox608) tree608 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox608 midpoint_even_608
  simp only [tree608,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox608,candidate_valid h (FixedTape.midBox ibox608),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox608 212 (FixedTape.rowsAux denominator ibox608 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox608) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_608
private noncomputable def tree607 : TapeTree := .centered (candidateRows ibox607) (candidateRows (FixedTape.midBox ibox607))
attribute [irreducible] tree607
private theorem sign_607 : 2*denominator*(computed denominator (FixedTape.midBox ibox607)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox607).gradient k).lo.natAbs ((computed denominator ibox607).gradient k).hi.natAbs : Int)*((ibox607 k).hi-(ibox607 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox607
    (computed denominator ibox607) (computed denominator (FixedTape.midBox ibox607))
    (by decide +kernel)
private theorem midpoint_even_607 : ∀ k, 2 ∣ (ibox607 k).lo+(ibox607 k).hi := by decide +kernel
private theorem accepted_607 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox607) tree607 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox607 midpoint_even_607
  simp only [tree607,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox607,candidate_valid h (FixedTape.midBox ibox607),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox607 212 (FixedTape.rowsAux denominator ibox607 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox607) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_607
private noncomputable def tree606 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree607 tree608
attribute [irreducible] tree606
private theorem accepted_606 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox606) tree606 = true := by
  simp only [tree606,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox606 3 (956278202624848328568138993621432148961525760000000000000 : Int) false,decode_split denominator ibox606 3 (956278202624848328568138993621432148961525760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_607 h,accepted_608 h⟩
private noncomputable def tree605 : TapeTree := .split 0 (((10067069359663930646449744483631873599419187200000000000 : Int) : ℚ)/(denominator : ℚ)) tree606 tree609
attribute [irreducible] tree605
private theorem accepted_605 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox605) tree605 = true := by
  simp only [tree605,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox605 0 (10067069359663930646449744483631873599419187200000000000 : Int) false,decode_split denominator ibox605 0 (10067069359663930646449744483631873599419187200000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_606 h,accepted_609 h⟩
private noncomputable def tree604 : TapeTree := .split 3 (((1912556405249696657136277987242864297923051520000000000000 : Int) : ℚ)/(denominator : ℚ)) tree605 tree612
attribute [irreducible] tree604
private theorem accepted_604 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox604) tree604 = true := by
  simp only [tree604,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox604 3 (1912556405249696657136277987242864297923051520000000000000 : Int) false,decode_split denominator ibox604 3 (1912556405249696657136277987242864297923051520000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_605 h,accepted_612 h⟩
private noncomputable def tree603 : TapeTree := .centered (candidateRows ibox603) (candidateRows (FixedTape.midBox ibox603))
attribute [irreducible] tree603
private theorem sign_603 : 2*denominator*(computed denominator (FixedTape.midBox ibox603)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox603).gradient k).lo.natAbs ((computed denominator ibox603).gradient k).hi.natAbs : Int)*((ibox603 k).hi-(ibox603 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox603
    (computed denominator ibox603) (computed denominator (FixedTape.midBox ibox603))
    (by decide +kernel)
private theorem midpoint_even_603 : ∀ k, 2 ∣ (ibox603 k).lo+(ibox603 k).hi := by decide +kernel
private theorem accepted_603 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox603) tree603 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox603 midpoint_even_603
  simp only [tree603,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox603,candidate_valid h (FixedTape.midBox ibox603),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox603 212 (FixedTape.rowsAux denominator ibox603 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox603) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_603
private noncomputable def tree602 : TapeTree := .centered (candidateRows ibox602) (candidateRows (FixedTape.midBox ibox602))
attribute [irreducible] tree602
private theorem sign_602 : 2*denominator*(computed denominator (FixedTape.midBox ibox602)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox602).gradient k).lo.natAbs ((computed denominator ibox602).gradient k).hi.natAbs : Int)*((ibox602 k).hi-(ibox602 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox602
    (computed denominator ibox602) (computed denominator (FixedTape.midBox ibox602))
    (by decide +kernel)
private theorem midpoint_even_602 : ∀ k, 2 ∣ (ibox602 k).lo+(ibox602 k).hi := by decide +kernel
private theorem accepted_602 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox602) tree602 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox602 midpoint_even_602
  simp only [tree602,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox602,candidate_valid h (FixedTape.midBox ibox602),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox602 212 (FixedTape.rowsAux denominator ibox602 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox602) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_602
private noncomputable def tree601 : TapeTree := .split 3 (((2868834607874544985704416980864296446884577280000000000000 : Int) : ℚ)/(denominator : ℚ)) tree602 tree603
attribute [irreducible] tree601
private theorem accepted_601 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox601) tree601 = true := by
  simp only [tree601,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox601 3 (2868834607874544985704416980864296446884577280000000000000 : Int) false,decode_split denominator ibox601 3 (2868834607874544985704416980864296446884577280000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_602 h,accepted_603 h⟩
private noncomputable def tree600 : TapeTree := .centered (candidateRows ibox600) (candidateRows (FixedTape.midBox ibox600))
attribute [irreducible] tree600
private theorem sign_600 : 2*denominator*(computed denominator (FixedTape.midBox ibox600)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox600).gradient k).lo.natAbs ((computed denominator ibox600).gradient k).hi.natAbs : Int)*((ibox600 k).hi-(ibox600 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox600
    (computed denominator ibox600) (computed denominator (FixedTape.midBox ibox600))
    (by decide +kernel)
private theorem midpoint_even_600 : ∀ k, 2 ∣ (ibox600 k).lo+(ibox600 k).hi := by decide +kernel
private theorem accepted_600 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox600) tree600 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox600 midpoint_even_600
  simp only [tree600,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox600,candidate_valid h (FixedTape.midBox ibox600),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox600 212 (FixedTape.rowsAux denominator ibox600 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox600) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_600
private noncomputable def tree599 : TapeTree := .centered (candidateRows ibox599) (candidateRows (FixedTape.midBox ibox599))
attribute [irreducible] tree599
private theorem sign_599 : 2*denominator*(computed denominator (FixedTape.midBox ibox599)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox599).gradient k).lo.natAbs ((computed denominator ibox599).gradient k).hi.natAbs : Int)*((ibox599 k).hi-(ibox599 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox599
    (computed denominator ibox599) (computed denominator (FixedTape.midBox ibox599))
    (by decide +kernel)
private theorem midpoint_even_599 : ∀ k, 2 ∣ (ibox599 k).lo+(ibox599 k).hi := by decide +kernel
private theorem accepted_599 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox599) tree599 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox599 midpoint_even_599
  simp only [tree599,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox599,candidate_valid h (FixedTape.midBox ibox599),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox599 212 (FixedTape.rowsAux denominator ibox599 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox599) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_599
private noncomputable def tree598 : TapeTree := .split 3 (((2868834607874544985704416980864296446884577280000000000000 : Int) : ℚ)/(denominator : ℚ)) tree599 tree600
attribute [irreducible] tree598
private theorem accepted_598 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox598) tree598 = true := by
  simp only [tree598,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox598 3 (2868834607874544985704416980864296446884577280000000000000 : Int) false,decode_split denominator ibox598 3 (2868834607874544985704416980864296446884577280000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_599 h,accepted_600 h⟩
private noncomputable def tree597 : TapeTree := .split 0 (((9700994110221605895669753775136169104894853120000000000 : Int) : ℚ)/(denominator : ℚ)) tree598 tree601
attribute [irreducible] tree597
private theorem accepted_597 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox597) tree597 = true := by
  simp only [tree597,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox597 0 (9700994110221605895669753775136169104894853120000000000 : Int) false,decode_split denominator ibox597 0 (9700994110221605895669753775136169104894853120000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_598 h,accepted_601 h⟩
private noncomputable def tree596 : TapeTree := .centered (candidateRows ibox596) (candidateRows (FixedTape.midBox ibox596))
attribute [irreducible] tree596
private theorem sign_596 : 2*denominator*(computed denominator (FixedTape.midBox ibox596)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox596).gradient k).lo.natAbs ((computed denominator ibox596).gradient k).hi.natAbs : Int)*((ibox596 k).hi-(ibox596 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox596
    (computed denominator ibox596) (computed denominator (FixedTape.midBox ibox596))
    (by decide +kernel)
private theorem midpoint_even_596 : ∀ k, 2 ∣ (ibox596 k).lo+(ibox596 k).hi := by decide +kernel
private theorem accepted_596 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox596) tree596 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox596 midpoint_even_596
  simp only [tree596,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox596,candidate_valid h (FixedTape.midBox ibox596),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox596 212 (FixedTape.rowsAux denominator ibox596 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox596) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_596
private noncomputable def tree595 : TapeTree := .centered (candidateRows ibox595) (candidateRows (FixedTape.midBox ibox595))
attribute [irreducible] tree595
private theorem sign_595 : 2*denominator*(computed denominator (FixedTape.midBox ibox595)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox595).gradient k).lo.natAbs ((computed denominator ibox595).gradient k).hi.natAbs : Int)*((ibox595 k).hi-(ibox595 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox595
    (computed denominator ibox595) (computed denominator (FixedTape.midBox ibox595))
    (by decide +kernel)
private theorem midpoint_even_595 : ∀ k, 2 ∣ (ibox595 k).lo+(ibox595 k).hi := by decide +kernel
private theorem accepted_595 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox595) tree595 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox595 midpoint_even_595
  simp only [tree595,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox595,candidate_valid h (FixedTape.midBox ibox595),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox595 212 (FixedTape.rowsAux denominator ibox595 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox595) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_595
private noncomputable def tree594 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree595 tree596
attribute [irreducible] tree594
private theorem accepted_594 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox594) tree594 = true := by
  simp only [tree594,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox594 3 (956278202624848328568138993621432148961525760000000000000 : Int) false,decode_split denominator ibox594 3 (956278202624848328568138993621432148961525760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_595 h,accepted_596 h⟩
private noncomputable def tree593 : TapeTree := .centered (candidateRows ibox593) (candidateRows (FixedTape.midBox ibox593))
attribute [irreducible] tree593
private theorem sign_593 : 2*denominator*(computed denominator (FixedTape.midBox ibox593)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox593).gradient k).lo.natAbs ((computed denominator ibox593).gradient k).hi.natAbs : Int)*((ibox593 k).hi-(ibox593 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox593
    (computed denominator ibox593) (computed denominator (FixedTape.midBox ibox593))
    (by decide +kernel)
private theorem midpoint_even_593 : ∀ k, 2 ∣ (ibox593 k).lo+(ibox593 k).hi := by decide +kernel
private theorem accepted_593 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox593) tree593 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox593 midpoint_even_593
  simp only [tree593,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox593,candidate_valid h (FixedTape.midBox ibox593),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox593 212 (FixedTape.rowsAux denominator ibox593 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox593) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_593
private noncomputable def tree592 : TapeTree := .centered (candidateRows ibox592) (candidateRows (FixedTape.midBox ibox592))
attribute [irreducible] tree592
private theorem sign_592 : 2*denominator*(computed denominator (FixedTape.midBox ibox592)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox592).gradient k).lo.natAbs ((computed denominator ibox592).gradient k).hi.natAbs : Int)*((ibox592 k).hi-(ibox592 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox592
    (computed denominator ibox592) (computed denominator (FixedTape.midBox ibox592))
    (by decide +kernel)
private theorem midpoint_even_592 : ∀ k, 2 ∣ (ibox592 k).lo+(ibox592 k).hi := by decide +kernel
private theorem accepted_592 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox592) tree592 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox592 midpoint_even_592
  simp only [tree592,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox592,candidate_valid h (FixedTape.midBox ibox592),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox592 212 (FixedTape.rowsAux denominator ibox592 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox592) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_592
private noncomputable def tree591 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree592 tree593
attribute [irreducible] tree591
private theorem accepted_591 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox591) tree591 = true := by
  simp only [tree591,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox591 3 (956278202624848328568138993621432148961525760000000000000 : Int) false,decode_split denominator ibox591 3 (956278202624848328568138993621432148961525760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_592 h,accepted_593 h⟩
private noncomputable def tree590 : TapeTree := .split 0 (((9700994110221605895669753775136169104894853120000000000 : Int) : ℚ)/(denominator : ℚ)) tree591 tree594
attribute [irreducible] tree590
private theorem accepted_590 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox590) tree590 = true := by
  simp only [tree590,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox590 0 (9700994110221605895669753775136169104894853120000000000 : Int) false,decode_split denominator ibox590 0 (9700994110221605895669753775136169104894853120000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_591 h,accepted_594 h⟩
private noncomputable def tree589 : TapeTree := .split 3 (((1912556405249696657136277987242864297923051520000000000000 : Int) : ℚ)/(denominator : ℚ)) tree590 tree597
attribute [irreducible] tree589
private theorem accepted_589 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox589) tree589 = true := by
  simp only [tree589,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox589 3 (1912556405249696657136277987242864297923051520000000000000 : Int) false,decode_split denominator ibox589 3 (1912556405249696657136277987242864297923051520000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_590 h,accepted_597 h⟩
private noncomputable def tree588 : TapeTree := .split 0 (((9884031734942768271059749129384021352157020160000000000 : Int) : ℚ)/(denominator : ℚ)) tree589 tree604
attribute [irreducible] tree588
private theorem accepted_588 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox588) tree588 = true := by
  simp only [tree588,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox588 0 (9884031734942768271059749129384021352157020160000000000 : Int) false,decode_split denominator ibox588 0 (9884031734942768271059749129384021352157020160000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_589 h,accepted_604 h⟩
private noncomputable def tree587 : TapeTree := .split 3 (((3825112810499393314272555974485728595846103040000000000000 : Int) : ℚ)/(denominator : ℚ)) tree588 tree619
attribute [irreducible] tree587
private theorem accepted_587 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox587) tree587 = true := by
  simp only [tree587,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox587 3 (3825112810499393314272555974485728595846103040000000000000 : Int) false,decode_split denominator ibox587 3 (3825112810499393314272555974485728595846103040000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_588 h,accepted_619 h⟩
private noncomputable def tree586 : TapeTree := .split 3 (((7650225620998786628545111948971457191692206080000000000000 : Int) : ℚ)/(denominator : ℚ)) tree587 tree650
attribute [irreducible] tree586
private theorem accepted_586 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox586) tree586 = true := by
  simp only [tree586,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox586 3 (7650225620998786628545111948971457191692206080000000000000 : Int) false,decode_split denominator ibox586 3 (7650225620998786628545111948971457191692206080000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_587 h,accepted_650 h⟩
private noncomputable def tree585 : TapeTree := .face 1 false (candidateRows ibox585) tree586
attribute [irreducible] tree585
private theorem sign_585 : ((computed denominator ibox585).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_585 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox585) tree585 = true := by
  simp only [tree585,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox585,?_,accepted_586 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox585)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox585).gradient 1).hi) denominator_positive).1 sign_585
private noncomputable def tree584 : TapeTree := .centered (candidateRows ibox584) (candidateRows (FixedTape.midBox ibox584))
attribute [irreducible] tree584
private theorem sign_584 : 2*denominator*(computed denominator (FixedTape.midBox ibox584)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox584).gradient k).lo.natAbs ((computed denominator ibox584).gradient k).hi.natAbs : Int)*((ibox584 k).hi-(ibox584 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox584
    (computed denominator ibox584) (computed denominator (FixedTape.midBox ibox584))
    (by decide +kernel)
private theorem midpoint_even_584 : ∀ k, 2 ∣ (ibox584 k).lo+(ibox584 k).hi := by decide +kernel
private theorem accepted_584 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox584) tree584 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox584 midpoint_even_584
  simp only [tree584,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox584,candidate_valid h (FixedTape.midBox ibox584),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox584 212 (FixedTape.rowsAux denominator ibox584 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox584) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_584
private noncomputable def tree583 : TapeTree := .centered (candidateRows ibox583) (candidateRows (FixedTape.midBox ibox583))
attribute [irreducible] tree583
private theorem sign_583 : 2*denominator*(computed denominator (FixedTape.midBox ibox583)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox583).gradient k).lo.natAbs ((computed denominator ibox583).gradient k).hi.natAbs : Int)*((ibox583 k).hi-(ibox583 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox583
    (computed denominator ibox583) (computed denominator (FixedTape.midBox ibox583))
    (by decide +kernel)
private theorem midpoint_even_583 : ∀ k, 2 ∣ (ibox583 k).lo+(ibox583 k).hi := by decide +kernel
private theorem accepted_583 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox583) tree583 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox583 midpoint_even_583
  simp only [tree583,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox583,candidate_valid h (FixedTape.midBox ibox583),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox583 212 (FixedTape.rowsAux denominator ibox583 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox583) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_583
private noncomputable def tree582 : TapeTree := .split 0 (((9334918860779281144889763066640464610370519040000000000 : Int) : ℚ)/(denominator : ℚ)) tree583 tree584
attribute [irreducible] tree582
private theorem accepted_582 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox582) tree582 = true := by
  simp only [tree582,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox582 0 (9334918860779281144889763066640464610370519040000000000 : Int) false,decode_split denominator ibox582 0 (9334918860779281144889763066640464610370519040000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_583 h,accepted_584 h⟩
private noncomputable def tree581 : TapeTree := .centered (candidateRows ibox581) (candidateRows (FixedTape.midBox ibox581))
attribute [irreducible] tree581
private theorem sign_581 : 2*denominator*(computed denominator (FixedTape.midBox ibox581)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox581).gradient k).lo.natAbs ((computed denominator ibox581).gradient k).hi.natAbs : Int)*((ibox581 k).hi-(ibox581 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox581
    (computed denominator ibox581) (computed denominator (FixedTape.midBox ibox581))
    (by decide +kernel)
private theorem midpoint_even_581 : ∀ k, 2 ∣ (ibox581 k).lo+(ibox581 k).hi := by decide +kernel
private theorem accepted_581 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox581) tree581 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox581 midpoint_even_581
  simp only [tree581,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox581,candidate_valid h (FixedTape.midBox ibox581),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox581 212 (FixedTape.rowsAux denominator ibox581 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox581) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_581
private noncomputable def tree580 : TapeTree := .centered (candidateRows ibox580) (candidateRows (FixedTape.midBox ibox580))
attribute [irreducible] tree580
private theorem sign_580 : 2*denominator*(computed denominator (FixedTape.midBox ibox580)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox580).gradient k).lo.natAbs ((computed denominator ibox580).gradient k).hi.natAbs : Int)*((ibox580 k).hi-(ibox580 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox580
    (computed denominator ibox580) (computed denominator (FixedTape.midBox ibox580))
    (by decide +kernel)
private theorem midpoint_even_580 : ∀ k, 2 ∣ (ibox580 k).lo+(ibox580 k).hi := by decide +kernel
private theorem accepted_580 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox580) tree580 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox580 midpoint_even_580
  simp only [tree580,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox580,candidate_valid h (FixedTape.midBox ibox580),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox580 212 (FixedTape.rowsAux denominator ibox580 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox580) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_580
private noncomputable def tree579 : TapeTree := .split 0 (((9334918860779281144889763066640464610370519040000000000 : Int) : ℚ)/(denominator : ℚ)) tree580 tree581
attribute [irreducible] tree579
private theorem accepted_579 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox579) tree579 = true := by
  simp only [tree579,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox579 0 (9334918860779281144889763066640464610370519040000000000 : Int) false,decode_split denominator ibox579 0 (9334918860779281144889763066640464610370519040000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_580 h,accepted_581 h⟩
private noncomputable def tree578 : TapeTree := .split 3 (((14344173039372724928522084904321482234422886400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree579 tree582
attribute [irreducible] tree578
private theorem accepted_578 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox578) tree578 = true := by
  simp only [tree578,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox578 3 (14344173039372724928522084904321482234422886400000000000000 : Int) false,decode_split denominator ibox578 3 (14344173039372724928522084904321482234422886400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_579 h,accepted_582 h⟩
private noncomputable def tree577 : TapeTree := .centered (candidateRows ibox577) (candidateRows (FixedTape.midBox ibox577))
attribute [irreducible] tree577
private theorem sign_577 : 2*denominator*(computed denominator (FixedTape.midBox ibox577)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox577).gradient k).lo.natAbs ((computed denominator ibox577).gradient k).hi.natAbs : Int)*((ibox577 k).hi-(ibox577 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox577
    (computed denominator ibox577) (computed denominator (FixedTape.midBox ibox577))
    (by decide +kernel)
private theorem midpoint_even_577 : ∀ k, 2 ∣ (ibox577 k).lo+(ibox577 k).hi := by decide +kernel
private theorem accepted_577 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox577) tree577 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox577 midpoint_even_577
  simp only [tree577,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox577,candidate_valid h (FixedTape.midBox ibox577),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox577 212 (FixedTape.rowsAux denominator ibox577 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox577) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_577
private noncomputable def tree576 : TapeTree := .centered (candidateRows ibox576) (candidateRows (FixedTape.midBox ibox576))
attribute [irreducible] tree576
private theorem sign_576 : 2*denominator*(computed denominator (FixedTape.midBox ibox576)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox576).gradient k).lo.natAbs ((computed denominator ibox576).gradient k).hi.natAbs : Int)*((ibox576 k).hi-(ibox576 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox576
    (computed denominator ibox576) (computed denominator (FixedTape.midBox ibox576))
    (by decide +kernel)
private theorem midpoint_even_576 : ∀ k, 2 ∣ (ibox576 k).lo+(ibox576 k).hi := by decide +kernel
private theorem accepted_576 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox576) tree576 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox576 midpoint_even_576
  simp only [tree576,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox576,candidate_valid h (FixedTape.midBox ibox576),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox576 212 (FixedTape.rowsAux denominator ibox576 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox576) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_576
private noncomputable def tree575 : TapeTree := .split 0 (((8968843611336956394109772358144760115846184960000000000 : Int) : ℚ)/(denominator : ℚ)) tree576 tree577
attribute [irreducible] tree575
private theorem accepted_575 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox575) tree575 = true := by
  simp only [tree575,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox575 0 (8968843611336956394109772358144760115846184960000000000 : Int) false,decode_split denominator ibox575 0 (8968843611336956394109772358144760115846184960000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_576 h,accepted_577 h⟩
private noncomputable def tree574 : TapeTree := .centered (candidateRows ibox574) (candidateRows (FixedTape.midBox ibox574))
attribute [irreducible] tree574
private theorem sign_574 : 2*denominator*(computed denominator (FixedTape.midBox ibox574)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox574).gradient k).lo.natAbs ((computed denominator ibox574).gradient k).hi.natAbs : Int)*((ibox574 k).hi-(ibox574 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox574
    (computed denominator ibox574) (computed denominator (FixedTape.midBox ibox574))
    (by decide +kernel)
private theorem midpoint_even_574 : ∀ k, 2 ∣ (ibox574 k).lo+(ibox574 k).hi := by decide +kernel
private theorem accepted_574 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox574) tree574 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox574 midpoint_even_574
  simp only [tree574,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox574,candidate_valid h (FixedTape.midBox ibox574),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox574 212 (FixedTape.rowsAux denominator ibox574 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox574) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_574
private noncomputable def tree573 : TapeTree := .centered (candidateRows ibox573) (candidateRows (FixedTape.midBox ibox573))
attribute [irreducible] tree573
private theorem sign_573 : 2*denominator*(computed denominator (FixedTape.midBox ibox573)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox573).gradient k).lo.natAbs ((computed denominator ibox573).gradient k).hi.natAbs : Int)*((ibox573 k).hi-(ibox573 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox573
    (computed denominator ibox573) (computed denominator (FixedTape.midBox ibox573))
    (by decide +kernel)
private theorem midpoint_even_573 : ∀ k, 2 ∣ (ibox573 k).lo+(ibox573 k).hi := by decide +kernel
private theorem accepted_573 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox573) tree573 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox573 midpoint_even_573
  simp only [tree573,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox573,candidate_valid h (FixedTape.midBox ibox573),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox573 212 (FixedTape.rowsAux denominator ibox573 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox573) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_573
private noncomputable def tree572 : TapeTree := .split 0 (((8968843611336956394109772358144760115846184960000000000 : Int) : ℚ)/(denominator : ℚ)) tree573 tree574
attribute [irreducible] tree572
private theorem accepted_572 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox572) tree572 = true := by
  simp only [tree572,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox572 0 (8968843611336956394109772358144760115846184960000000000 : Int) false,decode_split denominator ibox572 0 (8968843611336956394109772358144760115846184960000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_573 h,accepted_574 h⟩
private noncomputable def tree571 : TapeTree := .split 3 (((14344173039372724928522084904321482234422886400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree572 tree575
attribute [irreducible] tree571
private theorem accepted_571 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox571) tree571 = true := by
  simp only [tree571,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox571 3 (14344173039372724928522084904321482234422886400000000000000 : Int) false,decode_split denominator ibox571 3 (14344173039372724928522084904321482234422886400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_572 h,accepted_575 h⟩
private noncomputable def tree570 : TapeTree := .split 0 (((9151881236058118769499767712392612363108352000000000000 : Int) : ℚ)/(denominator : ℚ)) tree571 tree578
attribute [irreducible] tree570
private theorem accepted_570 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox570) tree570 = true := by
  simp only [tree570,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox570 0 (9151881236058118769499767712392612363108352000000000000 : Int) false,decode_split denominator ibox570 0 (9151881236058118769499767712392612363108352000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_571 h,accepted_578 h⟩
private noncomputable def tree569 : TapeTree := .centered (candidateRows ibox569) (candidateRows (FixedTape.midBox ibox569))
attribute [irreducible] tree569
private theorem sign_569 : 2*denominator*(computed denominator (FixedTape.midBox ibox569)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox569).gradient k).lo.natAbs ((computed denominator ibox569).gradient k).hi.natAbs : Int)*((ibox569 k).hi-(ibox569 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox569
    (computed denominator ibox569) (computed denominator (FixedTape.midBox ibox569))
    (by decide +kernel)
private theorem midpoint_even_569 : ∀ k, 2 ∣ (ibox569 k).lo+(ibox569 k).hi := by decide +kernel
private theorem accepted_569 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox569) tree569 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox569 midpoint_even_569
  simp only [tree569,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox569,candidate_valid h (FixedTape.midBox ibox569),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox569 212 (FixedTape.rowsAux denominator ibox569 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox569) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_569
private noncomputable def tree568 : TapeTree := .centered (candidateRows ibox568) (candidateRows (FixedTape.midBox ibox568))
attribute [irreducible] tree568
private theorem sign_568 : 2*denominator*(computed denominator (FixedTape.midBox ibox568)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox568).gradient k).lo.natAbs ((computed denominator ibox568).gradient k).hi.natAbs : Int)*((ibox568 k).hi-(ibox568 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox568
    (computed denominator ibox568) (computed denominator (FixedTape.midBox ibox568))
    (by decide +kernel)
private theorem midpoint_even_568 : ∀ k, 2 ∣ (ibox568 k).lo+(ibox568 k).hi := by decide +kernel
private theorem accepted_568 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox568) tree568 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox568 midpoint_even_568
  simp only [tree568,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox568,candidate_valid h (FixedTape.midBox ibox568),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox568 212 (FixedTape.rowsAux denominator ibox568 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox568) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_568
private noncomputable def tree567 : TapeTree := .split 0 (((9334918860779281144889763066640464610370519040000000000 : Int) : ℚ)/(denominator : ℚ)) tree568 tree569
attribute [irreducible] tree567
private theorem accepted_567 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox567) tree567 = true := by
  simp only [tree567,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox567 0 (9334918860779281144889763066640464610370519040000000000 : Int) false,decode_split denominator ibox567 0 (9334918860779281144889763066640464610370519040000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_568 h,accepted_569 h⟩
private noncomputable def tree566 : TapeTree := .centered (candidateRows ibox566) (candidateRows (FixedTape.midBox ibox566))
attribute [irreducible] tree566
private theorem sign_566 : 2*denominator*(computed denominator (FixedTape.midBox ibox566)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox566).gradient k).lo.natAbs ((computed denominator ibox566).gradient k).hi.natAbs : Int)*((ibox566 k).hi-(ibox566 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox566
    (computed denominator ibox566) (computed denominator (FixedTape.midBox ibox566))
    (by decide +kernel)
private theorem midpoint_even_566 : ∀ k, 2 ∣ (ibox566 k).lo+(ibox566 k).hi := by decide +kernel
private theorem accepted_566 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox566) tree566 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox566 midpoint_even_566
  simp only [tree566,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox566,candidate_valid h (FixedTape.midBox ibox566),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox566 212 (FixedTape.rowsAux denominator ibox566 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox566) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_566
private noncomputable def tree565 : TapeTree := .centered (candidateRows ibox565) (candidateRows (FixedTape.midBox ibox565))
attribute [irreducible] tree565
private theorem sign_565 : 2*denominator*(computed denominator (FixedTape.midBox ibox565)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox565).gradient k).lo.natAbs ((computed denominator ibox565).gradient k).hi.natAbs : Int)*((ibox565 k).hi-(ibox565 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox565
    (computed denominator ibox565) (computed denominator (FixedTape.midBox ibox565))
    (by decide +kernel)
private theorem midpoint_even_565 : ∀ k, 2 ∣ (ibox565 k).lo+(ibox565 k).hi := by decide +kernel
private theorem accepted_565 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox565) tree565 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox565 midpoint_even_565
  simp only [tree565,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox565,candidate_valid h (FixedTape.midBox ibox565),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox565 212 (FixedTape.rowsAux denominator ibox565 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox565) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_565
private noncomputable def tree564 : TapeTree := .split 0 (((9334918860779281144889763066640464610370519040000000000 : Int) : ℚ)/(denominator : ℚ)) tree565 tree566
attribute [irreducible] tree564
private theorem accepted_564 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox564) tree564 = true := by
  simp only [tree564,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox564 0 (9334918860779281144889763066640464610370519040000000000 : Int) false,decode_split denominator ibox564 0 (9334918860779281144889763066640464610370519040000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_565 h,accepted_566 h⟩
private noncomputable def tree563 : TapeTree := .split 3 (((12431616634123028271385806917078617936499834880000000000000 : Int) : ℚ)/(denominator : ℚ)) tree564 tree567
attribute [irreducible] tree563
private theorem accepted_563 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox563) tree563 = true := by
  simp only [tree563,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox563 3 (12431616634123028271385806917078617936499834880000000000000 : Int) false,decode_split denominator ibox563 3 (12431616634123028271385806917078617936499834880000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_564 h,accepted_567 h⟩
private noncomputable def tree562 : TapeTree := .centered (candidateRows ibox562) (candidateRows (FixedTape.midBox ibox562))
attribute [irreducible] tree562
private theorem sign_562 : 2*denominator*(computed denominator (FixedTape.midBox ibox562)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox562).gradient k).lo.natAbs ((computed denominator ibox562).gradient k).hi.natAbs : Int)*((ibox562 k).hi-(ibox562 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox562
    (computed denominator ibox562) (computed denominator (FixedTape.midBox ibox562))
    (by decide +kernel)
private theorem midpoint_even_562 : ∀ k, 2 ∣ (ibox562 k).lo+(ibox562 k).hi := by decide +kernel
private theorem accepted_562 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox562) tree562 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox562 midpoint_even_562
  simp only [tree562,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox562,candidate_valid h (FixedTape.midBox ibox562),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox562 212 (FixedTape.rowsAux denominator ibox562 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox562) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_562
private noncomputable def tree561 : TapeTree := .centered (candidateRows ibox561) (candidateRows (FixedTape.midBox ibox561))
attribute [irreducible] tree561
private theorem sign_561 : 2*denominator*(computed denominator (FixedTape.midBox ibox561)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox561).gradient k).lo.natAbs ((computed denominator ibox561).gradient k).hi.natAbs : Int)*((ibox561 k).hi-(ibox561 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox561
    (computed denominator ibox561) (computed denominator (FixedTape.midBox ibox561))
    (by decide +kernel)
private theorem midpoint_even_561 : ∀ k, 2 ∣ (ibox561 k).lo+(ibox561 k).hi := by decide +kernel
private theorem accepted_561 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox561) tree561 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox561 midpoint_even_561
  simp only [tree561,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox561,candidate_valid h (FixedTape.midBox ibox561),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox561 212 (FixedTape.rowsAux denominator ibox561 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox561) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_561
private noncomputable def tree560 : TapeTree := .split 0 (((8968843611336956394109772358144760115846184960000000000 : Int) : ℚ)/(denominator : ℚ)) tree561 tree562
attribute [irreducible] tree560
private theorem accepted_560 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox560) tree560 = true := by
  simp only [tree560,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox560 0 (8968843611336956394109772358144760115846184960000000000 : Int) false,decode_split denominator ibox560 0 (8968843611336956394109772358144760115846184960000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_561 h,accepted_562 h⟩
private noncomputable def tree559 : TapeTree := .centered (candidateRows ibox559) (candidateRows (FixedTape.midBox ibox559))
attribute [irreducible] tree559
private theorem sign_559 : 2*denominator*(computed denominator (FixedTape.midBox ibox559)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox559).gradient k).lo.natAbs ((computed denominator ibox559).gradient k).hi.natAbs : Int)*((ibox559 k).hi-(ibox559 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox559
    (computed denominator ibox559) (computed denominator (FixedTape.midBox ibox559))
    (by decide +kernel)
private theorem midpoint_even_559 : ∀ k, 2 ∣ (ibox559 k).lo+(ibox559 k).hi := by decide +kernel
private theorem accepted_559 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox559) tree559 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox559 midpoint_even_559
  simp only [tree559,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox559,candidate_valid h (FixedTape.midBox ibox559),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox559 212 (FixedTape.rowsAux denominator ibox559 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox559) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_559
private noncomputable def tree558 : TapeTree := .centered (candidateRows ibox558) (candidateRows (FixedTape.midBox ibox558))
attribute [irreducible] tree558
private theorem sign_558 : 2*denominator*(computed denominator (FixedTape.midBox ibox558)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox558).gradient k).lo.natAbs ((computed denominator ibox558).gradient k).hi.natAbs : Int)*((ibox558 k).hi-(ibox558 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox558
    (computed denominator ibox558) (computed denominator (FixedTape.midBox ibox558))
    (by decide +kernel)
private theorem midpoint_even_558 : ∀ k, 2 ∣ (ibox558 k).lo+(ibox558 k).hi := by decide +kernel
private theorem accepted_558 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox558) tree558 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox558 midpoint_even_558
  simp only [tree558,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox558,candidate_valid h (FixedTape.midBox ibox558),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox558 212 (FixedTape.rowsAux denominator ibox558 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox558) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_558
private noncomputable def tree557 : TapeTree := .split 0 (((8968843611336956394109772358144760115846184960000000000 : Int) : ℚ)/(denominator : ℚ)) tree558 tree559
attribute [irreducible] tree557
private theorem accepted_557 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox557) tree557 = true := by
  simp only [tree557,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox557 0 (8968843611336956394109772358144760115846184960000000000 : Int) false,decode_split denominator ibox557 0 (8968843611336956394109772358144760115846184960000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_558 h,accepted_559 h⟩
private noncomputable def tree556 : TapeTree := .split 3 (((12431616634123028271385806917078617936499834880000000000000 : Int) : ℚ)/(denominator : ℚ)) tree557 tree560
attribute [irreducible] tree556
private theorem accepted_556 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox556) tree556 = true := by
  simp only [tree556,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox556 3 (12431616634123028271385806917078617936499834880000000000000 : Int) false,decode_split denominator ibox556 3 (12431616634123028271385806917078617936499834880000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_557 h,accepted_560 h⟩
private noncomputable def tree555 : TapeTree := .split 0 (((9151881236058118769499767712392612363108352000000000000 : Int) : ℚ)/(denominator : ℚ)) tree556 tree563
attribute [irreducible] tree555
private theorem accepted_555 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox555) tree555 = true := by
  simp only [tree555,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox555 0 (9151881236058118769499767712392612363108352000000000000 : Int) false,decode_split denominator ibox555 0 (9151881236058118769499767712392612363108352000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_556 h,accepted_563 h⟩
private noncomputable def tree554 : TapeTree := .split 3 (((13387894836747876599953945910700050085461360640000000000000 : Int) : ℚ)/(denominator : ℚ)) tree555 tree570
attribute [irreducible] tree554
private theorem accepted_554 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox554) tree554 = true := by
  simp only [tree554,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox554 3 (13387894836747876599953945910700050085461360640000000000000 : Int) false,decode_split denominator ibox554 3 (13387894836747876599953945910700050085461360640000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_555 h,accepted_570 h⟩
private noncomputable def tree553 : TapeTree := .centered (candidateRows ibox553) (candidateRows (FixedTape.midBox ibox553))
attribute [irreducible] tree553
private theorem sign_553 : 2*denominator*(computed denominator (FixedTape.midBox ibox553)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox553).gradient k).lo.natAbs ((computed denominator ibox553).gradient k).hi.natAbs : Int)*((ibox553 k).hi-(ibox553 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox553
    (computed denominator ibox553) (computed denominator (FixedTape.midBox ibox553))
    (by decide +kernel)
private theorem midpoint_even_553 : ∀ k, 2 ∣ (ibox553 k).lo+(ibox553 k).hi := by decide +kernel
private theorem accepted_553 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox553) tree553 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox553 midpoint_even_553
  simp only [tree553,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox553,candidate_valid h (FixedTape.midBox ibox553),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox553 212 (FixedTape.rowsAux denominator ibox553 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox553) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_553
private noncomputable def tree552 : TapeTree := .centered (candidateRows ibox552) (candidateRows (FixedTape.midBox ibox552))
attribute [irreducible] tree552
private theorem sign_552 : 2*denominator*(computed denominator (FixedTape.midBox ibox552)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox552).gradient k).lo.natAbs ((computed denominator ibox552).gradient k).hi.natAbs : Int)*((ibox552 k).hi-(ibox552 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox552
    (computed denominator ibox552) (computed denominator (FixedTape.midBox ibox552))
    (by decide +kernel)
private theorem midpoint_even_552 : ∀ k, 2 ∣ (ibox552 k).lo+(ibox552 k).hi := by decide +kernel
private theorem accepted_552 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox552) tree552 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox552 midpoint_even_552
  simp only [tree552,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox552,candidate_valid h (FixedTape.midBox ibox552),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox552 212 (FixedTape.rowsAux denominator ibox552 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox552) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_552
private noncomputable def tree551 : TapeTree := .split 3 (((10519060228873331614249528929835753638576783360000000000000 : Int) : ℚ)/(denominator : ℚ)) tree552 tree553
attribute [irreducible] tree551
private theorem accepted_551 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox551) tree551 = true := by
  simp only [tree551,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox551 3 (10519060228873331614249528929835753638576783360000000000000 : Int) false,decode_split denominator ibox551 3 (10519060228873331614249528929835753638576783360000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_552 h,accepted_553 h⟩
private noncomputable def tree550 : TapeTree := .centered (candidateRows ibox550) (candidateRows (FixedTape.midBox ibox550))
attribute [irreducible] tree550
private theorem sign_550 : 2*denominator*(computed denominator (FixedTape.midBox ibox550)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox550).gradient k).lo.natAbs ((computed denominator ibox550).gradient k).hi.natAbs : Int)*((ibox550 k).hi-(ibox550 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox550
    (computed denominator ibox550) (computed denominator (FixedTape.midBox ibox550))
    (by decide +kernel)
private theorem midpoint_even_550 : ∀ k, 2 ∣ (ibox550 k).lo+(ibox550 k).hi := by decide +kernel
private theorem accepted_550 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox550) tree550 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox550 midpoint_even_550
  simp only [tree550,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox550,candidate_valid h (FixedTape.midBox ibox550),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox550 212 (FixedTape.rowsAux denominator ibox550 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox550) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_550
private noncomputable def tree549 : TapeTree := .centered (candidateRows ibox549) (candidateRows (FixedTape.midBox ibox549))
attribute [irreducible] tree549
private theorem sign_549 : 2*denominator*(computed denominator (FixedTape.midBox ibox549)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox549).gradient k).lo.natAbs ((computed denominator ibox549).gradient k).hi.natAbs : Int)*((ibox549 k).hi-(ibox549 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox549
    (computed denominator ibox549) (computed denominator (FixedTape.midBox ibox549))
    (by decide +kernel)
private theorem midpoint_even_549 : ∀ k, 2 ∣ (ibox549 k).lo+(ibox549 k).hi := by decide +kernel
private theorem accepted_549 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox549) tree549 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox549 midpoint_even_549
  simp only [tree549,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox549,candidate_valid h (FixedTape.midBox ibox549),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox549 212 (FixedTape.rowsAux denominator ibox549 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox549) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_549
private noncomputable def tree548 : TapeTree := .split 3 (((10519060228873331614249528929835753638576783360000000000000 : Int) : ℚ)/(denominator : ℚ)) tree549 tree550
attribute [irreducible] tree548
private theorem accepted_548 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox548) tree548 = true := by
  simp only [tree548,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox548 3 (10519060228873331614249528929835753638576783360000000000000 : Int) false,decode_split denominator ibox548 3 (10519060228873331614249528929835753638576783360000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_549 h,accepted_550 h⟩
private noncomputable def tree547 : TapeTree := .split 0 (((9334918860779281144889763066640464610370519040000000000 : Int) : ℚ)/(denominator : ℚ)) tree548 tree551
attribute [irreducible] tree547
private theorem accepted_547 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox547) tree547 = true := by
  simp only [tree547,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox547 0 (9334918860779281144889763066640464610370519040000000000 : Int) false,decode_split denominator ibox547 0 (9334918860779281144889763066640464610370519040000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_548 h,accepted_551 h⟩
private noncomputable def tree546 : TapeTree := .centered (candidateRows ibox546) (candidateRows (FixedTape.midBox ibox546))
attribute [irreducible] tree546
private theorem sign_546 : 2*denominator*(computed denominator (FixedTape.midBox ibox546)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox546).gradient k).lo.natAbs ((computed denominator ibox546).gradient k).hi.natAbs : Int)*((ibox546 k).hi-(ibox546 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox546
    (computed denominator ibox546) (computed denominator (FixedTape.midBox ibox546))
    (by decide +kernel)
private theorem midpoint_even_546 : ∀ k, 2 ∣ (ibox546 k).lo+(ibox546 k).hi := by decide +kernel
private theorem accepted_546 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox546) tree546 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox546 midpoint_even_546
  simp only [tree546,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox546,candidate_valid h (FixedTape.midBox ibox546),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox546 212 (FixedTape.rowsAux denominator ibox546 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox546) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_546
private noncomputable def tree545 : TapeTree := .centered (candidateRows ibox545) (candidateRows (FixedTape.midBox ibox545))
attribute [irreducible] tree545
private theorem sign_545 : 2*denominator*(computed denominator (FixedTape.midBox ibox545)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox545).gradient k).lo.natAbs ((computed denominator ibox545).gradient k).hi.natAbs : Int)*((ibox545 k).hi-(ibox545 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox545
    (computed denominator ibox545) (computed denominator (FixedTape.midBox ibox545))
    (by decide +kernel)
private theorem midpoint_even_545 : ∀ k, 2 ∣ (ibox545 k).lo+(ibox545 k).hi := by decide +kernel
private theorem accepted_545 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox545) tree545 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox545 midpoint_even_545
  simp only [tree545,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox545,candidate_valid h (FixedTape.midBox ibox545),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox545 212 (FixedTape.rowsAux denominator ibox545 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox545) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_545
private noncomputable def tree544 : TapeTree := .split 3 (((8606503823623634957113250942592889340653731840000000000000 : Int) : ℚ)/(denominator : ℚ)) tree545 tree546
attribute [irreducible] tree544
private theorem accepted_544 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox544) tree544 = true := by
  simp only [tree544,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox544 3 (8606503823623634957113250942592889340653731840000000000000 : Int) false,decode_split denominator ibox544 3 (8606503823623634957113250942592889340653731840000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_545 h,accepted_546 h⟩
private noncomputable def tree543 : TapeTree := .centered (candidateRows ibox543) (candidateRows (FixedTape.midBox ibox543))
attribute [irreducible] tree543
private theorem sign_543 : 2*denominator*(computed denominator (FixedTape.midBox ibox543)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox543).gradient k).lo.natAbs ((computed denominator ibox543).gradient k).hi.natAbs : Int)*((ibox543 k).hi-(ibox543 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox543
    (computed denominator ibox543) (computed denominator (FixedTape.midBox ibox543))
    (by decide +kernel)
private theorem midpoint_even_543 : ∀ k, 2 ∣ (ibox543 k).lo+(ibox543 k).hi := by decide +kernel
private theorem accepted_543 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox543) tree543 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox543 midpoint_even_543
  simp only [tree543,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox543,candidate_valid h (FixedTape.midBox ibox543),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox543 212 (FixedTape.rowsAux denominator ibox543 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox543) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_543
private noncomputable def tree542 : TapeTree := .centered (candidateRows ibox542) (candidateRows (FixedTape.midBox ibox542))
attribute [irreducible] tree542
private theorem sign_542 : 2*denominator*(computed denominator (FixedTape.midBox ibox542)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox542).gradient k).lo.natAbs ((computed denominator ibox542).gradient k).hi.natAbs : Int)*((ibox542 k).hi-(ibox542 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox542
    (computed denominator ibox542) (computed denominator (FixedTape.midBox ibox542))
    (by decide +kernel)
private theorem midpoint_even_542 : ∀ k, 2 ∣ (ibox542 k).lo+(ibox542 k).hi := by decide +kernel
private theorem accepted_542 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox542) tree542 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox542 midpoint_even_542
  simp only [tree542,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox542,candidate_valid h (FixedTape.midBox ibox542),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox542 212 (FixedTape.rowsAux denominator ibox542 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox542) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_542
private noncomputable def tree541 : TapeTree := .split 3 (((8606503823623634957113250942592889340653731840000000000000 : Int) : ℚ)/(denominator : ℚ)) tree542 tree543
attribute [irreducible] tree541
private theorem accepted_541 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox541) tree541 = true := by
  simp only [tree541,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox541 3 (8606503823623634957113250942592889340653731840000000000000 : Int) false,decode_split denominator ibox541 3 (8606503823623634957113250942592889340653731840000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_542 h,accepted_543 h⟩
private noncomputable def tree540 : TapeTree := .split 0 (((9334918860779281144889763066640464610370519040000000000 : Int) : ℚ)/(denominator : ℚ)) tree541 tree544
attribute [irreducible] tree540
private theorem accepted_540 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox540) tree540 = true := by
  simp only [tree540,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox540 0 (9334918860779281144889763066640464610370519040000000000 : Int) false,decode_split denominator ibox540 0 (9334918860779281144889763066640464610370519040000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_541 h,accepted_544 h⟩
private noncomputable def tree539 : TapeTree := .split 3 (((9562782026248483285681389936214321489615257600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree540 tree547
attribute [irreducible] tree539
private theorem accepted_539 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox539) tree539 = true := by
  simp only [tree539,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox539 3 (9562782026248483285681389936214321489615257600000000000000 : Int) false,decode_split denominator ibox539 3 (9562782026248483285681389936214321489615257600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_540 h,accepted_547 h⟩
private noncomputable def tree538 : TapeTree := .centered (candidateRows ibox538) (candidateRows (FixedTape.midBox ibox538))
attribute [irreducible] tree538
private theorem sign_538 : 2*denominator*(computed denominator (FixedTape.midBox ibox538)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox538).gradient k).lo.natAbs ((computed denominator ibox538).gradient k).hi.natAbs : Int)*((ibox538 k).hi-(ibox538 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox538
    (computed denominator ibox538) (computed denominator (FixedTape.midBox ibox538))
    (by decide +kernel)
private theorem midpoint_even_538 : ∀ k, 2 ∣ (ibox538 k).lo+(ibox538 k).hi := by decide +kernel
private theorem accepted_538 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox538) tree538 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox538 midpoint_even_538
  simp only [tree538,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox538,candidate_valid h (FixedTape.midBox ibox538),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox538 212 (FixedTape.rowsAux denominator ibox538 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox538) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_538
private noncomputable def tree537 : TapeTree := .centered (candidateRows ibox537) (candidateRows (FixedTape.midBox ibox537))
attribute [irreducible] tree537
private theorem sign_537 : 2*denominator*(computed denominator (FixedTape.midBox ibox537)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox537).gradient k).lo.natAbs ((computed denominator ibox537).gradient k).hi.natAbs : Int)*((ibox537 k).hi-(ibox537 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox537
    (computed denominator ibox537) (computed denominator (FixedTape.midBox ibox537))
    (by decide +kernel)
private theorem midpoint_even_537 : ∀ k, 2 ∣ (ibox537 k).lo+(ibox537 k).hi := by decide +kernel
private theorem accepted_537 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox537) tree537 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox537 midpoint_even_537
  simp only [tree537,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox537,candidate_valid h (FixedTape.midBox ibox537),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox537 212 (FixedTape.rowsAux denominator ibox537 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox537) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_537
private noncomputable def tree536 : TapeTree := .split 3 (((10519060228873331614249528929835753638576783360000000000000 : Int) : ℚ)/(denominator : ℚ)) tree537 tree538
attribute [irreducible] tree536
private theorem accepted_536 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox536) tree536 = true := by
  simp only [tree536,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox536 3 (10519060228873331614249528929835753638576783360000000000000 : Int) false,decode_split denominator ibox536 3 (10519060228873331614249528929835753638576783360000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_537 h,accepted_538 h⟩
private noncomputable def tree535 : TapeTree := .centered (candidateRows ibox535) (candidateRows (FixedTape.midBox ibox535))
attribute [irreducible] tree535
private theorem sign_535 : 2*denominator*(computed denominator (FixedTape.midBox ibox535)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox535).gradient k).lo.natAbs ((computed denominator ibox535).gradient k).hi.natAbs : Int)*((ibox535 k).hi-(ibox535 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox535
    (computed denominator ibox535) (computed denominator (FixedTape.midBox ibox535))
    (by decide +kernel)
private theorem midpoint_even_535 : ∀ k, 2 ∣ (ibox535 k).lo+(ibox535 k).hi := by decide +kernel
private theorem accepted_535 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox535) tree535 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox535 midpoint_even_535
  simp only [tree535,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox535,candidate_valid h (FixedTape.midBox ibox535),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox535 212 (FixedTape.rowsAux denominator ibox535 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox535) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_535
private noncomputable def tree534 : TapeTree := .centered (candidateRows ibox534) (candidateRows (FixedTape.midBox ibox534))
attribute [irreducible] tree534
private theorem sign_534 : 2*denominator*(computed denominator (FixedTape.midBox ibox534)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox534).gradient k).lo.natAbs ((computed denominator ibox534).gradient k).hi.natAbs : Int)*((ibox534 k).hi-(ibox534 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox534
    (computed denominator ibox534) (computed denominator (FixedTape.midBox ibox534))
    (by decide +kernel)
private theorem midpoint_even_534 : ∀ k, 2 ∣ (ibox534 k).lo+(ibox534 k).hi := by decide +kernel
private theorem accepted_534 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox534) tree534 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox534 midpoint_even_534
  simp only [tree534,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox534,candidate_valid h (FixedTape.midBox ibox534),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox534 212 (FixedTape.rowsAux denominator ibox534 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox534) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_534
private noncomputable def tree533 : TapeTree := .split 3 (((10519060228873331614249528929835753638576783360000000000000 : Int) : ℚ)/(denominator : ℚ)) tree534 tree535
attribute [irreducible] tree533
private theorem accepted_533 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox533) tree533 = true := by
  simp only [tree533,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox533 3 (10519060228873331614249528929835753638576783360000000000000 : Int) false,decode_split denominator ibox533 3 (10519060228873331614249528929835753638576783360000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_534 h,accepted_535 h⟩
private noncomputable def tree532 : TapeTree := .split 0 (((8968843611336956394109772358144760115846184960000000000 : Int) : ℚ)/(denominator : ℚ)) tree533 tree536
attribute [irreducible] tree532
private theorem accepted_532 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox532) tree532 = true := by
  simp only [tree532,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox532 0 (8968843611336956394109772358144760115846184960000000000 : Int) false,decode_split denominator ibox532 0 (8968843611336956394109772358144760115846184960000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_533 h,accepted_536 h⟩
private noncomputable def tree531 : TapeTree := .centered (candidateRows ibox531) (candidateRows (FixedTape.midBox ibox531))
attribute [irreducible] tree531
private theorem sign_531 : 2*denominator*(computed denominator (FixedTape.midBox ibox531)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox531).gradient k).lo.natAbs ((computed denominator ibox531).gradient k).hi.natAbs : Int)*((ibox531 k).hi-(ibox531 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox531
    (computed denominator ibox531) (computed denominator (FixedTape.midBox ibox531))
    (by decide +kernel)
private theorem midpoint_even_531 : ∀ k, 2 ∣ (ibox531 k).lo+(ibox531 k).hi := by decide +kernel
private theorem accepted_531 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox531) tree531 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox531 midpoint_even_531
  simp only [tree531,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox531,candidate_valid h (FixedTape.midBox ibox531),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox531 212 (FixedTape.rowsAux denominator ibox531 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox531) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_531
private noncomputable def tree530 : TapeTree := .centered (candidateRows ibox530) (candidateRows (FixedTape.midBox ibox530))
attribute [irreducible] tree530
private theorem sign_530 : 2*denominator*(computed denominator (FixedTape.midBox ibox530)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox530).gradient k).lo.natAbs ((computed denominator ibox530).gradient k).hi.natAbs : Int)*((ibox530 k).hi-(ibox530 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox530
    (computed denominator ibox530) (computed denominator (FixedTape.midBox ibox530))
    (by decide +kernel)
private theorem midpoint_even_530 : ∀ k, 2 ∣ (ibox530 k).lo+(ibox530 k).hi := by decide +kernel
private theorem accepted_530 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox530) tree530 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox530 midpoint_even_530
  simp only [tree530,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox530,candidate_valid h (FixedTape.midBox ibox530),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox530 212 (FixedTape.rowsAux denominator ibox530 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox530) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_530
private noncomputable def tree529 : TapeTree := .split 3 (((8606503823623634957113250942592889340653731840000000000000 : Int) : ℚ)/(denominator : ℚ)) tree530 tree531
attribute [irreducible] tree529
private theorem accepted_529 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox529) tree529 = true := by
  simp only [tree529,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox529 3 (8606503823623634957113250942592889340653731840000000000000 : Int) false,decode_split denominator ibox529 3 (8606503823623634957113250942592889340653731840000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_530 h,accepted_531 h⟩
private noncomputable def tree528 : TapeTree := .centered (candidateRows ibox528) (candidateRows (FixedTape.midBox ibox528))
attribute [irreducible] tree528
private theorem sign_528 : 2*denominator*(computed denominator (FixedTape.midBox ibox528)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox528).gradient k).lo.natAbs ((computed denominator ibox528).gradient k).hi.natAbs : Int)*((ibox528 k).hi-(ibox528 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox528
    (computed denominator ibox528) (computed denominator (FixedTape.midBox ibox528))
    (by decide +kernel)
private theorem midpoint_even_528 : ∀ k, 2 ∣ (ibox528 k).lo+(ibox528 k).hi := by decide +kernel
private theorem accepted_528 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox528) tree528 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox528 midpoint_even_528
  simp only [tree528,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox528,candidate_valid h (FixedTape.midBox ibox528),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox528 212 (FixedTape.rowsAux denominator ibox528 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox528) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_528
private noncomputable def tree527 : TapeTree := .centered (candidateRows ibox527) (candidateRows (FixedTape.midBox ibox527))
attribute [irreducible] tree527
private theorem sign_527 : 2*denominator*(computed denominator (FixedTape.midBox ibox527)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox527).gradient k).lo.natAbs ((computed denominator ibox527).gradient k).hi.natAbs : Int)*((ibox527 k).hi-(ibox527 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox527
    (computed denominator ibox527) (computed denominator (FixedTape.midBox ibox527))
    (by decide +kernel)
private theorem midpoint_even_527 : ∀ k, 2 ∣ (ibox527 k).lo+(ibox527 k).hi := by decide +kernel
private theorem accepted_527 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox527) tree527 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox527 midpoint_even_527
  simp only [tree527,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox527,candidate_valid h (FixedTape.midBox ibox527),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox527 212 (FixedTape.rowsAux denominator ibox527 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox527) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_527
private noncomputable def tree526 : TapeTree := .split 3 (((8606503823623634957113250942592889340653731840000000000000 : Int) : ℚ)/(denominator : ℚ)) tree527 tree528
attribute [irreducible] tree526
private theorem accepted_526 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox526) tree526 = true := by
  simp only [tree526,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox526 3 (8606503823623634957113250942592889340653731840000000000000 : Int) false,decode_split denominator ibox526 3 (8606503823623634957113250942592889340653731840000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_527 h,accepted_528 h⟩
private noncomputable def tree525 : TapeTree := .split 0 (((8968843611336956394109772358144760115846184960000000000 : Int) : ℚ)/(denominator : ℚ)) tree526 tree529
attribute [irreducible] tree525
private theorem accepted_525 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox525) tree525 = true := by
  simp only [tree525,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox525 0 (8968843611336956394109772358144760115846184960000000000 : Int) false,decode_split denominator ibox525 0 (8968843611336956394109772358144760115846184960000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_526 h,accepted_529 h⟩
private noncomputable def tree524 : TapeTree := .split 3 (((9562782026248483285681389936214321489615257600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree525 tree532
attribute [irreducible] tree524
private theorem accepted_524 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox524) tree524 = true := by
  simp only [tree524,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox524 3 (9562782026248483285681389936214321489615257600000000000000 : Int) false,decode_split denominator ibox524 3 (9562782026248483285681389936214321489615257600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_525 h,accepted_532 h⟩
private noncomputable def tree523 : TapeTree := .split 0 (((9151881236058118769499767712392612363108352000000000000 : Int) : ℚ)/(denominator : ℚ)) tree524 tree539
attribute [irreducible] tree523
private theorem accepted_523 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox523) tree523 = true := by
  simp only [tree523,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox523 0 (9151881236058118769499767712392612363108352000000000000 : Int) false,decode_split denominator ibox523 0 (9151881236058118769499767712392612363108352000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_524 h,accepted_539 h⟩
private noncomputable def tree522 : TapeTree := .split 3 (((11475338431498179942817667923457185787538309120000000000000 : Int) : ℚ)/(denominator : ℚ)) tree523 tree554
attribute [irreducible] tree522
private theorem accepted_522 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox522) tree522 = true := by
  simp only [tree522,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox522 3 (11475338431498179942817667923457185787538309120000000000000 : Int) false,decode_split denominator ibox522 3 (11475338431498179942817667923457185787538309120000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_523 h,accepted_554 h⟩
private noncomputable def tree521 : TapeTree := .centered (candidateRows ibox521) (candidateRows (FixedTape.midBox ibox521))
attribute [irreducible] tree521
private theorem sign_521 : 2*denominator*(computed denominator (FixedTape.midBox ibox521)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox521).gradient k).lo.natAbs ((computed denominator ibox521).gradient k).hi.natAbs : Int)*((ibox521 k).hi-(ibox521 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox521
    (computed denominator ibox521) (computed denominator (FixedTape.midBox ibox521))
    (by decide +kernel)
private theorem midpoint_even_521 : ∀ k, 2 ∣ (ibox521 k).lo+(ibox521 k).hi := by decide +kernel
private theorem accepted_521 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox521) tree521 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox521 midpoint_even_521
  simp only [tree521,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox521,candidate_valid h (FixedTape.midBox ibox521),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox521 212 (FixedTape.rowsAux denominator ibox521 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox521) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_521
private noncomputable def tree520 : TapeTree := .centered (candidateRows ibox520) (candidateRows (FixedTape.midBox ibox520))
attribute [irreducible] tree520
private theorem sign_520 : 2*denominator*(computed denominator (FixedTape.midBox ibox520)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox520).gradient k).lo.natAbs ((computed denominator ibox520).gradient k).hi.natAbs : Int)*((ibox520 k).hi-(ibox520 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox520
    (computed denominator ibox520) (computed denominator (FixedTape.midBox ibox520))
    (by decide +kernel)
private theorem midpoint_even_520 : ∀ k, 2 ∣ (ibox520 k).lo+(ibox520 k).hi := by decide +kernel
private theorem accepted_520 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox520) tree520 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox520 midpoint_even_520
  simp only [tree520,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox520,candidate_valid h (FixedTape.midBox ibox520),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox520 212 (FixedTape.rowsAux denominator ibox520 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox520) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_520
private noncomputable def tree519 : TapeTree := .split 3 (((6693947418373938299976972955350025042730680320000000000000 : Int) : ℚ)/(denominator : ℚ)) tree520 tree521
attribute [irreducible] tree519
private theorem accepted_519 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox519) tree519 = true := by
  simp only [tree519,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox519 3 (6693947418373938299976972955350025042730680320000000000000 : Int) false,decode_split denominator ibox519 3 (6693947418373938299976972955350025042730680320000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_520 h,accepted_521 h⟩
private noncomputable def tree518 : TapeTree := .centered (candidateRows ibox518) (candidateRows (FixedTape.midBox ibox518))
attribute [irreducible] tree518
private theorem sign_518 : 2*denominator*(computed denominator (FixedTape.midBox ibox518)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox518).gradient k).lo.natAbs ((computed denominator ibox518).gradient k).hi.natAbs : Int)*((ibox518 k).hi-(ibox518 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox518
    (computed denominator ibox518) (computed denominator (FixedTape.midBox ibox518))
    (by decide +kernel)
private theorem midpoint_even_518 : ∀ k, 2 ∣ (ibox518 k).lo+(ibox518 k).hi := by decide +kernel
private theorem accepted_518 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox518) tree518 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox518 midpoint_even_518
  simp only [tree518,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox518,candidate_valid h (FixedTape.midBox ibox518),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox518 212 (FixedTape.rowsAux denominator ibox518 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox518) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_518
private noncomputable def tree517 : TapeTree := .centered (candidateRows ibox517) (candidateRows (FixedTape.midBox ibox517))
attribute [irreducible] tree517
private theorem sign_517 : 2*denominator*(computed denominator (FixedTape.midBox ibox517)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox517).gradient k).lo.natAbs ((computed denominator ibox517).gradient k).hi.natAbs : Int)*((ibox517 k).hi-(ibox517 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox517
    (computed denominator ibox517) (computed denominator (FixedTape.midBox ibox517))
    (by decide +kernel)
private theorem midpoint_even_517 : ∀ k, 2 ∣ (ibox517 k).lo+(ibox517 k).hi := by decide +kernel
private theorem accepted_517 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox517) tree517 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox517 midpoint_even_517
  simp only [tree517,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox517,candidate_valid h (FixedTape.midBox ibox517),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox517 212 (FixedTape.rowsAux denominator ibox517 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox517) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_517
private noncomputable def tree516 : TapeTree := .split 3 (((6693947418373938299976972955350025042730680320000000000000 : Int) : ℚ)/(denominator : ℚ)) tree517 tree518
attribute [irreducible] tree516
private theorem accepted_516 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox516) tree516 = true := by
  simp only [tree516,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox516 3 (6693947418373938299976972955350025042730680320000000000000 : Int) false,decode_split denominator ibox516 3 (6693947418373938299976972955350025042730680320000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_517 h,accepted_518 h⟩
private noncomputable def tree515 : TapeTree := .split 0 (((9334918860779281144889763066640464610370519040000000000 : Int) : ℚ)/(denominator : ℚ)) tree516 tree519
attribute [irreducible] tree515
private theorem accepted_515 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox515) tree515 = true := by
  simp only [tree515,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox515 0 (9334918860779281144889763066640464610370519040000000000 : Int) false,decode_split denominator ibox515 0 (9334918860779281144889763066640464610370519040000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_516 h,accepted_519 h⟩
private noncomputable def tree514 : TapeTree := .centered (candidateRows ibox514) (candidateRows (FixedTape.midBox ibox514))
attribute [irreducible] tree514
private theorem sign_514 : 2*denominator*(computed denominator (FixedTape.midBox ibox514)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox514).gradient k).lo.natAbs ((computed denominator ibox514).gradient k).hi.natAbs : Int)*((ibox514 k).hi-(ibox514 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox514
    (computed denominator ibox514) (computed denominator (FixedTape.midBox ibox514))
    (by decide +kernel)
private theorem midpoint_even_514 : ∀ k, 2 ∣ (ibox514 k).lo+(ibox514 k).hi := by decide +kernel
private theorem accepted_514 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox514) tree514 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox514 midpoint_even_514
  simp only [tree514,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox514,candidate_valid h (FixedTape.midBox ibox514),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox514 212 (FixedTape.rowsAux denominator ibox514 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox514) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_514
private noncomputable def tree513 : TapeTree := .centered (candidateRows ibox513) (candidateRows (FixedTape.midBox ibox513))
attribute [irreducible] tree513
private theorem sign_513 : 2*denominator*(computed denominator (FixedTape.midBox ibox513)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox513).gradient k).lo.natAbs ((computed denominator ibox513).gradient k).hi.natAbs : Int)*((ibox513 k).hi-(ibox513 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox513
    (computed denominator ibox513) (computed denominator (FixedTape.midBox ibox513))
    (by decide +kernel)
private theorem midpoint_even_513 : ∀ k, 2 ∣ (ibox513 k).lo+(ibox513 k).hi := by decide +kernel
private theorem accepted_513 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox513) tree513 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox513 midpoint_even_513
  simp only [tree513,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox513,candidate_valid h (FixedTape.midBox ibox513),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox513 212 (FixedTape.rowsAux denominator ibox513 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox513) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_513
private noncomputable def tree512 : TapeTree := .split 3 (((4781391013124241642840694968107160744807628800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree513 tree514
attribute [irreducible] tree512
private theorem accepted_512 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox512) tree512 = true := by
  simp only [tree512,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox512 3 (4781391013124241642840694968107160744807628800000000000000 : Int) false,decode_split denominator ibox512 3 (4781391013124241642840694968107160744807628800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_513 h,accepted_514 h⟩
private noncomputable def tree511 : TapeTree := .centered (candidateRows ibox511) (candidateRows (FixedTape.midBox ibox511))
attribute [irreducible] tree511
private theorem sign_511 : 2*denominator*(computed denominator (FixedTape.midBox ibox511)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox511).gradient k).lo.natAbs ((computed denominator ibox511).gradient k).hi.natAbs : Int)*((ibox511 k).hi-(ibox511 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox511
    (computed denominator ibox511) (computed denominator (FixedTape.midBox ibox511))
    (by decide +kernel)
private theorem midpoint_even_511 : ∀ k, 2 ∣ (ibox511 k).lo+(ibox511 k).hi := by decide +kernel
private theorem accepted_511 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox511) tree511 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox511 midpoint_even_511
  simp only [tree511,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox511,candidate_valid h (FixedTape.midBox ibox511),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox511 212 (FixedTape.rowsAux denominator ibox511 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox511) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_511
private noncomputable def tree510 : TapeTree := .centered (candidateRows ibox510) (candidateRows (FixedTape.midBox ibox510))
attribute [irreducible] tree510
private theorem sign_510 : 2*denominator*(computed denominator (FixedTape.midBox ibox510)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox510).gradient k).lo.natAbs ((computed denominator ibox510).gradient k).hi.natAbs : Int)*((ibox510 k).hi-(ibox510 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox510
    (computed denominator ibox510) (computed denominator (FixedTape.midBox ibox510))
    (by decide +kernel)
private theorem midpoint_even_510 : ∀ k, 2 ∣ (ibox510 k).lo+(ibox510 k).hi := by decide +kernel
private theorem accepted_510 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox510) tree510 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox510 midpoint_even_510
  simp only [tree510,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox510,candidate_valid h (FixedTape.midBox ibox510),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox510 212 (FixedTape.rowsAux denominator ibox510 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox510) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_510
private noncomputable def tree509 : TapeTree := .split 3 (((4781391013124241642840694968107160744807628800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree510 tree511
attribute [irreducible] tree509
private theorem accepted_509 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox509) tree509 = true := by
  simp only [tree509,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox509 3 (4781391013124241642840694968107160744807628800000000000000 : Int) false,decode_split denominator ibox509 3 (4781391013124241642840694968107160744807628800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_510 h,accepted_511 h⟩
private noncomputable def tree508 : TapeTree := .split 0 (((9334918860779281144889763066640464610370519040000000000 : Int) : ℚ)/(denominator : ℚ)) tree509 tree512
attribute [irreducible] tree508
private theorem accepted_508 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox508) tree508 = true := by
  simp only [tree508,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox508 0 (9334918860779281144889763066640464610370519040000000000 : Int) false,decode_split denominator ibox508 0 (9334918860779281144889763066640464610370519040000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_509 h,accepted_512 h⟩
private noncomputable def tree507 : TapeTree := .split 3 (((5737669215749089971408833961728592893769154560000000000000 : Int) : ℚ)/(denominator : ℚ)) tree508 tree515
attribute [irreducible] tree507
private theorem accepted_507 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox507) tree507 = true := by
  simp only [tree507,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox507 3 (5737669215749089971408833961728592893769154560000000000000 : Int) false,decode_split denominator ibox507 3 (5737669215749089971408833961728592893769154560000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_508 h,accepted_515 h⟩
private noncomputable def tree506 : TapeTree := .centered (candidateRows ibox506) (candidateRows (FixedTape.midBox ibox506))
attribute [irreducible] tree506
private theorem sign_506 : 2*denominator*(computed denominator (FixedTape.midBox ibox506)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox506).gradient k).lo.natAbs ((computed denominator ibox506).gradient k).hi.natAbs : Int)*((ibox506 k).hi-(ibox506 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox506
    (computed denominator ibox506) (computed denominator (FixedTape.midBox ibox506))
    (by decide +kernel)
private theorem midpoint_even_506 : ∀ k, 2 ∣ (ibox506 k).lo+(ibox506 k).hi := by decide +kernel
private theorem accepted_506 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox506) tree506 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox506 midpoint_even_506
  simp only [tree506,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox506,candidate_valid h (FixedTape.midBox ibox506),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox506 212 (FixedTape.rowsAux denominator ibox506 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox506) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_506
private noncomputable def tree505 : TapeTree := .centered (candidateRows ibox505) (candidateRows (FixedTape.midBox ibox505))
attribute [irreducible] tree505
private theorem sign_505 : 2*denominator*(computed denominator (FixedTape.midBox ibox505)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox505).gradient k).lo.natAbs ((computed denominator ibox505).gradient k).hi.natAbs : Int)*((ibox505 k).hi-(ibox505 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox505
    (computed denominator ibox505) (computed denominator (FixedTape.midBox ibox505))
    (by decide +kernel)
private theorem midpoint_even_505 : ∀ k, 2 ∣ (ibox505 k).lo+(ibox505 k).hi := by decide +kernel
private theorem accepted_505 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox505) tree505 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox505 midpoint_even_505
  simp only [tree505,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox505,candidate_valid h (FixedTape.midBox ibox505),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox505 212 (FixedTape.rowsAux denominator ibox505 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox505) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_505
private noncomputable def tree504 : TapeTree := .split 3 (((6693947418373938299976972955350025042730680320000000000000 : Int) : ℚ)/(denominator : ℚ)) tree505 tree506
attribute [irreducible] tree504
private theorem accepted_504 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox504) tree504 = true := by
  simp only [tree504,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox504 3 (6693947418373938299976972955350025042730680320000000000000 : Int) false,decode_split denominator ibox504 3 (6693947418373938299976972955350025042730680320000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_505 h,accepted_506 h⟩
private noncomputable def tree503 : TapeTree := .centered (candidateRows ibox503) (candidateRows (FixedTape.midBox ibox503))
attribute [irreducible] tree503
private theorem sign_503 : 2*denominator*(computed denominator (FixedTape.midBox ibox503)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox503).gradient k).lo.natAbs ((computed denominator ibox503).gradient k).hi.natAbs : Int)*((ibox503 k).hi-(ibox503 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox503
    (computed denominator ibox503) (computed denominator (FixedTape.midBox ibox503))
    (by decide +kernel)
private theorem midpoint_even_503 : ∀ k, 2 ∣ (ibox503 k).lo+(ibox503 k).hi := by decide +kernel
private theorem accepted_503 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox503) tree503 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox503 midpoint_even_503
  simp only [tree503,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox503,candidate_valid h (FixedTape.midBox ibox503),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox503 212 (FixedTape.rowsAux denominator ibox503 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox503) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_503
private noncomputable def tree502 : TapeTree := .centered (candidateRows ibox502) (candidateRows (FixedTape.midBox ibox502))
attribute [irreducible] tree502
private theorem sign_502 : 2*denominator*(computed denominator (FixedTape.midBox ibox502)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox502).gradient k).lo.natAbs ((computed denominator ibox502).gradient k).hi.natAbs : Int)*((ibox502 k).hi-(ibox502 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox502
    (computed denominator ibox502) (computed denominator (FixedTape.midBox ibox502))
    (by decide +kernel)
private theorem midpoint_even_502 : ∀ k, 2 ∣ (ibox502 k).lo+(ibox502 k).hi := by decide +kernel
private theorem accepted_502 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox502) tree502 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox502 midpoint_even_502
  simp only [tree502,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox502,candidate_valid h (FixedTape.midBox ibox502),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox502 212 (FixedTape.rowsAux denominator ibox502 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox502) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_502
private noncomputable def tree501 : TapeTree := .split 3 (((6693947418373938299976972955350025042730680320000000000000 : Int) : ℚ)/(denominator : ℚ)) tree502 tree503
attribute [irreducible] tree501
private theorem accepted_501 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox501) tree501 = true := by
  simp only [tree501,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox501 3 (6693947418373938299976972955350025042730680320000000000000 : Int) false,decode_split denominator ibox501 3 (6693947418373938299976972955350025042730680320000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_502 h,accepted_503 h⟩
private noncomputable def tree500 : TapeTree := .split 0 (((8968843611336956394109772358144760115846184960000000000 : Int) : ℚ)/(denominator : ℚ)) tree501 tree504
attribute [irreducible] tree500
private theorem accepted_500 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox500) tree500 = true := by
  simp only [tree500,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox500 0 (8968843611336956394109772358144760115846184960000000000 : Int) false,decode_split denominator ibox500 0 (8968843611336956394109772358144760115846184960000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_501 h,accepted_504 h⟩
private noncomputable def tree499 : TapeTree := .centered (candidateRows ibox499) (candidateRows (FixedTape.midBox ibox499))
attribute [irreducible] tree499
private theorem sign_499 : 2*denominator*(computed denominator (FixedTape.midBox ibox499)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox499).gradient k).lo.natAbs ((computed denominator ibox499).gradient k).hi.natAbs : Int)*((ibox499 k).hi-(ibox499 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox499
    (computed denominator ibox499) (computed denominator (FixedTape.midBox ibox499))
    (by decide +kernel)
private theorem midpoint_even_499 : ∀ k, 2 ∣ (ibox499 k).lo+(ibox499 k).hi := by decide +kernel
private theorem accepted_499 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox499) tree499 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox499 midpoint_even_499
  simp only [tree499,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox499,candidate_valid h (FixedTape.midBox ibox499),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox499 212 (FixedTape.rowsAux denominator ibox499 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox499) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_499
private noncomputable def tree498 : TapeTree := .centered (candidateRows ibox498) (candidateRows (FixedTape.midBox ibox498))
attribute [irreducible] tree498
private theorem sign_498 : 2*denominator*(computed denominator (FixedTape.midBox ibox498)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox498).gradient k).lo.natAbs ((computed denominator ibox498).gradient k).hi.natAbs : Int)*((ibox498 k).hi-(ibox498 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox498
    (computed denominator ibox498) (computed denominator (FixedTape.midBox ibox498))
    (by decide +kernel)
private theorem midpoint_even_498 : ∀ k, 2 ∣ (ibox498 k).lo+(ibox498 k).hi := by decide +kernel
private theorem accepted_498 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox498) tree498 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox498 midpoint_even_498
  simp only [tree498,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox498,candidate_valid h (FixedTape.midBox ibox498),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox498 212 (FixedTape.rowsAux denominator ibox498 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox498) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_498
private noncomputable def tree497 : TapeTree := .split 3 (((4781391013124241642840694968107160744807628800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree498 tree499
attribute [irreducible] tree497
private theorem accepted_497 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox497) tree497 = true := by
  simp only [tree497,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox497 3 (4781391013124241642840694968107160744807628800000000000000 : Int) false,decode_split denominator ibox497 3 (4781391013124241642840694968107160744807628800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_498 h,accepted_499 h⟩
private noncomputable def tree496 : TapeTree := .centered (candidateRows ibox496) (candidateRows (FixedTape.midBox ibox496))
attribute [irreducible] tree496
private theorem sign_496 : 2*denominator*(computed denominator (FixedTape.midBox ibox496)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox496).gradient k).lo.natAbs ((computed denominator ibox496).gradient k).hi.natAbs : Int)*((ibox496 k).hi-(ibox496 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox496
    (computed denominator ibox496) (computed denominator (FixedTape.midBox ibox496))
    (by decide +kernel)
private theorem midpoint_even_496 : ∀ k, 2 ∣ (ibox496 k).lo+(ibox496 k).hi := by decide +kernel
private theorem accepted_496 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox496) tree496 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox496 midpoint_even_496
  simp only [tree496,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox496,candidate_valid h (FixedTape.midBox ibox496),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox496 212 (FixedTape.rowsAux denominator ibox496 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox496) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_496
private noncomputable def tree495 : TapeTree := .centered (candidateRows ibox495) (candidateRows (FixedTape.midBox ibox495))
attribute [irreducible] tree495
private theorem sign_495 : 2*denominator*(computed denominator (FixedTape.midBox ibox495)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox495).gradient k).lo.natAbs ((computed denominator ibox495).gradient k).hi.natAbs : Int)*((ibox495 k).hi-(ibox495 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox495
    (computed denominator ibox495) (computed denominator (FixedTape.midBox ibox495))
    (by decide +kernel)
private theorem midpoint_even_495 : ∀ k, 2 ∣ (ibox495 k).lo+(ibox495 k).hi := by decide +kernel
private theorem accepted_495 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox495) tree495 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox495 midpoint_even_495
  simp only [tree495,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox495,candidate_valid h (FixedTape.midBox ibox495),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox495 212 (FixedTape.rowsAux denominator ibox495 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox495) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_495
private noncomputable def tree494 : TapeTree := .split 3 (((4781391013124241642840694968107160744807628800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree495 tree496
attribute [irreducible] tree494
private theorem accepted_494 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox494) tree494 = true := by
  simp only [tree494,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox494 3 (4781391013124241642840694968107160744807628800000000000000 : Int) false,decode_split denominator ibox494 3 (4781391013124241642840694968107160744807628800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_495 h,accepted_496 h⟩
private noncomputable def tree493 : TapeTree := .split 0 (((8968843611336956394109772358144760115846184960000000000 : Int) : ℚ)/(denominator : ℚ)) tree494 tree497
attribute [irreducible] tree493
private theorem accepted_493 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox493) tree493 = true := by
  simp only [tree493,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox493 0 (8968843611336956394109772358144760115846184960000000000 : Int) false,decode_split denominator ibox493 0 (8968843611336956394109772358144760115846184960000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_494 h,accepted_497 h⟩
private noncomputable def tree492 : TapeTree := .split 3 (((5737669215749089971408833961728592893769154560000000000000 : Int) : ℚ)/(denominator : ℚ)) tree493 tree500
attribute [irreducible] tree492
private theorem accepted_492 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox492) tree492 = true := by
  simp only [tree492,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox492 3 (5737669215749089971408833961728592893769154560000000000000 : Int) false,decode_split denominator ibox492 3 (5737669215749089971408833961728592893769154560000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_493 h,accepted_500 h⟩
private noncomputable def tree491 : TapeTree := .split 0 (((9151881236058118769499767712392612363108352000000000000 : Int) : ℚ)/(denominator : ℚ)) tree492 tree507
attribute [irreducible] tree491
private theorem accepted_491 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox491) tree491 = true := by
  simp only [tree491,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox491 0 (9151881236058118769499767712392612363108352000000000000 : Int) false,decode_split denominator ibox491 0 (9151881236058118769499767712392612363108352000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_492 h,accepted_507 h⟩
private noncomputable def tree490 : TapeTree := .centered (candidateRows ibox490) (candidateRows (FixedTape.midBox ibox490))
attribute [irreducible] tree490
private theorem sign_490 : 2*denominator*(computed denominator (FixedTape.midBox ibox490)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox490).gradient k).lo.natAbs ((computed denominator ibox490).gradient k).hi.natAbs : Int)*((ibox490 k).hi-(ibox490 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox490
    (computed denominator ibox490) (computed denominator (FixedTape.midBox ibox490))
    (by decide +kernel)
private theorem midpoint_even_490 : ∀ k, 2 ∣ (ibox490 k).lo+(ibox490 k).hi := by decide +kernel
private theorem accepted_490 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox490) tree490 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox490 midpoint_even_490
  simp only [tree490,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox490,candidate_valid h (FixedTape.midBox ibox490),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox490 212 (FixedTape.rowsAux denominator ibox490 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox490) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_490
private noncomputable def tree489 : TapeTree := .centered (candidateRows ibox489) (candidateRows (FixedTape.midBox ibox489))
attribute [irreducible] tree489
private theorem sign_489 : 2*denominator*(computed denominator (FixedTape.midBox ibox489)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox489).gradient k).lo.natAbs ((computed denominator ibox489).gradient k).hi.natAbs : Int)*((ibox489 k).hi-(ibox489 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox489
    (computed denominator ibox489) (computed denominator (FixedTape.midBox ibox489))
    (by decide +kernel)
private theorem midpoint_even_489 : ∀ k, 2 ∣ (ibox489 k).lo+(ibox489 k).hi := by decide +kernel
private theorem accepted_489 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox489) tree489 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox489 midpoint_even_489
  simp only [tree489,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox489,candidate_valid h (FixedTape.midBox ibox489),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox489 212 (FixedTape.rowsAux denominator ibox489 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox489) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_489
private noncomputable def tree488 : TapeTree := .split 3 (((2868834607874544985704416980864296446884577280000000000000 : Int) : ℚ)/(denominator : ℚ)) tree489 tree490
attribute [irreducible] tree488
private theorem accepted_488 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox488) tree488 = true := by
  simp only [tree488,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox488 3 (2868834607874544985704416980864296446884577280000000000000 : Int) false,decode_split denominator ibox488 3 (2868834607874544985704416980864296446884577280000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_489 h,accepted_490 h⟩
private noncomputable def tree487 : TapeTree := .centered (candidateRows ibox487) (candidateRows (FixedTape.midBox ibox487))
attribute [irreducible] tree487
private theorem sign_487 : 2*denominator*(computed denominator (FixedTape.midBox ibox487)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox487).gradient k).lo.natAbs ((computed denominator ibox487).gradient k).hi.natAbs : Int)*((ibox487 k).hi-(ibox487 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox487
    (computed denominator ibox487) (computed denominator (FixedTape.midBox ibox487))
    (by decide +kernel)
private theorem midpoint_even_487 : ∀ k, 2 ∣ (ibox487 k).lo+(ibox487 k).hi := by decide +kernel
private theorem accepted_487 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox487) tree487 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox487 midpoint_even_487
  simp only [tree487,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox487,candidate_valid h (FixedTape.midBox ibox487),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox487 212 (FixedTape.rowsAux denominator ibox487 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox487) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_487
private noncomputable def tree486 : TapeTree := .centered (candidateRows ibox486) (candidateRows (FixedTape.midBox ibox486))
attribute [irreducible] tree486
private theorem sign_486 : 2*denominator*(computed denominator (FixedTape.midBox ibox486)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox486).gradient k).lo.natAbs ((computed denominator ibox486).gradient k).hi.natAbs : Int)*((ibox486 k).hi-(ibox486 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox486
    (computed denominator ibox486) (computed denominator (FixedTape.midBox ibox486))
    (by decide +kernel)
private theorem midpoint_even_486 : ∀ k, 2 ∣ (ibox486 k).lo+(ibox486 k).hi := by decide +kernel
private theorem accepted_486 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox486) tree486 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox486 midpoint_even_486
  simp only [tree486,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox486,candidate_valid h (FixedTape.midBox ibox486),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox486 212 (FixedTape.rowsAux denominator ibox486 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox486) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_486
private noncomputable def tree485 : TapeTree := .split 3 (((2868834607874544985704416980864296446884577280000000000000 : Int) : ℚ)/(denominator : ℚ)) tree486 tree487
attribute [irreducible] tree485
private theorem accepted_485 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox485) tree485 = true := by
  simp only [tree485,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox485 3 (2868834607874544985704416980864296446884577280000000000000 : Int) false,decode_split denominator ibox485 3 (2868834607874544985704416980864296446884577280000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_486 h,accepted_487 h⟩
private noncomputable def tree484 : TapeTree := .split 0 (((9334918860779281144889763066640464610370519040000000000 : Int) : ℚ)/(denominator : ℚ)) tree485 tree488
attribute [irreducible] tree484
private theorem accepted_484 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox484) tree484 = true := by
  simp only [tree484,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox484 0 (9334918860779281144889763066640464610370519040000000000 : Int) false,decode_split denominator ibox484 0 (9334918860779281144889763066640464610370519040000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_485 h,accepted_488 h⟩
private noncomputable def tree483 : TapeTree := .centered (candidateRows ibox483) (candidateRows (FixedTape.midBox ibox483))
attribute [irreducible] tree483
private theorem sign_483 : 2*denominator*(computed denominator (FixedTape.midBox ibox483)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox483).gradient k).lo.natAbs ((computed denominator ibox483).gradient k).hi.natAbs : Int)*((ibox483 k).hi-(ibox483 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox483
    (computed denominator ibox483) (computed denominator (FixedTape.midBox ibox483))
    (by decide +kernel)
private theorem midpoint_even_483 : ∀ k, 2 ∣ (ibox483 k).lo+(ibox483 k).hi := by decide +kernel
private theorem accepted_483 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox483) tree483 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox483 midpoint_even_483
  simp only [tree483,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox483,candidate_valid h (FixedTape.midBox ibox483),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox483 212 (FixedTape.rowsAux denominator ibox483 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox483) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_483
private noncomputable def tree482 : TapeTree := .centered (candidateRows ibox482) (candidateRows (FixedTape.midBox ibox482))
attribute [irreducible] tree482
private theorem sign_482 : 2*denominator*(computed denominator (FixedTape.midBox ibox482)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox482).gradient k).lo.natAbs ((computed denominator ibox482).gradient k).hi.natAbs : Int)*((ibox482 k).hi-(ibox482 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox482
    (computed denominator ibox482) (computed denominator (FixedTape.midBox ibox482))
    (by decide +kernel)
private theorem midpoint_even_482 : ∀ k, 2 ∣ (ibox482 k).lo+(ibox482 k).hi := by decide +kernel
private theorem accepted_482 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox482) tree482 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox482 midpoint_even_482
  simp only [tree482,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox482,candidate_valid h (FixedTape.midBox ibox482),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox482 212 (FixedTape.rowsAux denominator ibox482 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox482) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_482
private noncomputable def tree481 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree482 tree483
attribute [irreducible] tree481
private theorem accepted_481 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox481) tree481 = true := by
  simp only [tree481,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox481 3 (956278202624848328568138993621432148961525760000000000000 : Int) false,decode_split denominator ibox481 3 (956278202624848328568138993621432148961525760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_482 h,accepted_483 h⟩
private noncomputable def tree480 : TapeTree := .centered (candidateRows ibox480) (candidateRows (FixedTape.midBox ibox480))
attribute [irreducible] tree480
private theorem sign_480 : 2*denominator*(computed denominator (FixedTape.midBox ibox480)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox480).gradient k).lo.natAbs ((computed denominator ibox480).gradient k).hi.natAbs : Int)*((ibox480 k).hi-(ibox480 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox480
    (computed denominator ibox480) (computed denominator (FixedTape.midBox ibox480))
    (by decide +kernel)
private theorem midpoint_even_480 : ∀ k, 2 ∣ (ibox480 k).lo+(ibox480 k).hi := by decide +kernel
private theorem accepted_480 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox480) tree480 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox480 midpoint_even_480
  simp only [tree480,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox480,candidate_valid h (FixedTape.midBox ibox480),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox480 212 (FixedTape.rowsAux denominator ibox480 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox480) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_480
private noncomputable def tree479 : TapeTree := .centered (candidateRows ibox479) (candidateRows (FixedTape.midBox ibox479))
attribute [irreducible] tree479
private theorem sign_479 : 2*denominator*(computed denominator (FixedTape.midBox ibox479)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox479).gradient k).lo.natAbs ((computed denominator ibox479).gradient k).hi.natAbs : Int)*((ibox479 k).hi-(ibox479 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox479
    (computed denominator ibox479) (computed denominator (FixedTape.midBox ibox479))
    (by decide +kernel)
private theorem midpoint_even_479 : ∀ k, 2 ∣ (ibox479 k).lo+(ibox479 k).hi := by decide +kernel
private theorem accepted_479 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox479) tree479 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox479 midpoint_even_479
  simp only [tree479,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox479,candidate_valid h (FixedTape.midBox ibox479),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox479 212 (FixedTape.rowsAux denominator ibox479 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox479) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_479
private noncomputable def tree478 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree479 tree480
attribute [irreducible] tree478
private theorem accepted_478 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox478) tree478 = true := by
  simp only [tree478,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox478 3 (956278202624848328568138993621432148961525760000000000000 : Int) false,decode_split denominator ibox478 3 (956278202624848328568138993621432148961525760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_479 h,accepted_480 h⟩
private noncomputable def tree477 : TapeTree := .split 0 (((9334918860779281144889763066640464610370519040000000000 : Int) : ℚ)/(denominator : ℚ)) tree478 tree481
attribute [irreducible] tree477
private theorem accepted_477 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox477) tree477 = true := by
  simp only [tree477,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox477 0 (9334918860779281144889763066640464610370519040000000000 : Int) false,decode_split denominator ibox477 0 (9334918860779281144889763066640464610370519040000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_478 h,accepted_481 h⟩
private noncomputable def tree476 : TapeTree := .split 3 (((1912556405249696657136277987242864297923051520000000000000 : Int) : ℚ)/(denominator : ℚ)) tree477 tree484
attribute [irreducible] tree476
private theorem accepted_476 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox476) tree476 = true := by
  simp only [tree476,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox476 3 (1912556405249696657136277987242864297923051520000000000000 : Int) false,decode_split denominator ibox476 3 (1912556405249696657136277987242864297923051520000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_477 h,accepted_484 h⟩
private noncomputable def tree475 : TapeTree := .centered (candidateRows ibox475) (candidateRows (FixedTape.midBox ibox475))
attribute [irreducible] tree475
private theorem sign_475 : 2*denominator*(computed denominator (FixedTape.midBox ibox475)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox475).gradient k).lo.natAbs ((computed denominator ibox475).gradient k).hi.natAbs : Int)*((ibox475 k).hi-(ibox475 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox475
    (computed denominator ibox475) (computed denominator (FixedTape.midBox ibox475))
    (by decide +kernel)
private theorem midpoint_even_475 : ∀ k, 2 ∣ (ibox475 k).lo+(ibox475 k).hi := by decide +kernel
private theorem accepted_475 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox475) tree475 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox475 midpoint_even_475
  simp only [tree475,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox475,candidate_valid h (FixedTape.midBox ibox475),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox475 212 (FixedTape.rowsAux denominator ibox475 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox475) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_475
private noncomputable def tree474 : TapeTree := .centered (candidateRows ibox474) (candidateRows (FixedTape.midBox ibox474))
attribute [irreducible] tree474
private theorem sign_474 : 2*denominator*(computed denominator (FixedTape.midBox ibox474)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox474).gradient k).lo.natAbs ((computed denominator ibox474).gradient k).hi.natAbs : Int)*((ibox474 k).hi-(ibox474 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox474
    (computed denominator ibox474) (computed denominator (FixedTape.midBox ibox474))
    (by decide +kernel)
private theorem midpoint_even_474 : ∀ k, 2 ∣ (ibox474 k).lo+(ibox474 k).hi := by decide +kernel
private theorem accepted_474 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox474) tree474 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox474 midpoint_even_474
  simp only [tree474,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox474,candidate_valid h (FixedTape.midBox ibox474),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox474 212 (FixedTape.rowsAux denominator ibox474 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox474) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_474
private noncomputable def tree473 : TapeTree := .split 3 (((2868834607874544985704416980864296446884577280000000000000 : Int) : ℚ)/(denominator : ℚ)) tree474 tree475
attribute [irreducible] tree473
private theorem accepted_473 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox473) tree473 = true := by
  simp only [tree473,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox473 3 (2868834607874544985704416980864296446884577280000000000000 : Int) false,decode_split denominator ibox473 3 (2868834607874544985704416980864296446884577280000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_474 h,accepted_475 h⟩
private noncomputable def tree472 : TapeTree := .centered (candidateRows ibox472) (candidateRows (FixedTape.midBox ibox472))
attribute [irreducible] tree472
private theorem sign_472 : 2*denominator*(computed denominator (FixedTape.midBox ibox472)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox472).gradient k).lo.natAbs ((computed denominator ibox472).gradient k).hi.natAbs : Int)*((ibox472 k).hi-(ibox472 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox472
    (computed denominator ibox472) (computed denominator (FixedTape.midBox ibox472))
    (by decide +kernel)
private theorem midpoint_even_472 : ∀ k, 2 ∣ (ibox472 k).lo+(ibox472 k).hi := by decide +kernel
private theorem accepted_472 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox472) tree472 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox472 midpoint_even_472
  simp only [tree472,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox472,candidate_valid h (FixedTape.midBox ibox472),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox472 212 (FixedTape.rowsAux denominator ibox472 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox472) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_472
private noncomputable def tree471 : TapeTree := .centered (candidateRows ibox471) (candidateRows (FixedTape.midBox ibox471))
attribute [irreducible] tree471
private theorem sign_471 : 2*denominator*(computed denominator (FixedTape.midBox ibox471)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox471).gradient k).lo.natAbs ((computed denominator ibox471).gradient k).hi.natAbs : Int)*((ibox471 k).hi-(ibox471 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox471
    (computed denominator ibox471) (computed denominator (FixedTape.midBox ibox471))
    (by decide +kernel)
private theorem midpoint_even_471 : ∀ k, 2 ∣ (ibox471 k).lo+(ibox471 k).hi := by decide +kernel
private theorem accepted_471 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox471) tree471 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox471 midpoint_even_471
  simp only [tree471,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox471,candidate_valid h (FixedTape.midBox ibox471),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox471 212 (FixedTape.rowsAux denominator ibox471 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox471) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_471
private noncomputable def tree470 : TapeTree := .split 3 (((2868834607874544985704416980864296446884577280000000000000 : Int) : ℚ)/(denominator : ℚ)) tree471 tree472
attribute [irreducible] tree470
private theorem accepted_470 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox470) tree470 = true := by
  simp only [tree470,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox470 3 (2868834607874544985704416980864296446884577280000000000000 : Int) false,decode_split denominator ibox470 3 (2868834607874544985704416980864296446884577280000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_471 h,accepted_472 h⟩
private noncomputable def tree469 : TapeTree := .split 0 (((8968843611336956394109772358144760115846184960000000000 : Int) : ℚ)/(denominator : ℚ)) tree470 tree473
attribute [irreducible] tree469
private theorem accepted_469 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox469) tree469 = true := by
  simp only [tree469,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox469 0 (8968843611336956394109772358144760115846184960000000000 : Int) false,decode_split denominator ibox469 0 (8968843611336956394109772358144760115846184960000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_470 h,accepted_473 h⟩
private noncomputable def tree468 : TapeTree := .centered (candidateRows ibox468) (candidateRows (FixedTape.midBox ibox468))
attribute [irreducible] tree468
private theorem sign_468 : 2*denominator*(computed denominator (FixedTape.midBox ibox468)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox468).gradient k).lo.natAbs ((computed denominator ibox468).gradient k).hi.natAbs : Int)*((ibox468 k).hi-(ibox468 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox468
    (computed denominator ibox468) (computed denominator (FixedTape.midBox ibox468))
    (by decide +kernel)
private theorem midpoint_even_468 : ∀ k, 2 ∣ (ibox468 k).lo+(ibox468 k).hi := by decide +kernel
private theorem accepted_468 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox468) tree468 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox468 midpoint_even_468
  simp only [tree468,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox468,candidate_valid h (FixedTape.midBox ibox468),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox468 212 (FixedTape.rowsAux denominator ibox468 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox468) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_468
private noncomputable def tree467 : TapeTree := .centered (candidateRows ibox467) (candidateRows (FixedTape.midBox ibox467))
attribute [irreducible] tree467
private theorem sign_467 : 2*denominator*(computed denominator (FixedTape.midBox ibox467)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox467).gradient k).lo.natAbs ((computed denominator ibox467).gradient k).hi.natAbs : Int)*((ibox467 k).hi-(ibox467 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox467
    (computed denominator ibox467) (computed denominator (FixedTape.midBox ibox467))
    (by decide +kernel)
private theorem midpoint_even_467 : ∀ k, 2 ∣ (ibox467 k).lo+(ibox467 k).hi := by decide +kernel
private theorem accepted_467 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox467) tree467 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox467 midpoint_even_467
  simp only [tree467,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox467,candidate_valid h (FixedTape.midBox ibox467),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox467 212 (FixedTape.rowsAux denominator ibox467 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox467) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_467
private noncomputable def tree466 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree467 tree468
attribute [irreducible] tree466
private theorem accepted_466 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox466) tree466 = true := by
  simp only [tree466,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox466 3 (956278202624848328568138993621432148961525760000000000000 : Int) false,decode_split denominator ibox466 3 (956278202624848328568138993621432148961525760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_467 h,accepted_468 h⟩
private noncomputable def tree465 : TapeTree := .centered (candidateRows ibox465) (candidateRows (FixedTape.midBox ibox465))
attribute [irreducible] tree465
private theorem sign_465 : 2*denominator*(computed denominator (FixedTape.midBox ibox465)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox465).gradient k).lo.natAbs ((computed denominator ibox465).gradient k).hi.natAbs : Int)*((ibox465 k).hi-(ibox465 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox465
    (computed denominator ibox465) (computed denominator (FixedTape.midBox ibox465))
    (by decide +kernel)
private theorem midpoint_even_465 : ∀ k, 2 ∣ (ibox465 k).lo+(ibox465 k).hi := by decide +kernel
private theorem accepted_465 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox465) tree465 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox465 midpoint_even_465
  simp only [tree465,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox465,candidate_valid h (FixedTape.midBox ibox465),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox465 212 (FixedTape.rowsAux denominator ibox465 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox465) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_465
private noncomputable def tree464 : TapeTree := .centered (candidateRows ibox464) (candidateRows (FixedTape.midBox ibox464))
attribute [irreducible] tree464
private theorem sign_464 : 2*denominator*(computed denominator (FixedTape.midBox ibox464)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox464).gradient k).lo.natAbs ((computed denominator ibox464).gradient k).hi.natAbs : Int)*((ibox464 k).hi-(ibox464 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox464
    (computed denominator ibox464) (computed denominator (FixedTape.midBox ibox464))
    (by decide +kernel)
private theorem midpoint_even_464 : ∀ k, 2 ∣ (ibox464 k).lo+(ibox464 k).hi := by decide +kernel
private theorem accepted_464 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox464) tree464 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox464 midpoint_even_464
  simp only [tree464,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox464,candidate_valid h (FixedTape.midBox ibox464),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox464 212 (FixedTape.rowsAux denominator ibox464 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox464) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_464
private noncomputable def tree463 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree464 tree465
attribute [irreducible] tree463
private theorem accepted_463 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox463) tree463 = true := by
  simp only [tree463,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox463 3 (956278202624848328568138993621432148961525760000000000000 : Int) false,decode_split denominator ibox463 3 (956278202624848328568138993621432148961525760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_464 h,accepted_465 h⟩
private noncomputable def tree462 : TapeTree := .split 0 (((8968843611336956394109772358144760115846184960000000000 : Int) : ℚ)/(denominator : ℚ)) tree463 tree466
attribute [irreducible] tree462
private theorem accepted_462 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox462) tree462 = true := by
  simp only [tree462,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox462 0 (8968843611336956394109772358144760115846184960000000000 : Int) false,decode_split denominator ibox462 0 (8968843611336956394109772358144760115846184960000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_463 h,accepted_466 h⟩
private noncomputable def tree461 : TapeTree := .split 3 (((1912556405249696657136277987242864297923051520000000000000 : Int) : ℚ)/(denominator : ℚ)) tree462 tree469
attribute [irreducible] tree461
private theorem accepted_461 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox461) tree461 = true := by
  simp only [tree461,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox461 3 (1912556405249696657136277987242864297923051520000000000000 : Int) false,decode_split denominator ibox461 3 (1912556405249696657136277987242864297923051520000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_462 h,accepted_469 h⟩
private noncomputable def tree460 : TapeTree := .split 0 (((9151881236058118769499767712392612363108352000000000000 : Int) : ℚ)/(denominator : ℚ)) tree461 tree476
attribute [irreducible] tree460
private theorem accepted_460 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox460) tree460 = true := by
  simp only [tree460,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox460 0 (9151881236058118769499767712392612363108352000000000000 : Int) false,decode_split denominator ibox460 0 (9151881236058118769499767712392612363108352000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_461 h,accepted_476 h⟩
private noncomputable def tree459 : TapeTree := .split 3 (((3825112810499393314272555974485728595846103040000000000000 : Int) : ℚ)/(denominator : ℚ)) tree460 tree491
attribute [irreducible] tree459
private theorem accepted_459 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox459) tree459 = true := by
  simp only [tree459,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox459 3 (3825112810499393314272555974485728595846103040000000000000 : Int) false,decode_split denominator ibox459 3 (3825112810499393314272555974485728595846103040000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_460 h,accepted_491 h⟩
private noncomputable def tree458 : TapeTree := .split 3 (((7650225620998786628545111948971457191692206080000000000000 : Int) : ℚ)/(denominator : ℚ)) tree459 tree522
attribute [irreducible] tree458
private theorem accepted_458 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox458) tree458 = true := by
  simp only [tree458,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox458 3 (7650225620998786628545111948971457191692206080000000000000 : Int) false,decode_split denominator ibox458 3 (7650225620998786628545111948971457191692206080000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_459 h,accepted_522 h⟩
private noncomputable def tree457 : TapeTree := .face 1 false (candidateRows ibox457) tree458
attribute [irreducible] tree457
private theorem sign_457 : ((computed denominator ibox457).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_457 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox457) tree457 = true := by
  simp only [tree457,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox457,?_,accepted_458 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox457)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox457).gradient 1).hi) denominator_positive).1 sign_457
private noncomputable def tree456 : TapeTree := .split 0 (((9517956485500443520279758420888316857632686080000000000 : Int) : ℚ)/(denominator : ℚ)) tree457 tree585
attribute [irreducible] tree456
private theorem accepted_456 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox456) tree456 = true := by
  simp only [tree456,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox456 0 (9517956485500443520279758420888316857632686080000000000 : Int) false,decode_split denominator ibox456 0 (9517956485500443520279758420888316857632686080000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_457 h,accepted_585 h⟩
private noncomputable def tree455 : TapeTree := .split 1 (((1912556405249696657136277987242864297923051520000000000000 : Int) : ℚ)/(denominator : ℚ)) tree456 tree713
attribute [irreducible] tree455
private theorem accepted_455 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox455) tree455 = true := by
  simp only [tree455,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox455 1 (1912556405249696657136277987242864297923051520000000000000 : Int) false,decode_split denominator ibox455 1 (1912556405249696657136277987242864297923051520000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_456 h,accepted_713 h⟩
private noncomputable def tree454 : TapeTree := .split 1 (((3825112810499393314272555974485728595846103040000000000000 : Int) : ℚ)/(denominator : ℚ)) tree455 tree722
attribute [irreducible] tree454
private theorem accepted_454 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox454) tree454 = true := by
  simp only [tree454,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox454 1 (3825112810499393314272555974485728595846103040000000000000 : Int) false,decode_split denominator ibox454 1 (3825112810499393314272555974485728595846103040000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_455 h,accepted_722 h⟩
private noncomputable def tree453 : TapeTree := .face 2 true (candidateRows ibox453) tree454
attribute [irreducible] tree453
private theorem sign_453 : 0 ≤ ((computed denominator ibox453).gradient 2).lo := by decide +kernel
private theorem accepted_453 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox453) tree453 = true := by
  simp only [tree453,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox453,?_,accepted_454 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox453)).gradient 2).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox453).gradient 2).lo) denominator_positive).2 sign_453
private noncomputable def tree452 : TapeTree := .split 1 (((7650225620998786628545111948971457191692206080000000000000 : Int) : ℚ)/(denominator : ℚ)) tree453 tree727
attribute [irreducible] tree452
private theorem accepted_452 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox452) tree452 = true := by
  simp only [tree452,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox452 1 (7650225620998786628545111948971457191692206080000000000000 : Int) false,decode_split denominator ibox452 1 (7650225620998786628545111948971457191692206080000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_453 h,accepted_727 h⟩
private noncomputable def tree451 : TapeTree := .centered (candidateRows ibox451) (candidateRows (FixedTape.midBox ibox451))
attribute [irreducible] tree451
private theorem sign_451 : 2*denominator*(computed denominator (FixedTape.midBox ibox451)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox451).gradient k).lo.natAbs ((computed denominator ibox451).gradient k).hi.natAbs : Int)*((ibox451 k).hi-(ibox451 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox451
    (computed denominator ibox451) (computed denominator (FixedTape.midBox ibox451))
    (by decide +kernel)
private theorem midpoint_even_451 : ∀ k, 2 ∣ (ibox451 k).lo+(ibox451 k).hi := by decide +kernel
private theorem accepted_451 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox451) tree451 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox451 midpoint_even_451
  simp only [tree451,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox451,candidate_valid h (FixedTape.midBox ibox451),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox451 212 (FixedTape.rowsAux denominator ibox451 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox451) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_451
private noncomputable def tree450 : TapeTree := .centered (candidateRows ibox450) (candidateRows (FixedTape.midBox ibox450))
attribute [irreducible] tree450
private theorem sign_450 : 2*denominator*(computed denominator (FixedTape.midBox ibox450)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox450).gradient k).lo.natAbs ((computed denominator ibox450).gradient k).hi.natAbs : Int)*((ibox450 k).hi-(ibox450 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox450
    (computed denominator ibox450) (computed denominator (FixedTape.midBox ibox450))
    (by decide +kernel)
private theorem midpoint_even_450 : ∀ k, 2 ∣ (ibox450 k).lo+(ibox450 k).hi := by decide +kernel
private theorem accepted_450 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox450) tree450 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox450 midpoint_even_450
  simp only [tree450,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox450,candidate_valid h (FixedTape.midBox ibox450),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox450 212 (FixedTape.rowsAux denominator ibox450 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox450) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_450
private noncomputable def tree449 : TapeTree := .split 1 (((7650225620998786628545111948971457191692206080000000000000 : Int) : ℚ)/(denominator : ℚ)) tree450 tree451
attribute [irreducible] tree449
private theorem accepted_449 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox449) tree449 = true := by
  simp only [tree449,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox449 1 (7650225620998786628545111948971457191692206080000000000000 : Int) false,decode_split denominator ibox449 1 (7650225620998786628545111948971457191692206080000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_450 h,accepted_451 h⟩
private noncomputable def tree448 : TapeTree := .centered (candidateRows ibox448) (candidateRows (FixedTape.midBox ibox448))
attribute [irreducible] tree448
private theorem sign_448 : 2*denominator*(computed denominator (FixedTape.midBox ibox448)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox448).gradient k).lo.natAbs ((computed denominator ibox448).gradient k).hi.natAbs : Int)*((ibox448 k).hi-(ibox448 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox448
    (computed denominator ibox448) (computed denominator (FixedTape.midBox ibox448))
    (by decide +kernel)
private theorem midpoint_even_448 : ∀ k, 2 ∣ (ibox448 k).lo+(ibox448 k).hi := by decide +kernel
private theorem accepted_448 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox448) tree448 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox448 midpoint_even_448
  simp only [tree448,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox448,candidate_valid h (FixedTape.midBox ibox448),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox448 212 (FixedTape.rowsAux denominator ibox448 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox448) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_448
private noncomputable def tree447 : TapeTree := .centered (candidateRows ibox447) (candidateRows (FixedTape.midBox ibox447))
attribute [irreducible] tree447
private theorem sign_447 : 2*denominator*(computed denominator (FixedTape.midBox ibox447)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox447).gradient k).lo.natAbs ((computed denominator ibox447).gradient k).hi.natAbs : Int)*((ibox447 k).hi-(ibox447 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox447
    (computed denominator ibox447) (computed denominator (FixedTape.midBox ibox447))
    (by decide +kernel)
private theorem midpoint_even_447 : ∀ k, 2 ∣ (ibox447 k).lo+(ibox447 k).hi := by decide +kernel
private theorem accepted_447 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox447) tree447 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox447 midpoint_even_447
  simp only [tree447,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox447,candidate_valid h (FixedTape.midBox ibox447),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox447 212 (FixedTape.rowsAux denominator ibox447 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox447) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_447
private noncomputable def tree446 : TapeTree := .split 1 (((7650225620998786628545111948971457191692206080000000000000 : Int) : ℚ)/(denominator : ℚ)) tree447 tree448
attribute [irreducible] tree446
private theorem accepted_446 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox446) tree446 = true := by
  simp only [tree446,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox446 1 (7650225620998786628545111948971457191692206080000000000000 : Int) false,decode_split denominator ibox446 1 (7650225620998786628545111948971457191692206080000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_447 h,accepted_448 h⟩
private noncomputable def tree445 : TapeTree := .split 0 (((9517956485500443520279758420888316857632686080000000000 : Int) : ℚ)/(denominator : ℚ)) tree446 tree449
attribute [irreducible] tree445
private theorem accepted_445 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox445) tree445 = true := by
  simp only [tree445,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox445 0 (9517956485500443520279758420888316857632686080000000000 : Int) false,decode_split denominator ibox445 0 (9517956485500443520279758420888316857632686080000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_446 h,accepted_449 h⟩
private noncomputable def tree444 : TapeTree := .face 3 false (candidateRows ibox444) tree445
attribute [irreducible] tree444
private theorem sign_444 : ((computed denominator ibox444).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_444 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox444) tree444 = true := by
  simp only [tree444,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox444,?_,accepted_445 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox444)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox444).gradient 3).hi) denominator_positive).1 sign_444
private noncomputable def tree443 : TapeTree := .split 2 (((11475338431498179942817667923457185787538309120000000000000 : Int) : ℚ)/(denominator : ℚ)) tree444 tree452
attribute [irreducible] tree443
private theorem accepted_443 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox443) tree443 = true := by
  simp only [tree443,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox443 2 (11475338431498179942817667923457185787538309120000000000000 : Int) false,decode_split denominator ibox443 2 (11475338431498179942817667923457185787538309120000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_444 h,accepted_452 h⟩
private noncomputable def tree442 : TapeTree := .centered (candidateRows ibox442) (candidateRows (FixedTape.midBox ibox442))
attribute [irreducible] tree442
private theorem sign_442 : 2*denominator*(computed denominator (FixedTape.midBox ibox442)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox442).gradient k).lo.natAbs ((computed denominator ibox442).gradient k).hi.natAbs : Int)*((ibox442 k).hi-(ibox442 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox442
    (computed denominator ibox442) (computed denominator (FixedTape.midBox ibox442))
    (by decide +kernel)
private theorem midpoint_even_442 : ∀ k, 2 ∣ (ibox442 k).lo+(ibox442 k).hi := by decide +kernel
private theorem accepted_442 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox442) tree442 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox442 midpoint_even_442
  simp only [tree442,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox442,candidate_valid h (FixedTape.midBox ibox442),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox442 212 (FixedTape.rowsAux denominator ibox442 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox442) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_442
private noncomputable def tree441 : TapeTree := .centered (candidateRows ibox441) (candidateRows (FixedTape.midBox ibox441))
attribute [irreducible] tree441
private theorem sign_441 : 2*denominator*(computed denominator (FixedTape.midBox ibox441)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox441).gradient k).lo.natAbs ((computed denominator ibox441).gradient k).hi.natAbs : Int)*((ibox441 k).hi-(ibox441 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox441
    (computed denominator ibox441) (computed denominator (FixedTape.midBox ibox441))
    (by decide +kernel)
private theorem midpoint_even_441 : ∀ k, 2 ∣ (ibox441 k).lo+(ibox441 k).hi := by decide +kernel
private theorem accepted_441 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox441) tree441 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox441 midpoint_even_441
  simp only [tree441,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox441,candidate_valid h (FixedTape.midBox ibox441),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox441 212 (FixedTape.rowsAux denominator ibox441 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox441) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_441
private noncomputable def tree440 : TapeTree := .split 1 (((11475338431498179942817667923457185787538309120000000000000 : Int) : ℚ)/(denominator : ℚ)) tree441 tree442
attribute [irreducible] tree440
private theorem accepted_440 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox440) tree440 = true := by
  simp only [tree440,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox440 1 (11475338431498179942817667923457185787538309120000000000000 : Int) false,decode_split denominator ibox440 1 (11475338431498179942817667923457185787538309120000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_441 h,accepted_442 h⟩
private noncomputable def tree439 : TapeTree := .centered (candidateRows ibox439) (candidateRows (FixedTape.midBox ibox439))
attribute [irreducible] tree439
private theorem sign_439 : 2*denominator*(computed denominator (FixedTape.midBox ibox439)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox439).gradient k).lo.natAbs ((computed denominator ibox439).gradient k).hi.natAbs : Int)*((ibox439 k).hi-(ibox439 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox439
    (computed denominator ibox439) (computed denominator (FixedTape.midBox ibox439))
    (by decide +kernel)
private theorem midpoint_even_439 : ∀ k, 2 ∣ (ibox439 k).lo+(ibox439 k).hi := by decide +kernel
private theorem accepted_439 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox439) tree439 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox439 midpoint_even_439
  simp only [tree439,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox439,candidate_valid h (FixedTape.midBox ibox439),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox439 212 (FixedTape.rowsAux denominator ibox439 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox439) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_439
private noncomputable def tree438 : TapeTree := .centered (candidateRows ibox438) (candidateRows (FixedTape.midBox ibox438))
attribute [irreducible] tree438
private theorem sign_438 : 2*denominator*(computed denominator (FixedTape.midBox ibox438)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox438).gradient k).lo.natAbs ((computed denominator ibox438).gradient k).hi.natAbs : Int)*((ibox438 k).hi-(ibox438 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox438
    (computed denominator ibox438) (computed denominator (FixedTape.midBox ibox438))
    (by decide +kernel)
private theorem midpoint_even_438 : ∀ k, 2 ∣ (ibox438 k).lo+(ibox438 k).hi := by decide +kernel
private theorem accepted_438 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox438) tree438 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox438 midpoint_even_438
  simp only [tree438,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox438,candidate_valid h (FixedTape.midBox ibox438),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox438 212 (FixedTape.rowsAux denominator ibox438 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox438) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_438
private noncomputable def tree437 : TapeTree := .split 1 (((11475338431498179942817667923457185787538309120000000000000 : Int) : ℚ)/(denominator : ℚ)) tree438 tree439
attribute [irreducible] tree437
private theorem accepted_437 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox437) tree437 = true := by
  simp only [tree437,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox437 1 (11475338431498179942817667923457185787538309120000000000000 : Int) false,decode_split denominator ibox437 1 (11475338431498179942817667923457185787538309120000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_438 h,accepted_439 h⟩
private noncomputable def tree436 : TapeTree := .split 0 (((8053655487731144517159795586905498879535349760000000000 : Int) : ℚ)/(denominator : ℚ)) tree437 tree440
attribute [irreducible] tree436
private theorem accepted_436 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox436) tree436 = true := by
  simp only [tree436,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox436 0 (8053655487731144517159795586905498879535349760000000000 : Int) false,decode_split denominator ibox436 0 (8053655487731144517159795586905498879535349760000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_437 h,accepted_440 h⟩
private noncomputable def tree435 : TapeTree := .face 3 false (candidateRows ibox435) tree436
attribute [irreducible] tree435
private theorem sign_435 : ((computed denominator ibox435).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_435 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox435) tree435 = true := by
  simp only [tree435,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox435,?_,accepted_436 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox435)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox435).gradient 3).hi) denominator_positive).1 sign_435
private noncomputable def tree434 : TapeTree := .centered (candidateRows ibox434) (candidateRows (FixedTape.midBox ibox434))
attribute [irreducible] tree434
private theorem sign_434 : 2*denominator*(computed denominator (FixedTape.midBox ibox434)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox434).gradient k).lo.natAbs ((computed denominator ibox434).gradient k).hi.natAbs : Int)*((ibox434 k).hi-(ibox434 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox434
    (computed denominator ibox434) (computed denominator (FixedTape.midBox ibox434))
    (by decide +kernel)
private theorem midpoint_even_434 : ∀ k, 2 ∣ (ibox434 k).lo+(ibox434 k).hi := by decide +kernel
private theorem accepted_434 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox434) tree434 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox434 midpoint_even_434
  simp only [tree434,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox434,candidate_valid h (FixedTape.midBox ibox434),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox434 212 (FixedTape.rowsAux denominator ibox434 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox434) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_434
private noncomputable def tree433 : TapeTree := .face 1 false (candidateRows ibox433) tree434
attribute [irreducible] tree433
private theorem sign_433 : ((computed denominator ibox433).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_433 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox433) tree433 = true := by
  simp only [tree433,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox433,?_,accepted_434 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox433)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox433).gradient 1).hi) denominator_positive).1 sign_433
private noncomputable def tree432 : TapeTree := .centered (candidateRows ibox432) (candidateRows (FixedTape.midBox ibox432))
attribute [irreducible] tree432
private theorem sign_432 : 2*denominator*(computed denominator (FixedTape.midBox ibox432)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox432).gradient k).lo.natAbs ((computed denominator ibox432).gradient k).hi.natAbs : Int)*((ibox432 k).hi-(ibox432 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox432
    (computed denominator ibox432) (computed denominator (FixedTape.midBox ibox432))
    (by decide +kernel)
private theorem midpoint_even_432 : ∀ k, 2 ∣ (ibox432 k).lo+(ibox432 k).hi := by decide +kernel
private theorem accepted_432 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox432) tree432 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox432 midpoint_even_432
  simp only [tree432,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox432,candidate_valid h (FixedTape.midBox ibox432),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox432 212 (FixedTape.rowsAux denominator ibox432 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox432) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_432
private noncomputable def tree431 : TapeTree := .face 1 false (candidateRows ibox431) tree432
attribute [irreducible] tree431
private theorem sign_431 : ((computed denominator ibox431).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_431 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox431) tree431 = true := by
  simp only [tree431,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox431,?_,accepted_432 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox431)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox431).gradient 1).hi) denominator_positive).1 sign_431
private noncomputable def tree430 : TapeTree := .split 0 (((8053655487731144517159795586905498879535349760000000000 : Int) : ℚ)/(denominator : ℚ)) tree431 tree433
attribute [irreducible] tree430
private theorem accepted_430 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox430) tree430 = true := by
  simp only [tree430,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox430 0 (8053655487731144517159795586905498879535349760000000000 : Int) false,decode_split denominator ibox430 0 (8053655487731144517159795586905498879535349760000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_431 h,accepted_433 h⟩
private noncomputable def tree429 : TapeTree := .centered (candidateRows ibox429) (candidateRows (FixedTape.midBox ibox429))
attribute [irreducible] tree429
private theorem sign_429 : 2*denominator*(computed denominator (FixedTape.midBox ibox429)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox429).gradient k).lo.natAbs ((computed denominator ibox429).gradient k).hi.natAbs : Int)*((ibox429 k).hi-(ibox429 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox429
    (computed denominator ibox429) (computed denominator (FixedTape.midBox ibox429))
    (by decide +kernel)
private theorem midpoint_even_429 : ∀ k, 2 ∣ (ibox429 k).lo+(ibox429 k).hi := by decide +kernel
private theorem accepted_429 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox429) tree429 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox429 midpoint_even_429
  simp only [tree429,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox429,candidate_valid h (FixedTape.midBox ibox429),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox429 212 (FixedTape.rowsAux denominator ibox429 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox429) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_429
private noncomputable def tree428 : TapeTree := .centered (candidateRows ibox428) (candidateRows (FixedTape.midBox ibox428))
attribute [irreducible] tree428
private theorem sign_428 : 2*denominator*(computed denominator (FixedTape.midBox ibox428)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox428).gradient k).lo.natAbs ((computed denominator ibox428).gradient k).hi.natAbs : Int)*((ibox428 k).hi-(ibox428 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox428
    (computed denominator ibox428) (computed denominator (FixedTape.midBox ibox428))
    (by decide +kernel)
private theorem midpoint_even_428 : ∀ k, 2 ∣ (ibox428 k).lo+(ibox428 k).hi := by decide +kernel
private theorem accepted_428 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox428) tree428 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox428 midpoint_even_428
  simp only [tree428,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox428,candidate_valid h (FixedTape.midBox ibox428),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox428 212 (FixedTape.rowsAux denominator ibox428 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox428) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_428
private noncomputable def tree427 : TapeTree := .split 3 (((7650225620998786628545111948971457191692206080000000000000 : Int) : ℚ)/(denominator : ℚ)) tree428 tree429
attribute [irreducible] tree427
private theorem accepted_427 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox427) tree427 = true := by
  simp only [tree427,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox427 3 (7650225620998786628545111948971457191692206080000000000000 : Int) false,decode_split denominator ibox427 3 (7650225620998786628545111948971457191692206080000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_428 h,accepted_429 h⟩
private noncomputable def tree426 : TapeTree := .face 1 false (candidateRows ibox426) tree427
attribute [irreducible] tree426
private theorem sign_426 : ((computed denominator ibox426).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_426 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox426) tree426 = true := by
  simp only [tree426,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox426,?_,accepted_427 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox426)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox426).gradient 1).hi) denominator_positive).1 sign_426
private noncomputable def tree425 : TapeTree := .centered (candidateRows ibox425) (candidateRows (FixedTape.midBox ibox425))
attribute [irreducible] tree425
private theorem sign_425 : 2*denominator*(computed denominator (FixedTape.midBox ibox425)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox425).gradient k).lo.natAbs ((computed denominator ibox425).gradient k).hi.natAbs : Int)*((ibox425 k).hi-(ibox425 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox425
    (computed denominator ibox425) (computed denominator (FixedTape.midBox ibox425))
    (by decide +kernel)
private theorem midpoint_even_425 : ∀ k, 2 ∣ (ibox425 k).lo+(ibox425 k).hi := by decide +kernel
private theorem accepted_425 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox425) tree425 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox425 midpoint_even_425
  simp only [tree425,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox425,candidate_valid h (FixedTape.midBox ibox425),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox425 212 (FixedTape.rowsAux denominator ibox425 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox425) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_425
private noncomputable def tree424 : TapeTree := .centered (candidateRows ibox424) (candidateRows (FixedTape.midBox ibox424))
attribute [irreducible] tree424
private theorem sign_424 : 2*denominator*(computed denominator (FixedTape.midBox ibox424)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox424).gradient k).lo.natAbs ((computed denominator ibox424).gradient k).hi.natAbs : Int)*((ibox424 k).hi-(ibox424 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox424
    (computed denominator ibox424) (computed denominator (FixedTape.midBox ibox424))
    (by decide +kernel)
private theorem midpoint_even_424 : ∀ k, 2 ∣ (ibox424 k).lo+(ibox424 k).hi := by decide +kernel
private theorem accepted_424 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox424) tree424 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox424 midpoint_even_424
  simp only [tree424,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox424,candidate_valid h (FixedTape.midBox ibox424),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox424 212 (FixedTape.rowsAux denominator ibox424 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox424) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_424
private noncomputable def tree423 : TapeTree := .split 3 (((7650225620998786628545111948971457191692206080000000000000 : Int) : ℚ)/(denominator : ℚ)) tree424 tree425
attribute [irreducible] tree423
private theorem accepted_423 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox423) tree423 = true := by
  simp only [tree423,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox423 3 (7650225620998786628545111948971457191692206080000000000000 : Int) false,decode_split denominator ibox423 3 (7650225620998786628545111948971457191692206080000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_424 h,accepted_425 h⟩
private noncomputable def tree422 : TapeTree := .face 1 false (candidateRows ibox422) tree423
attribute [irreducible] tree422
private theorem sign_422 : ((computed denominator ibox422).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_422 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox422) tree422 = true := by
  simp only [tree422,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox422,?_,accepted_423 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox422)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox422).gradient 1).hi) denominator_positive).1 sign_422
private noncomputable def tree421 : TapeTree := .split 0 (((8053655487731144517159795586905498879535349760000000000 : Int) : ℚ)/(denominator : ℚ)) tree422 tree426
attribute [irreducible] tree421
private theorem accepted_421 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox421) tree421 = true := by
  simp only [tree421,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox421 0 (8053655487731144517159795586905498879535349760000000000 : Int) false,decode_split denominator ibox421 0 (8053655487731144517159795586905498879535349760000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_422 h,accepted_426 h⟩
private noncomputable def tree420 : TapeTree := .centered (candidateRows ibox420) (candidateRows (FixedTape.midBox ibox420))
attribute [irreducible] tree420
private theorem sign_420 : 2*denominator*(computed denominator (FixedTape.midBox ibox420)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox420).gradient k).lo.natAbs ((computed denominator ibox420).gradient k).hi.natAbs : Int)*((ibox420 k).hi-(ibox420 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox420
    (computed denominator ibox420) (computed denominator (FixedTape.midBox ibox420))
    (by decide +kernel)
private theorem midpoint_even_420 : ∀ k, 2 ∣ (ibox420 k).lo+(ibox420 k).hi := by decide +kernel
private theorem accepted_420 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox420) tree420 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox420 midpoint_even_420
  simp only [tree420,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox420,candidate_valid h (FixedTape.midBox ibox420),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox420 212 (FixedTape.rowsAux denominator ibox420 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox420) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_420
private noncomputable def tree419 : TapeTree := .centered (candidateRows ibox419) (candidateRows (FixedTape.midBox ibox419))
attribute [irreducible] tree419
private theorem sign_419 : 2*denominator*(computed denominator (FixedTape.midBox ibox419)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox419).gradient k).lo.natAbs ((computed denominator ibox419).gradient k).hi.natAbs : Int)*((ibox419 k).hi-(ibox419 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox419
    (computed denominator ibox419) (computed denominator (FixedTape.midBox ibox419))
    (by decide +kernel)
private theorem midpoint_even_419 : ∀ k, 2 ∣ (ibox419 k).lo+(ibox419 k).hi := by decide +kernel
private theorem accepted_419 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox419) tree419 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox419 midpoint_even_419
  simp only [tree419,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox419,candidate_valid h (FixedTape.midBox ibox419),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox419 212 (FixedTape.rowsAux denominator ibox419 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox419) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_419
private noncomputable def tree418 : TapeTree := .split 0 (((8602768361894631643329781649649055621321850880000000000 : Int) : ℚ)/(denominator : ℚ)) tree419 tree420
attribute [irreducible] tree418
private theorem accepted_418 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox418) tree418 = true := by
  simp only [tree418,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox418 0 (8602768361894631643329781649649055621321850880000000000 : Int) false,decode_split denominator ibox418 0 (8602768361894631643329781649649055621321850880000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_419 h,accepted_420 h⟩
private noncomputable def tree417 : TapeTree := .centered (candidateRows ibox417) (candidateRows (FixedTape.midBox ibox417))
attribute [irreducible] tree417
private theorem sign_417 : 2*denominator*(computed denominator (FixedTape.midBox ibox417)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox417).gradient k).lo.natAbs ((computed denominator ibox417).gradient k).hi.natAbs : Int)*((ibox417 k).hi-(ibox417 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox417
    (computed denominator ibox417) (computed denominator (FixedTape.midBox ibox417))
    (by decide +kernel)
private theorem midpoint_even_417 : ∀ k, 2 ∣ (ibox417 k).lo+(ibox417 k).hi := by decide +kernel
private theorem accepted_417 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox417) tree417 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox417 midpoint_even_417
  simp only [tree417,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox417,candidate_valid h (FixedTape.midBox ibox417),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox417 212 (FixedTape.rowsAux denominator ibox417 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox417) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_417
private noncomputable def tree416 : TapeTree := .centered (candidateRows ibox416) (candidateRows (FixedTape.midBox ibox416))
attribute [irreducible] tree416
private theorem sign_416 : 2*denominator*(computed denominator (FixedTape.midBox ibox416)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox416).gradient k).lo.natAbs ((computed denominator ibox416).gradient k).hi.natAbs : Int)*((ibox416 k).hi-(ibox416 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox416
    (computed denominator ibox416) (computed denominator (FixedTape.midBox ibox416))
    (by decide +kernel)
private theorem midpoint_even_416 : ∀ k, 2 ∣ (ibox416 k).lo+(ibox416 k).hi := by decide +kernel
private theorem accepted_416 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox416) tree416 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox416 midpoint_even_416
  simp only [tree416,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox416,candidate_valid h (FixedTape.midBox ibox416),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox416 212 (FixedTape.rowsAux denominator ibox416 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox416) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_416
private noncomputable def tree415 : TapeTree := .split 0 (((8602768361894631643329781649649055621321850880000000000 : Int) : ℚ)/(denominator : ℚ)) tree416 tree417
attribute [irreducible] tree415
private theorem accepted_415 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox415) tree415 = true := by
  simp only [tree415,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox415 0 (8602768361894631643329781649649055621321850880000000000 : Int) false,decode_split denominator ibox415 0 (8602768361894631643329781649649055621321850880000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_416 h,accepted_417 h⟩
private noncomputable def tree414 : TapeTree := .split 3 (((14344173039372724928522084904321482234422886400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree415 tree418
attribute [irreducible] tree414
private theorem accepted_414 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox414) tree414 = true := by
  simp only [tree414,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox414 3 (14344173039372724928522084904321482234422886400000000000000 : Int) false,decode_split denominator ibox414 3 (14344173039372724928522084904321482234422886400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_415 h,accepted_418 h⟩
private noncomputable def tree413 : TapeTree := .centered (candidateRows ibox413) (candidateRows (FixedTape.midBox ibox413))
attribute [irreducible] tree413
private theorem sign_413 : 2*denominator*(computed denominator (FixedTape.midBox ibox413)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox413).gradient k).lo.natAbs ((computed denominator ibox413).gradient k).hi.natAbs : Int)*((ibox413 k).hi-(ibox413 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox413
    (computed denominator ibox413) (computed denominator (FixedTape.midBox ibox413))
    (by decide +kernel)
private theorem midpoint_even_413 : ∀ k, 2 ∣ (ibox413 k).lo+(ibox413 k).hi := by decide +kernel
private theorem accepted_413 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox413) tree413 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox413 midpoint_even_413
  simp only [tree413,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox413,candidate_valid h (FixedTape.midBox ibox413),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox413 212 (FixedTape.rowsAux denominator ibox413 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox413) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_413
private noncomputable def tree412 : TapeTree := .centered (candidateRows ibox412) (candidateRows (FixedTape.midBox ibox412))
attribute [irreducible] tree412
private theorem sign_412 : 2*denominator*(computed denominator (FixedTape.midBox ibox412)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox412).gradient k).lo.natAbs ((computed denominator ibox412).gradient k).hi.natAbs : Int)*((ibox412 k).hi-(ibox412 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox412
    (computed denominator ibox412) (computed denominator (FixedTape.midBox ibox412))
    (by decide +kernel)
private theorem midpoint_even_412 : ∀ k, 2 ∣ (ibox412 k).lo+(ibox412 k).hi := by decide +kernel
private theorem accepted_412 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox412) tree412 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox412 midpoint_even_412
  simp only [tree412,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox412,candidate_valid h (FixedTape.midBox ibox412),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox412 212 (FixedTape.rowsAux denominator ibox412 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox412) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_412
private noncomputable def tree411 : TapeTree := .split 0 (((8236693112452306892549790941153351126797516800000000000 : Int) : ℚ)/(denominator : ℚ)) tree412 tree413
attribute [irreducible] tree411
private theorem accepted_411 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox411) tree411 = true := by
  simp only [tree411,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox411 0 (8236693112452306892549790941153351126797516800000000000 : Int) false,decode_split denominator ibox411 0 (8236693112452306892549790941153351126797516800000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_412 h,accepted_413 h⟩
private noncomputable def tree410 : TapeTree := .centered (candidateRows ibox410) (candidateRows (FixedTape.midBox ibox410))
attribute [irreducible] tree410
private theorem sign_410 : 2*denominator*(computed denominator (FixedTape.midBox ibox410)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox410).gradient k).lo.natAbs ((computed denominator ibox410).gradient k).hi.natAbs : Int)*((ibox410 k).hi-(ibox410 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox410
    (computed denominator ibox410) (computed denominator (FixedTape.midBox ibox410))
    (by decide +kernel)
private theorem midpoint_even_410 : ∀ k, 2 ∣ (ibox410 k).lo+(ibox410 k).hi := by decide +kernel
private theorem accepted_410 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox410) tree410 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox410 midpoint_even_410
  simp only [tree410,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox410,candidate_valid h (FixedTape.midBox ibox410),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox410 212 (FixedTape.rowsAux denominator ibox410 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox410) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_410
private noncomputable def tree409 : TapeTree := .centered (candidateRows ibox409) (candidateRows (FixedTape.midBox ibox409))
attribute [irreducible] tree409
private theorem sign_409 : 2*denominator*(computed denominator (FixedTape.midBox ibox409)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox409).gradient k).lo.natAbs ((computed denominator ibox409).gradient k).hi.natAbs : Int)*((ibox409 k).hi-(ibox409 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox409
    (computed denominator ibox409) (computed denominator (FixedTape.midBox ibox409))
    (by decide +kernel)
private theorem midpoint_even_409 : ∀ k, 2 ∣ (ibox409 k).lo+(ibox409 k).hi := by decide +kernel
private theorem accepted_409 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox409) tree409 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox409 midpoint_even_409
  simp only [tree409,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox409,candidate_valid h (FixedTape.midBox ibox409),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox409 212 (FixedTape.rowsAux denominator ibox409 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox409) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_409
private noncomputable def tree408 : TapeTree := .split 0 (((8236693112452306892549790941153351126797516800000000000 : Int) : ℚ)/(denominator : ℚ)) tree409 tree410
attribute [irreducible] tree408
private theorem accepted_408 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox408) tree408 = true := by
  simp only [tree408,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox408 0 (8236693112452306892549790941153351126797516800000000000 : Int) false,decode_split denominator ibox408 0 (8236693112452306892549790941153351126797516800000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_409 h,accepted_410 h⟩
private noncomputable def tree407 : TapeTree := .split 3 (((14344173039372724928522084904321482234422886400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree408 tree411
attribute [irreducible] tree407
private theorem accepted_407 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox407) tree407 = true := by
  simp only [tree407,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox407 3 (14344173039372724928522084904321482234422886400000000000000 : Int) false,decode_split denominator ibox407 3 (14344173039372724928522084904321482234422886400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_408 h,accepted_411 h⟩
private noncomputable def tree406 : TapeTree := .split 0 (((8419730737173469267939786295401203374059683840000000000 : Int) : ℚ)/(denominator : ℚ)) tree407 tree414
attribute [irreducible] tree406
private theorem accepted_406 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox406) tree406 = true := by
  simp only [tree406,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox406 0 (8419730737173469267939786295401203374059683840000000000 : Int) false,decode_split denominator ibox406 0 (8419730737173469267939786295401203374059683840000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_407 h,accepted_414 h⟩
private noncomputable def tree405 : TapeTree := .centered (candidateRows ibox405) (candidateRows (FixedTape.midBox ibox405))
attribute [irreducible] tree405
private theorem sign_405 : 2*denominator*(computed denominator (FixedTape.midBox ibox405)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox405).gradient k).lo.natAbs ((computed denominator ibox405).gradient k).hi.natAbs : Int)*((ibox405 k).hi-(ibox405 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox405
    (computed denominator ibox405) (computed denominator (FixedTape.midBox ibox405))
    (by decide +kernel)
private theorem midpoint_even_405 : ∀ k, 2 ∣ (ibox405 k).lo+(ibox405 k).hi := by decide +kernel
private theorem accepted_405 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox405) tree405 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox405 midpoint_even_405
  simp only [tree405,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox405,candidate_valid h (FixedTape.midBox ibox405),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox405 212 (FixedTape.rowsAux denominator ibox405 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox405) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_405
private noncomputable def tree404 : TapeTree := .centered (candidateRows ibox404) (candidateRows (FixedTape.midBox ibox404))
attribute [irreducible] tree404
private theorem sign_404 : 2*denominator*(computed denominator (FixedTape.midBox ibox404)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox404).gradient k).lo.natAbs ((computed denominator ibox404).gradient k).hi.natAbs : Int)*((ibox404 k).hi-(ibox404 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox404
    (computed denominator ibox404) (computed denominator (FixedTape.midBox ibox404))
    (by decide +kernel)
private theorem midpoint_even_404 : ∀ k, 2 ∣ (ibox404 k).lo+(ibox404 k).hi := by decide +kernel
private theorem accepted_404 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox404) tree404 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox404 midpoint_even_404
  simp only [tree404,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox404,candidate_valid h (FixedTape.midBox ibox404),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox404 212 (FixedTape.rowsAux denominator ibox404 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox404) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_404
private noncomputable def tree403 : TapeTree := .split 3 (((12431616634123028271385806917078617936499834880000000000000 : Int) : ℚ)/(denominator : ℚ)) tree404 tree405
attribute [irreducible] tree403
private theorem accepted_403 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox403) tree403 = true := by
  simp only [tree403,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox403 3 (12431616634123028271385806917078617936499834880000000000000 : Int) false,decode_split denominator ibox403 3 (12431616634123028271385806917078617936499834880000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_404 h,accepted_405 h⟩
private noncomputable def tree402 : TapeTree := .centered (candidateRows ibox402) (candidateRows (FixedTape.midBox ibox402))
attribute [irreducible] tree402
private theorem sign_402 : 2*denominator*(computed denominator (FixedTape.midBox ibox402)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox402).gradient k).lo.natAbs ((computed denominator ibox402).gradient k).hi.natAbs : Int)*((ibox402 k).hi-(ibox402 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox402
    (computed denominator ibox402) (computed denominator (FixedTape.midBox ibox402))
    (by decide +kernel)
private theorem midpoint_even_402 : ∀ k, 2 ∣ (ibox402 k).lo+(ibox402 k).hi := by decide +kernel
private theorem accepted_402 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox402) tree402 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox402 midpoint_even_402
  simp only [tree402,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox402,candidate_valid h (FixedTape.midBox ibox402),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox402 212 (FixedTape.rowsAux denominator ibox402 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox402) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_402
private noncomputable def tree401 : TapeTree := .centered (candidateRows ibox401) (candidateRows (FixedTape.midBox ibox401))
attribute [irreducible] tree401
private theorem sign_401 : 2*denominator*(computed denominator (FixedTape.midBox ibox401)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox401).gradient k).lo.natAbs ((computed denominator ibox401).gradient k).hi.natAbs : Int)*((ibox401 k).hi-(ibox401 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox401
    (computed denominator ibox401) (computed denominator (FixedTape.midBox ibox401))
    (by decide +kernel)
private theorem midpoint_even_401 : ∀ k, 2 ∣ (ibox401 k).lo+(ibox401 k).hi := by decide +kernel
private theorem accepted_401 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox401) tree401 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox401 midpoint_even_401
  simp only [tree401,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox401,candidate_valid h (FixedTape.midBox ibox401),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox401 212 (FixedTape.rowsAux denominator ibox401 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox401) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_401
private noncomputable def tree400 : TapeTree := .split 3 (((12431616634123028271385806917078617936499834880000000000000 : Int) : ℚ)/(denominator : ℚ)) tree401 tree402
attribute [irreducible] tree400
private theorem accepted_400 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox400) tree400 = true := by
  simp only [tree400,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox400 3 (12431616634123028271385806917078617936499834880000000000000 : Int) false,decode_split denominator ibox400 3 (12431616634123028271385806917078617936499834880000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_401 h,accepted_402 h⟩
private noncomputable def tree399 : TapeTree := .split 0 (((8602768361894631643329781649649055621321850880000000000 : Int) : ℚ)/(denominator : ℚ)) tree400 tree403
attribute [irreducible] tree399
private theorem accepted_399 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox399) tree399 = true := by
  simp only [tree399,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox399 0 (8602768361894631643329781649649055621321850880000000000 : Int) false,decode_split denominator ibox399 0 (8602768361894631643329781649649055621321850880000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_400 h,accepted_403 h⟩
private noncomputable def tree398 : TapeTree := .centered (candidateRows ibox398) (candidateRows (FixedTape.midBox ibox398))
attribute [irreducible] tree398
private theorem sign_398 : 2*denominator*(computed denominator (FixedTape.midBox ibox398)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox398).gradient k).lo.natAbs ((computed denominator ibox398).gradient k).hi.natAbs : Int)*((ibox398 k).hi-(ibox398 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox398
    (computed denominator ibox398) (computed denominator (FixedTape.midBox ibox398))
    (by decide +kernel)
private theorem midpoint_even_398 : ∀ k, 2 ∣ (ibox398 k).lo+(ibox398 k).hi := by decide +kernel
private theorem accepted_398 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox398) tree398 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox398 midpoint_even_398
  simp only [tree398,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox398,candidate_valid h (FixedTape.midBox ibox398),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox398 212 (FixedTape.rowsAux denominator ibox398 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox398) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_398
private noncomputable def tree397 : TapeTree := .centered (candidateRows ibox397) (candidateRows (FixedTape.midBox ibox397))
attribute [irreducible] tree397
private theorem sign_397 : 2*denominator*(computed denominator (FixedTape.midBox ibox397)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox397).gradient k).lo.natAbs ((computed denominator ibox397).gradient k).hi.natAbs : Int)*((ibox397 k).hi-(ibox397 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox397
    (computed denominator ibox397) (computed denominator (FixedTape.midBox ibox397))
    (by decide +kernel)
private theorem midpoint_even_397 : ∀ k, 2 ∣ (ibox397 k).lo+(ibox397 k).hi := by decide +kernel
private theorem accepted_397 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox397) tree397 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox397 midpoint_even_397
  simp only [tree397,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox397,candidate_valid h (FixedTape.midBox ibox397),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox397 212 (FixedTape.rowsAux denominator ibox397 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox397) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_397
private noncomputable def tree396 : TapeTree := .split 3 (((12431616634123028271385806917078617936499834880000000000000 : Int) : ℚ)/(denominator : ℚ)) tree397 tree398
attribute [irreducible] tree396
private theorem accepted_396 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox396) tree396 = true := by
  simp only [tree396,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox396 3 (12431616634123028271385806917078617936499834880000000000000 : Int) false,decode_split denominator ibox396 3 (12431616634123028271385806917078617936499834880000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_397 h,accepted_398 h⟩
private noncomputable def tree395 : TapeTree := .centered (candidateRows ibox395) (candidateRows (FixedTape.midBox ibox395))
attribute [irreducible] tree395
private theorem sign_395 : 2*denominator*(computed denominator (FixedTape.midBox ibox395)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox395).gradient k).lo.natAbs ((computed denominator ibox395).gradient k).hi.natAbs : Int)*((ibox395 k).hi-(ibox395 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox395
    (computed denominator ibox395) (computed denominator (FixedTape.midBox ibox395))
    (by decide +kernel)
private theorem midpoint_even_395 : ∀ k, 2 ∣ (ibox395 k).lo+(ibox395 k).hi := by decide +kernel
private theorem accepted_395 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox395) tree395 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox395 midpoint_even_395
  simp only [tree395,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox395,candidate_valid h (FixedTape.midBox ibox395),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox395 212 (FixedTape.rowsAux denominator ibox395 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox395) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_395
private noncomputable def tree394 : TapeTree := .centered (candidateRows ibox394) (candidateRows (FixedTape.midBox ibox394))
attribute [irreducible] tree394
private theorem sign_394 : 2*denominator*(computed denominator (FixedTape.midBox ibox394)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox394).gradient k).lo.natAbs ((computed denominator ibox394).gradient k).hi.natAbs : Int)*((ibox394 k).hi-(ibox394 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox394
    (computed denominator ibox394) (computed denominator (FixedTape.midBox ibox394))
    (by decide +kernel)
private theorem midpoint_even_394 : ∀ k, 2 ∣ (ibox394 k).lo+(ibox394 k).hi := by decide +kernel
private theorem accepted_394 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox394) tree394 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox394 midpoint_even_394
  simp only [tree394,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox394,candidate_valid h (FixedTape.midBox ibox394),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox394 212 (FixedTape.rowsAux denominator ibox394 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox394) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_394
private noncomputable def tree393 : TapeTree := .split 3 (((12431616634123028271385806917078617936499834880000000000000 : Int) : ℚ)/(denominator : ℚ)) tree394 tree395
attribute [irreducible] tree393
private theorem accepted_393 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox393) tree393 = true := by
  simp only [tree393,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox393 3 (12431616634123028271385806917078617936499834880000000000000 : Int) false,decode_split denominator ibox393 3 (12431616634123028271385806917078617936499834880000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_394 h,accepted_395 h⟩
private noncomputable def tree392 : TapeTree := .split 0 (((8236693112452306892549790941153351126797516800000000000 : Int) : ℚ)/(denominator : ℚ)) tree393 tree396
attribute [irreducible] tree392
private theorem accepted_392 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox392) tree392 = true := by
  simp only [tree392,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox392 0 (8236693112452306892549790941153351126797516800000000000 : Int) false,decode_split denominator ibox392 0 (8236693112452306892549790941153351126797516800000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_393 h,accepted_396 h⟩
private noncomputable def tree391 : TapeTree := .split 0 (((8419730737173469267939786295401203374059683840000000000 : Int) : ℚ)/(denominator : ℚ)) tree392 tree399
attribute [irreducible] tree391
private theorem accepted_391 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox391) tree391 = true := by
  simp only [tree391,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox391 0 (8419730737173469267939786295401203374059683840000000000 : Int) false,decode_split denominator ibox391 0 (8419730737173469267939786295401203374059683840000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_392 h,accepted_399 h⟩
private noncomputable def tree390 : TapeTree := .split 3 (((13387894836747876599953945910700050085461360640000000000000 : Int) : ℚ)/(denominator : ℚ)) tree391 tree406
attribute [irreducible] tree390
private theorem accepted_390 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox390) tree390 = true := by
  simp only [tree390,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox390 3 (13387894836747876599953945910700050085461360640000000000000 : Int) false,decode_split denominator ibox390 3 (13387894836747876599953945910700050085461360640000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_391 h,accepted_406 h⟩
private noncomputable def tree389 : TapeTree := .centered (candidateRows ibox389) (candidateRows (FixedTape.midBox ibox389))
attribute [irreducible] tree389
private theorem sign_389 : 2*denominator*(computed denominator (FixedTape.midBox ibox389)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox389).gradient k).lo.natAbs ((computed denominator ibox389).gradient k).hi.natAbs : Int)*((ibox389 k).hi-(ibox389 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox389
    (computed denominator ibox389) (computed denominator (FixedTape.midBox ibox389))
    (by decide +kernel)
private theorem midpoint_even_389 : ∀ k, 2 ∣ (ibox389 k).lo+(ibox389 k).hi := by decide +kernel
private theorem accepted_389 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox389) tree389 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox389 midpoint_even_389
  simp only [tree389,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox389,candidate_valid h (FixedTape.midBox ibox389),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox389 212 (FixedTape.rowsAux denominator ibox389 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox389) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_389
private noncomputable def tree388 : TapeTree := .centered (candidateRows ibox388) (candidateRows (FixedTape.midBox ibox388))
attribute [irreducible] tree388
private theorem sign_388 : 2*denominator*(computed denominator (FixedTape.midBox ibox388)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox388).gradient k).lo.natAbs ((computed denominator ibox388).gradient k).hi.natAbs : Int)*((ibox388 k).hi-(ibox388 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox388
    (computed denominator ibox388) (computed denominator (FixedTape.midBox ibox388))
    (by decide +kernel)
private theorem midpoint_even_388 : ∀ k, 2 ∣ (ibox388 k).lo+(ibox388 k).hi := by decide +kernel
private theorem accepted_388 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox388) tree388 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox388 midpoint_even_388
  simp only [tree388,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox388,candidate_valid h (FixedTape.midBox ibox388),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox388 212 (FixedTape.rowsAux denominator ibox388 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox388) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_388
private noncomputable def tree387 : TapeTree := .split 3 (((10519060228873331614249528929835753638576783360000000000000 : Int) : ℚ)/(denominator : ℚ)) tree388 tree389
attribute [irreducible] tree387
private theorem accepted_387 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox387) tree387 = true := by
  simp only [tree387,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox387 3 (10519060228873331614249528929835753638576783360000000000000 : Int) false,decode_split denominator ibox387 3 (10519060228873331614249528929835753638576783360000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_388 h,accepted_389 h⟩
private noncomputable def tree386 : TapeTree := .centered (candidateRows ibox386) (candidateRows (FixedTape.midBox ibox386))
attribute [irreducible] tree386
private theorem sign_386 : 2*denominator*(computed denominator (FixedTape.midBox ibox386)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox386).gradient k).lo.natAbs ((computed denominator ibox386).gradient k).hi.natAbs : Int)*((ibox386 k).hi-(ibox386 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox386
    (computed denominator ibox386) (computed denominator (FixedTape.midBox ibox386))
    (by decide +kernel)
private theorem midpoint_even_386 : ∀ k, 2 ∣ (ibox386 k).lo+(ibox386 k).hi := by decide +kernel
private theorem accepted_386 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox386) tree386 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox386 midpoint_even_386
  simp only [tree386,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox386,candidate_valid h (FixedTape.midBox ibox386),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox386 212 (FixedTape.rowsAux denominator ibox386 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox386) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_386
private noncomputable def tree385 : TapeTree := .centered (candidateRows ibox385) (candidateRows (FixedTape.midBox ibox385))
attribute [irreducible] tree385
private theorem sign_385 : 2*denominator*(computed denominator (FixedTape.midBox ibox385)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox385).gradient k).lo.natAbs ((computed denominator ibox385).gradient k).hi.natAbs : Int)*((ibox385 k).hi-(ibox385 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox385
    (computed denominator ibox385) (computed denominator (FixedTape.midBox ibox385))
    (by decide +kernel)
private theorem midpoint_even_385 : ∀ k, 2 ∣ (ibox385 k).lo+(ibox385 k).hi := by decide +kernel
private theorem accepted_385 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox385) tree385 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox385 midpoint_even_385
  simp only [tree385,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox385,candidate_valid h (FixedTape.midBox ibox385),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox385 212 (FixedTape.rowsAux denominator ibox385 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox385) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_385
private noncomputable def tree384 : TapeTree := .split 3 (((10519060228873331614249528929835753638576783360000000000000 : Int) : ℚ)/(denominator : ℚ)) tree385 tree386
attribute [irreducible] tree384
private theorem accepted_384 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox384) tree384 = true := by
  simp only [tree384,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox384 3 (10519060228873331614249528929835753638576783360000000000000 : Int) false,decode_split denominator ibox384 3 (10519060228873331614249528929835753638576783360000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_385 h,accepted_386 h⟩
private noncomputable def tree383 : TapeTree := .split 0 (((8602768361894631643329781649649055621321850880000000000 : Int) : ℚ)/(denominator : ℚ)) tree384 tree387
attribute [irreducible] tree383
private theorem accepted_383 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox383) tree383 = true := by
  simp only [tree383,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox383 0 (8602768361894631643329781649649055621321850880000000000 : Int) false,decode_split denominator ibox383 0 (8602768361894631643329781649649055621321850880000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_384 h,accepted_387 h⟩
private noncomputable def tree382 : TapeTree := .centered (candidateRows ibox382) (candidateRows (FixedTape.midBox ibox382))
attribute [irreducible] tree382
private theorem sign_382 : 2*denominator*(computed denominator (FixedTape.midBox ibox382)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox382).gradient k).lo.natAbs ((computed denominator ibox382).gradient k).hi.natAbs : Int)*((ibox382 k).hi-(ibox382 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox382
    (computed denominator ibox382) (computed denominator (FixedTape.midBox ibox382))
    (by decide +kernel)
private theorem midpoint_even_382 : ∀ k, 2 ∣ (ibox382 k).lo+(ibox382 k).hi := by decide +kernel
private theorem accepted_382 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox382) tree382 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox382 midpoint_even_382
  simp only [tree382,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox382,candidate_valid h (FixedTape.midBox ibox382),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox382 212 (FixedTape.rowsAux denominator ibox382 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox382) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_382
private noncomputable def tree381 : TapeTree := .centered (candidateRows ibox381) (candidateRows (FixedTape.midBox ibox381))
attribute [irreducible] tree381
private theorem sign_381 : 2*denominator*(computed denominator (FixedTape.midBox ibox381)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox381).gradient k).lo.natAbs ((computed denominator ibox381).gradient k).hi.natAbs : Int)*((ibox381 k).hi-(ibox381 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox381
    (computed denominator ibox381) (computed denominator (FixedTape.midBox ibox381))
    (by decide +kernel)
private theorem midpoint_even_381 : ∀ k, 2 ∣ (ibox381 k).lo+(ibox381 k).hi := by decide +kernel
private theorem accepted_381 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox381) tree381 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox381 midpoint_even_381
  simp only [tree381,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox381,candidate_valid h (FixedTape.midBox ibox381),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox381 212 (FixedTape.rowsAux denominator ibox381 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox381) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_381
private noncomputable def tree380 : TapeTree := .split 3 (((8606503823623634957113250942592889340653731840000000000000 : Int) : ℚ)/(denominator : ℚ)) tree381 tree382
attribute [irreducible] tree380
private theorem accepted_380 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox380) tree380 = true := by
  simp only [tree380,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox380 3 (8606503823623634957113250942592889340653731840000000000000 : Int) false,decode_split denominator ibox380 3 (8606503823623634957113250942592889340653731840000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_381 h,accepted_382 h⟩
private noncomputable def tree379 : TapeTree := .centered (candidateRows ibox379) (candidateRows (FixedTape.midBox ibox379))
attribute [irreducible] tree379
private theorem sign_379 : 2*denominator*(computed denominator (FixedTape.midBox ibox379)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox379).gradient k).lo.natAbs ((computed denominator ibox379).gradient k).hi.natAbs : Int)*((ibox379 k).hi-(ibox379 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox379
    (computed denominator ibox379) (computed denominator (FixedTape.midBox ibox379))
    (by decide +kernel)
private theorem midpoint_even_379 : ∀ k, 2 ∣ (ibox379 k).lo+(ibox379 k).hi := by decide +kernel
private theorem accepted_379 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox379) tree379 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox379 midpoint_even_379
  simp only [tree379,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox379,candidate_valid h (FixedTape.midBox ibox379),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox379 212 (FixedTape.rowsAux denominator ibox379 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox379) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_379
private noncomputable def tree378 : TapeTree := .centered (candidateRows ibox378) (candidateRows (FixedTape.midBox ibox378))
attribute [irreducible] tree378
private theorem sign_378 : 2*denominator*(computed denominator (FixedTape.midBox ibox378)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox378).gradient k).lo.natAbs ((computed denominator ibox378).gradient k).hi.natAbs : Int)*((ibox378 k).hi-(ibox378 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox378
    (computed denominator ibox378) (computed denominator (FixedTape.midBox ibox378))
    (by decide +kernel)
private theorem midpoint_even_378 : ∀ k, 2 ∣ (ibox378 k).lo+(ibox378 k).hi := by decide +kernel
private theorem accepted_378 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox378) tree378 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox378 midpoint_even_378
  simp only [tree378,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox378,candidate_valid h (FixedTape.midBox ibox378),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox378 212 (FixedTape.rowsAux denominator ibox378 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox378) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_378
private noncomputable def tree377 : TapeTree := .split 3 (((8606503823623634957113250942592889340653731840000000000000 : Int) : ℚ)/(denominator : ℚ)) tree378 tree379
attribute [irreducible] tree377
private theorem accepted_377 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox377) tree377 = true := by
  simp only [tree377,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox377 3 (8606503823623634957113250942592889340653731840000000000000 : Int) false,decode_split denominator ibox377 3 (8606503823623634957113250942592889340653731840000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_378 h,accepted_379 h⟩
private noncomputable def tree376 : TapeTree := .split 0 (((8602768361894631643329781649649055621321850880000000000 : Int) : ℚ)/(denominator : ℚ)) tree377 tree380
attribute [irreducible] tree376
private theorem accepted_376 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox376) tree376 = true := by
  simp only [tree376,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox376 0 (8602768361894631643329781649649055621321850880000000000 : Int) false,decode_split denominator ibox376 0 (8602768361894631643329781649649055621321850880000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_377 h,accepted_380 h⟩
private noncomputable def tree375 : TapeTree := .split 3 (((9562782026248483285681389936214321489615257600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree376 tree383
attribute [irreducible] tree375
private theorem accepted_375 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox375) tree375 = true := by
  simp only [tree375,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox375 3 (9562782026248483285681389936214321489615257600000000000000 : Int) false,decode_split denominator ibox375 3 (9562782026248483285681389936214321489615257600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_376 h,accepted_383 h⟩
private noncomputable def tree374 : TapeTree := .centered (candidateRows ibox374) (candidateRows (FixedTape.midBox ibox374))
attribute [irreducible] tree374
private theorem sign_374 : 2*denominator*(computed denominator (FixedTape.midBox ibox374)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox374).gradient k).lo.natAbs ((computed denominator ibox374).gradient k).hi.natAbs : Int)*((ibox374 k).hi-(ibox374 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox374
    (computed denominator ibox374) (computed denominator (FixedTape.midBox ibox374))
    (by decide +kernel)
private theorem midpoint_even_374 : ∀ k, 2 ∣ (ibox374 k).lo+(ibox374 k).hi := by decide +kernel
private theorem accepted_374 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox374) tree374 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox374 midpoint_even_374
  simp only [tree374,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox374,candidate_valid h (FixedTape.midBox ibox374),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox374 212 (FixedTape.rowsAux denominator ibox374 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox374) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_374
private noncomputable def tree373 : TapeTree := .centered (candidateRows ibox373) (candidateRows (FixedTape.midBox ibox373))
attribute [irreducible] tree373
private theorem sign_373 : 2*denominator*(computed denominator (FixedTape.midBox ibox373)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox373).gradient k).lo.natAbs ((computed denominator ibox373).gradient k).hi.natAbs : Int)*((ibox373 k).hi-(ibox373 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox373
    (computed denominator ibox373) (computed denominator (FixedTape.midBox ibox373))
    (by decide +kernel)
private theorem midpoint_even_373 : ∀ k, 2 ∣ (ibox373 k).lo+(ibox373 k).hi := by decide +kernel
private theorem accepted_373 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox373) tree373 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox373 midpoint_even_373
  simp only [tree373,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox373,candidate_valid h (FixedTape.midBox ibox373),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox373 212 (FixedTape.rowsAux denominator ibox373 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox373) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_373
private noncomputable def tree372 : TapeTree := .split 3 (((10519060228873331614249528929835753638576783360000000000000 : Int) : ℚ)/(denominator : ℚ)) tree373 tree374
attribute [irreducible] tree372
private theorem accepted_372 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox372) tree372 = true := by
  simp only [tree372,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox372 3 (10519060228873331614249528929835753638576783360000000000000 : Int) false,decode_split denominator ibox372 3 (10519060228873331614249528929835753638576783360000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_373 h,accepted_374 h⟩
private noncomputable def tree371 : TapeTree := .centered (candidateRows ibox371) (candidateRows (FixedTape.midBox ibox371))
attribute [irreducible] tree371
private theorem sign_371 : 2*denominator*(computed denominator (FixedTape.midBox ibox371)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox371).gradient k).lo.natAbs ((computed denominator ibox371).gradient k).hi.natAbs : Int)*((ibox371 k).hi-(ibox371 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox371
    (computed denominator ibox371) (computed denominator (FixedTape.midBox ibox371))
    (by decide +kernel)
private theorem midpoint_even_371 : ∀ k, 2 ∣ (ibox371 k).lo+(ibox371 k).hi := by decide +kernel
private theorem accepted_371 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox371) tree371 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox371 midpoint_even_371
  simp only [tree371,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox371,candidate_valid h (FixedTape.midBox ibox371),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox371 212 (FixedTape.rowsAux denominator ibox371 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox371) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_371
private noncomputable def tree370 : TapeTree := .centered (candidateRows ibox370) (candidateRows (FixedTape.midBox ibox370))
attribute [irreducible] tree370
private theorem sign_370 : 2*denominator*(computed denominator (FixedTape.midBox ibox370)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox370).gradient k).lo.natAbs ((computed denominator ibox370).gradient k).hi.natAbs : Int)*((ibox370 k).hi-(ibox370 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox370
    (computed denominator ibox370) (computed denominator (FixedTape.midBox ibox370))
    (by decide +kernel)
private theorem midpoint_even_370 : ∀ k, 2 ∣ (ibox370 k).lo+(ibox370 k).hi := by decide +kernel
private theorem accepted_370 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox370) tree370 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox370 midpoint_even_370
  simp only [tree370,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox370,candidate_valid h (FixedTape.midBox ibox370),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox370 212 (FixedTape.rowsAux denominator ibox370 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox370) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_370
private noncomputable def tree369 : TapeTree := .split 3 (((10519060228873331614249528929835753638576783360000000000000 : Int) : ℚ)/(denominator : ℚ)) tree370 tree371
attribute [irreducible] tree369
private theorem accepted_369 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox369) tree369 = true := by
  simp only [tree369,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox369 3 (10519060228873331614249528929835753638576783360000000000000 : Int) false,decode_split denominator ibox369 3 (10519060228873331614249528929835753638576783360000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_370 h,accepted_371 h⟩
private noncomputable def tree368 : TapeTree := .split 0 (((8236693112452306892549790941153351126797516800000000000 : Int) : ℚ)/(denominator : ℚ)) tree369 tree372
attribute [irreducible] tree368
private theorem accepted_368 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox368) tree368 = true := by
  simp only [tree368,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox368 0 (8236693112452306892549790941153351126797516800000000000 : Int) false,decode_split denominator ibox368 0 (8236693112452306892549790941153351126797516800000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_369 h,accepted_372 h⟩
private noncomputable def tree367 : TapeTree := .centered (candidateRows ibox367) (candidateRows (FixedTape.midBox ibox367))
attribute [irreducible] tree367
private theorem sign_367 : 2*denominator*(computed denominator (FixedTape.midBox ibox367)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox367).gradient k).lo.natAbs ((computed denominator ibox367).gradient k).hi.natAbs : Int)*((ibox367 k).hi-(ibox367 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox367
    (computed denominator ibox367) (computed denominator (FixedTape.midBox ibox367))
    (by decide +kernel)
private theorem midpoint_even_367 : ∀ k, 2 ∣ (ibox367 k).lo+(ibox367 k).hi := by decide +kernel
private theorem accepted_367 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox367) tree367 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox367 midpoint_even_367
  simp only [tree367,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox367,candidate_valid h (FixedTape.midBox ibox367),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox367 212 (FixedTape.rowsAux denominator ibox367 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox367) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_367
private noncomputable def tree366 : TapeTree := .centered (candidateRows ibox366) (candidateRows (FixedTape.midBox ibox366))
attribute [irreducible] tree366
private theorem sign_366 : 2*denominator*(computed denominator (FixedTape.midBox ibox366)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox366).gradient k).lo.natAbs ((computed denominator ibox366).gradient k).hi.natAbs : Int)*((ibox366 k).hi-(ibox366 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox366
    (computed denominator ibox366) (computed denominator (FixedTape.midBox ibox366))
    (by decide +kernel)
private theorem midpoint_even_366 : ∀ k, 2 ∣ (ibox366 k).lo+(ibox366 k).hi := by decide +kernel
private theorem accepted_366 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox366) tree366 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox366 midpoint_even_366
  simp only [tree366,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox366,candidate_valid h (FixedTape.midBox ibox366),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox366 212 (FixedTape.rowsAux denominator ibox366 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox366) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_366
private noncomputable def tree365 : TapeTree := .split 3 (((8606503823623634957113250942592889340653731840000000000000 : Int) : ℚ)/(denominator : ℚ)) tree366 tree367
attribute [irreducible] tree365
private theorem accepted_365 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox365) tree365 = true := by
  simp only [tree365,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox365 3 (8606503823623634957113250942592889340653731840000000000000 : Int) false,decode_split denominator ibox365 3 (8606503823623634957113250942592889340653731840000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_366 h,accepted_367 h⟩
private noncomputable def tree364 : TapeTree := .centered (candidateRows ibox364) (candidateRows (FixedTape.midBox ibox364))
attribute [irreducible] tree364
private theorem sign_364 : 2*denominator*(computed denominator (FixedTape.midBox ibox364)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox364).gradient k).lo.natAbs ((computed denominator ibox364).gradient k).hi.natAbs : Int)*((ibox364 k).hi-(ibox364 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox364
    (computed denominator ibox364) (computed denominator (FixedTape.midBox ibox364))
    (by decide +kernel)
private theorem midpoint_even_364 : ∀ k, 2 ∣ (ibox364 k).lo+(ibox364 k).hi := by decide +kernel
private theorem accepted_364 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox364) tree364 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox364 midpoint_even_364
  simp only [tree364,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox364,candidate_valid h (FixedTape.midBox ibox364),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox364 212 (FixedTape.rowsAux denominator ibox364 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox364) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_364
private noncomputable def tree363 : TapeTree := .centered (candidateRows ibox363) (candidateRows (FixedTape.midBox ibox363))
attribute [irreducible] tree363
private theorem sign_363 : 2*denominator*(computed denominator (FixedTape.midBox ibox363)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox363).gradient k).lo.natAbs ((computed denominator ibox363).gradient k).hi.natAbs : Int)*((ibox363 k).hi-(ibox363 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox363
    (computed denominator ibox363) (computed denominator (FixedTape.midBox ibox363))
    (by decide +kernel)
private theorem midpoint_even_363 : ∀ k, 2 ∣ (ibox363 k).lo+(ibox363 k).hi := by decide +kernel
private theorem accepted_363 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox363) tree363 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox363 midpoint_even_363
  simp only [tree363,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox363,candidate_valid h (FixedTape.midBox ibox363),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox363 212 (FixedTape.rowsAux denominator ibox363 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox363) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_363
private noncomputable def tree362 : TapeTree := .split 3 (((8606503823623634957113250942592889340653731840000000000000 : Int) : ℚ)/(denominator : ℚ)) tree363 tree364
attribute [irreducible] tree362
private theorem accepted_362 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox362) tree362 = true := by
  simp only [tree362,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox362 3 (8606503823623634957113250942592889340653731840000000000000 : Int) false,decode_split denominator ibox362 3 (8606503823623634957113250942592889340653731840000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_363 h,accepted_364 h⟩
private noncomputable def tree361 : TapeTree := .split 0 (((8236693112452306892549790941153351126797516800000000000 : Int) : ℚ)/(denominator : ℚ)) tree362 tree365
attribute [irreducible] tree361
private theorem accepted_361 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox361) tree361 = true := by
  simp only [tree361,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox361 0 (8236693112452306892549790941153351126797516800000000000 : Int) false,decode_split denominator ibox361 0 (8236693112452306892549790941153351126797516800000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_362 h,accepted_365 h⟩
private noncomputable def tree360 : TapeTree := .split 3 (((9562782026248483285681389936214321489615257600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree361 tree368
attribute [irreducible] tree360
private theorem accepted_360 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox360) tree360 = true := by
  simp only [tree360,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox360 3 (9562782026248483285681389936214321489615257600000000000000 : Int) false,decode_split denominator ibox360 3 (9562782026248483285681389936214321489615257600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_361 h,accepted_368 h⟩
private noncomputable def tree359 : TapeTree := .split 0 (((8419730737173469267939786295401203374059683840000000000 : Int) : ℚ)/(denominator : ℚ)) tree360 tree375
attribute [irreducible] tree359
private theorem accepted_359 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox359) tree359 = true := by
  simp only [tree359,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox359 0 (8419730737173469267939786295401203374059683840000000000 : Int) false,decode_split denominator ibox359 0 (8419730737173469267939786295401203374059683840000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_360 h,accepted_375 h⟩
private noncomputable def tree358 : TapeTree := .split 3 (((11475338431498179942817667923457185787538309120000000000000 : Int) : ℚ)/(denominator : ℚ)) tree359 tree390
attribute [irreducible] tree358
private theorem accepted_358 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox358) tree358 = true := by
  simp only [tree358,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox358 3 (11475338431498179942817667923457185787538309120000000000000 : Int) false,decode_split denominator ibox358 3 (11475338431498179942817667923457185787538309120000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_359 h,accepted_390 h⟩
private noncomputable def tree357 : TapeTree := .centered (candidateRows ibox357) (candidateRows (FixedTape.midBox ibox357))
attribute [irreducible] tree357
private theorem sign_357 : 2*denominator*(computed denominator (FixedTape.midBox ibox357)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox357).gradient k).lo.natAbs ((computed denominator ibox357).gradient k).hi.natAbs : Int)*((ibox357 k).hi-(ibox357 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox357
    (computed denominator ibox357) (computed denominator (FixedTape.midBox ibox357))
    (by decide +kernel)
private theorem midpoint_even_357 : ∀ k, 2 ∣ (ibox357 k).lo+(ibox357 k).hi := by decide +kernel
private theorem accepted_357 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox357) tree357 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox357 midpoint_even_357
  simp only [tree357,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox357,candidate_valid h (FixedTape.midBox ibox357),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox357 212 (FixedTape.rowsAux denominator ibox357 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox357) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_357
private noncomputable def tree356 : TapeTree := .centered (candidateRows ibox356) (candidateRows (FixedTape.midBox ibox356))
attribute [irreducible] tree356
private theorem sign_356 : 2*denominator*(computed denominator (FixedTape.midBox ibox356)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox356).gradient k).lo.natAbs ((computed denominator ibox356).gradient k).hi.natAbs : Int)*((ibox356 k).hi-(ibox356 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox356
    (computed denominator ibox356) (computed denominator (FixedTape.midBox ibox356))
    (by decide +kernel)
private theorem midpoint_even_356 : ∀ k, 2 ∣ (ibox356 k).lo+(ibox356 k).hi := by decide +kernel
private theorem accepted_356 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox356) tree356 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox356 midpoint_even_356
  simp only [tree356,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox356,candidate_valid h (FixedTape.midBox ibox356),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox356 212 (FixedTape.rowsAux denominator ibox356 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox356) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_356
private noncomputable def tree355 : TapeTree := .split 3 (((6693947418373938299976972955350025042730680320000000000000 : Int) : ℚ)/(denominator : ℚ)) tree356 tree357
attribute [irreducible] tree355
private theorem accepted_355 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox355) tree355 = true := by
  simp only [tree355,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox355 3 (6693947418373938299976972955350025042730680320000000000000 : Int) false,decode_split denominator ibox355 3 (6693947418373938299976972955350025042730680320000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_356 h,accepted_357 h⟩
private noncomputable def tree354 : TapeTree := .centered (candidateRows ibox354) (candidateRows (FixedTape.midBox ibox354))
attribute [irreducible] tree354
private theorem sign_354 : 2*denominator*(computed denominator (FixedTape.midBox ibox354)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox354).gradient k).lo.natAbs ((computed denominator ibox354).gradient k).hi.natAbs : Int)*((ibox354 k).hi-(ibox354 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox354
    (computed denominator ibox354) (computed denominator (FixedTape.midBox ibox354))
    (by decide +kernel)
private theorem midpoint_even_354 : ∀ k, 2 ∣ (ibox354 k).lo+(ibox354 k).hi := by decide +kernel
private theorem accepted_354 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox354) tree354 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox354 midpoint_even_354
  simp only [tree354,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox354,candidate_valid h (FixedTape.midBox ibox354),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox354 212 (FixedTape.rowsAux denominator ibox354 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox354) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_354
private noncomputable def tree353 : TapeTree := .centered (candidateRows ibox353) (candidateRows (FixedTape.midBox ibox353))
attribute [irreducible] tree353
private theorem sign_353 : 2*denominator*(computed denominator (FixedTape.midBox ibox353)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox353).gradient k).lo.natAbs ((computed denominator ibox353).gradient k).hi.natAbs : Int)*((ibox353 k).hi-(ibox353 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox353
    (computed denominator ibox353) (computed denominator (FixedTape.midBox ibox353))
    (by decide +kernel)
private theorem midpoint_even_353 : ∀ k, 2 ∣ (ibox353 k).lo+(ibox353 k).hi := by decide +kernel
private theorem accepted_353 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox353) tree353 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox353 midpoint_even_353
  simp only [tree353,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox353,candidate_valid h (FixedTape.midBox ibox353),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox353 212 (FixedTape.rowsAux denominator ibox353 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox353) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_353
private noncomputable def tree352 : TapeTree := .split 3 (((6693947418373938299976972955350025042730680320000000000000 : Int) : ℚ)/(denominator : ℚ)) tree353 tree354
attribute [irreducible] tree352
private theorem accepted_352 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox352) tree352 = true := by
  simp only [tree352,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox352 3 (6693947418373938299976972955350025042730680320000000000000 : Int) false,decode_split denominator ibox352 3 (6693947418373938299976972955350025042730680320000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_353 h,accepted_354 h⟩
private noncomputable def tree351 : TapeTree := .split 0 (((8602768361894631643329781649649055621321850880000000000 : Int) : ℚ)/(denominator : ℚ)) tree352 tree355
attribute [irreducible] tree351
private theorem accepted_351 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox351) tree351 = true := by
  simp only [tree351,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox351 0 (8602768361894631643329781649649055621321850880000000000 : Int) false,decode_split denominator ibox351 0 (8602768361894631643329781649649055621321850880000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_352 h,accepted_355 h⟩
private noncomputable def tree350 : TapeTree := .centered (candidateRows ibox350) (candidateRows (FixedTape.midBox ibox350))
attribute [irreducible] tree350
private theorem sign_350 : 2*denominator*(computed denominator (FixedTape.midBox ibox350)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox350).gradient k).lo.natAbs ((computed denominator ibox350).gradient k).hi.natAbs : Int)*((ibox350 k).hi-(ibox350 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox350
    (computed denominator ibox350) (computed denominator (FixedTape.midBox ibox350))
    (by decide +kernel)
private theorem midpoint_even_350 : ∀ k, 2 ∣ (ibox350 k).lo+(ibox350 k).hi := by decide +kernel
private theorem accepted_350 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox350) tree350 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox350 midpoint_even_350
  simp only [tree350,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox350,candidate_valid h (FixedTape.midBox ibox350),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox350 212 (FixedTape.rowsAux denominator ibox350 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox350) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_350
private noncomputable def tree349 : TapeTree := .centered (candidateRows ibox349) (candidateRows (FixedTape.midBox ibox349))
attribute [irreducible] tree349
private theorem sign_349 : 2*denominator*(computed denominator (FixedTape.midBox ibox349)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox349).gradient k).lo.natAbs ((computed denominator ibox349).gradient k).hi.natAbs : Int)*((ibox349 k).hi-(ibox349 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox349
    (computed denominator ibox349) (computed denominator (FixedTape.midBox ibox349))
    (by decide +kernel)
private theorem midpoint_even_349 : ∀ k, 2 ∣ (ibox349 k).lo+(ibox349 k).hi := by decide +kernel
private theorem accepted_349 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox349) tree349 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox349 midpoint_even_349
  simp only [tree349,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox349,candidate_valid h (FixedTape.midBox ibox349),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox349 212 (FixedTape.rowsAux denominator ibox349 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox349) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_349
private noncomputable def tree348 : TapeTree := .split 3 (((4781391013124241642840694968107160744807628800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree349 tree350
attribute [irreducible] tree348
private theorem accepted_348 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox348) tree348 = true := by
  simp only [tree348,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox348 3 (4781391013124241642840694968107160744807628800000000000000 : Int) false,decode_split denominator ibox348 3 (4781391013124241642840694968107160744807628800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_349 h,accepted_350 h⟩
private noncomputable def tree347 : TapeTree := .centered (candidateRows ibox347) (candidateRows (FixedTape.midBox ibox347))
attribute [irreducible] tree347
private theorem sign_347 : 2*denominator*(computed denominator (FixedTape.midBox ibox347)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox347).gradient k).lo.natAbs ((computed denominator ibox347).gradient k).hi.natAbs : Int)*((ibox347 k).hi-(ibox347 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox347
    (computed denominator ibox347) (computed denominator (FixedTape.midBox ibox347))
    (by decide +kernel)
private theorem midpoint_even_347 : ∀ k, 2 ∣ (ibox347 k).lo+(ibox347 k).hi := by decide +kernel
private theorem accepted_347 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox347) tree347 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox347 midpoint_even_347
  simp only [tree347,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox347,candidate_valid h (FixedTape.midBox ibox347),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox347 212 (FixedTape.rowsAux denominator ibox347 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox347) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_347
private noncomputable def tree346 : TapeTree := .centered (candidateRows ibox346) (candidateRows (FixedTape.midBox ibox346))
attribute [irreducible] tree346
private theorem sign_346 : 2*denominator*(computed denominator (FixedTape.midBox ibox346)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox346).gradient k).lo.natAbs ((computed denominator ibox346).gradient k).hi.natAbs : Int)*((ibox346 k).hi-(ibox346 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox346
    (computed denominator ibox346) (computed denominator (FixedTape.midBox ibox346))
    (by decide +kernel)
private theorem midpoint_even_346 : ∀ k, 2 ∣ (ibox346 k).lo+(ibox346 k).hi := by decide +kernel
private theorem accepted_346 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox346) tree346 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox346 midpoint_even_346
  simp only [tree346,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox346,candidate_valid h (FixedTape.midBox ibox346),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox346 212 (FixedTape.rowsAux denominator ibox346 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox346) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_346
private noncomputable def tree345 : TapeTree := .split 3 (((4781391013124241642840694968107160744807628800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree346 tree347
attribute [irreducible] tree345
private theorem accepted_345 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox345) tree345 = true := by
  simp only [tree345,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox345 3 (4781391013124241642840694968107160744807628800000000000000 : Int) false,decode_split denominator ibox345 3 (4781391013124241642840694968107160744807628800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_346 h,accepted_347 h⟩
private noncomputable def tree344 : TapeTree := .split 0 (((8602768361894631643329781649649055621321850880000000000 : Int) : ℚ)/(denominator : ℚ)) tree345 tree348
attribute [irreducible] tree344
private theorem accepted_344 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox344) tree344 = true := by
  simp only [tree344,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox344 0 (8602768361894631643329781649649055621321850880000000000 : Int) false,decode_split denominator ibox344 0 (8602768361894631643329781649649055621321850880000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_345 h,accepted_348 h⟩
private noncomputable def tree343 : TapeTree := .split 3 (((5737669215749089971408833961728592893769154560000000000000 : Int) : ℚ)/(denominator : ℚ)) tree344 tree351
attribute [irreducible] tree343
private theorem accepted_343 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox343) tree343 = true := by
  simp only [tree343,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox343 3 (5737669215749089971408833961728592893769154560000000000000 : Int) false,decode_split denominator ibox343 3 (5737669215749089971408833961728592893769154560000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_344 h,accepted_351 h⟩
private noncomputable def tree342 : TapeTree := .centered (candidateRows ibox342) (candidateRows (FixedTape.midBox ibox342))
attribute [irreducible] tree342
private theorem sign_342 : 2*denominator*(computed denominator (FixedTape.midBox ibox342)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox342).gradient k).lo.natAbs ((computed denominator ibox342).gradient k).hi.natAbs : Int)*((ibox342 k).hi-(ibox342 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox342
    (computed denominator ibox342) (computed denominator (FixedTape.midBox ibox342))
    (by decide +kernel)
private theorem midpoint_even_342 : ∀ k, 2 ∣ (ibox342 k).lo+(ibox342 k).hi := by decide +kernel
private theorem accepted_342 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox342) tree342 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox342 midpoint_even_342
  simp only [tree342,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox342,candidate_valid h (FixedTape.midBox ibox342),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox342 212 (FixedTape.rowsAux denominator ibox342 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox342) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_342
private noncomputable def tree341 : TapeTree := .centered (candidateRows ibox341) (candidateRows (FixedTape.midBox ibox341))
attribute [irreducible] tree341
private theorem sign_341 : 2*denominator*(computed denominator (FixedTape.midBox ibox341)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox341).gradient k).lo.natAbs ((computed denominator ibox341).gradient k).hi.natAbs : Int)*((ibox341 k).hi-(ibox341 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox341
    (computed denominator ibox341) (computed denominator (FixedTape.midBox ibox341))
    (by decide +kernel)
private theorem midpoint_even_341 : ∀ k, 2 ∣ (ibox341 k).lo+(ibox341 k).hi := by decide +kernel
private theorem accepted_341 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox341) tree341 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox341 midpoint_even_341
  simp only [tree341,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox341,candidate_valid h (FixedTape.midBox ibox341),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox341 212 (FixedTape.rowsAux denominator ibox341 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox341) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_341
private noncomputable def tree340 : TapeTree := .split 3 (((6693947418373938299976972955350025042730680320000000000000 : Int) : ℚ)/(denominator : ℚ)) tree341 tree342
attribute [irreducible] tree340
private theorem accepted_340 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox340) tree340 = true := by
  simp only [tree340,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox340 3 (6693947418373938299976972955350025042730680320000000000000 : Int) false,decode_split denominator ibox340 3 (6693947418373938299976972955350025042730680320000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_341 h,accepted_342 h⟩
private noncomputable def tree339 : TapeTree := .centered (candidateRows ibox339) (candidateRows (FixedTape.midBox ibox339))
attribute [irreducible] tree339
private theorem sign_339 : 2*denominator*(computed denominator (FixedTape.midBox ibox339)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox339).gradient k).lo.natAbs ((computed denominator ibox339).gradient k).hi.natAbs : Int)*((ibox339 k).hi-(ibox339 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox339
    (computed denominator ibox339) (computed denominator (FixedTape.midBox ibox339))
    (by decide +kernel)
private theorem midpoint_even_339 : ∀ k, 2 ∣ (ibox339 k).lo+(ibox339 k).hi := by decide +kernel
private theorem accepted_339 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox339) tree339 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox339 midpoint_even_339
  simp only [tree339,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox339,candidate_valid h (FixedTape.midBox ibox339),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox339 212 (FixedTape.rowsAux denominator ibox339 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox339) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_339
private noncomputable def tree338 : TapeTree := .centered (candidateRows ibox338) (candidateRows (FixedTape.midBox ibox338))
attribute [irreducible] tree338
private theorem sign_338 : 2*denominator*(computed denominator (FixedTape.midBox ibox338)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox338).gradient k).lo.natAbs ((computed denominator ibox338).gradient k).hi.natAbs : Int)*((ibox338 k).hi-(ibox338 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox338
    (computed denominator ibox338) (computed denominator (FixedTape.midBox ibox338))
    (by decide +kernel)
private theorem midpoint_even_338 : ∀ k, 2 ∣ (ibox338 k).lo+(ibox338 k).hi := by decide +kernel
private theorem accepted_338 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox338) tree338 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox338 midpoint_even_338
  simp only [tree338,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox338,candidate_valid h (FixedTape.midBox ibox338),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox338 212 (FixedTape.rowsAux denominator ibox338 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox338) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_338
private noncomputable def tree337 : TapeTree := .split 3 (((6693947418373938299976972955350025042730680320000000000000 : Int) : ℚ)/(denominator : ℚ)) tree338 tree339
attribute [irreducible] tree337
private theorem accepted_337 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox337) tree337 = true := by
  simp only [tree337,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox337 3 (6693947418373938299976972955350025042730680320000000000000 : Int) false,decode_split denominator ibox337 3 (6693947418373938299976972955350025042730680320000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_338 h,accepted_339 h⟩
private noncomputable def tree336 : TapeTree := .split 0 (((8236693112452306892549790941153351126797516800000000000 : Int) : ℚ)/(denominator : ℚ)) tree337 tree340
attribute [irreducible] tree336
private theorem accepted_336 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox336) tree336 = true := by
  simp only [tree336,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox336 0 (8236693112452306892549790941153351126797516800000000000 : Int) false,decode_split denominator ibox336 0 (8236693112452306892549790941153351126797516800000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_337 h,accepted_340 h⟩
private noncomputable def tree335 : TapeTree := .centered (candidateRows ibox335) (candidateRows (FixedTape.midBox ibox335))
attribute [irreducible] tree335
private theorem sign_335 : 2*denominator*(computed denominator (FixedTape.midBox ibox335)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox335).gradient k).lo.natAbs ((computed denominator ibox335).gradient k).hi.natAbs : Int)*((ibox335 k).hi-(ibox335 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox335
    (computed denominator ibox335) (computed denominator (FixedTape.midBox ibox335))
    (by decide +kernel)
private theorem midpoint_even_335 : ∀ k, 2 ∣ (ibox335 k).lo+(ibox335 k).hi := by decide +kernel
private theorem accepted_335 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox335) tree335 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox335 midpoint_even_335
  simp only [tree335,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox335,candidate_valid h (FixedTape.midBox ibox335),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox335 212 (FixedTape.rowsAux denominator ibox335 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox335) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_335
private noncomputable def tree334 : TapeTree := .centered (candidateRows ibox334) (candidateRows (FixedTape.midBox ibox334))
attribute [irreducible] tree334
private theorem sign_334 : 2*denominator*(computed denominator (FixedTape.midBox ibox334)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox334).gradient k).lo.natAbs ((computed denominator ibox334).gradient k).hi.natAbs : Int)*((ibox334 k).hi-(ibox334 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox334
    (computed denominator ibox334) (computed denominator (FixedTape.midBox ibox334))
    (by decide +kernel)
private theorem midpoint_even_334 : ∀ k, 2 ∣ (ibox334 k).lo+(ibox334 k).hi := by decide +kernel
private theorem accepted_334 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox334) tree334 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox334 midpoint_even_334
  simp only [tree334,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox334,candidate_valid h (FixedTape.midBox ibox334),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox334 212 (FixedTape.rowsAux denominator ibox334 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox334) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_334
private noncomputable def tree333 : TapeTree := .split 3 (((4781391013124241642840694968107160744807628800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree334 tree335
attribute [irreducible] tree333
private theorem accepted_333 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox333) tree333 = true := by
  simp only [tree333,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox333 3 (4781391013124241642840694968107160744807628800000000000000 : Int) false,decode_split denominator ibox333 3 (4781391013124241642840694968107160744807628800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_334 h,accepted_335 h⟩
private noncomputable def tree332 : TapeTree := .centered (candidateRows ibox332) (candidateRows (FixedTape.midBox ibox332))
attribute [irreducible] tree332
private theorem sign_332 : 2*denominator*(computed denominator (FixedTape.midBox ibox332)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox332).gradient k).lo.natAbs ((computed denominator ibox332).gradient k).hi.natAbs : Int)*((ibox332 k).hi-(ibox332 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox332
    (computed denominator ibox332) (computed denominator (FixedTape.midBox ibox332))
    (by decide +kernel)
private theorem midpoint_even_332 : ∀ k, 2 ∣ (ibox332 k).lo+(ibox332 k).hi := by decide +kernel
private theorem accepted_332 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox332) tree332 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox332 midpoint_even_332
  simp only [tree332,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox332,candidate_valid h (FixedTape.midBox ibox332),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox332 212 (FixedTape.rowsAux denominator ibox332 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox332) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_332
private noncomputable def tree331 : TapeTree := .centered (candidateRows ibox331) (candidateRows (FixedTape.midBox ibox331))
attribute [irreducible] tree331
private theorem sign_331 : 2*denominator*(computed denominator (FixedTape.midBox ibox331)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox331).gradient k).lo.natAbs ((computed denominator ibox331).gradient k).hi.natAbs : Int)*((ibox331 k).hi-(ibox331 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox331
    (computed denominator ibox331) (computed denominator (FixedTape.midBox ibox331))
    (by decide +kernel)
private theorem midpoint_even_331 : ∀ k, 2 ∣ (ibox331 k).lo+(ibox331 k).hi := by decide +kernel
private theorem accepted_331 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox331) tree331 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox331 midpoint_even_331
  simp only [tree331,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox331,candidate_valid h (FixedTape.midBox ibox331),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox331 212 (FixedTape.rowsAux denominator ibox331 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox331) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_331
private noncomputable def tree330 : TapeTree := .split 0 (((8145174300091725704854793264029425003166433280000000000 : Int) : ℚ)/(denominator : ℚ)) tree331 tree332
attribute [irreducible] tree330
private theorem accepted_330 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox330) tree330 = true := by
  simp only [tree330,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox330 0 (8145174300091725704854793264029425003166433280000000000 : Int) false,decode_split denominator ibox330 0 (8145174300091725704854793264029425003166433280000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_331 h,accepted_332 h⟩
private noncomputable def tree329 : TapeTree := .centered (candidateRows ibox329) (candidateRows (FixedTape.midBox ibox329))
attribute [irreducible] tree329
private theorem sign_329 : 2*denominator*(computed denominator (FixedTape.midBox ibox329)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox329).gradient k).lo.natAbs ((computed denominator ibox329).gradient k).hi.natAbs : Int)*((ibox329 k).hi-(ibox329 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox329
    (computed denominator ibox329) (computed denominator (FixedTape.midBox ibox329))
    (by decide +kernel)
private theorem midpoint_even_329 : ∀ k, 2 ∣ (ibox329 k).lo+(ibox329 k).hi := by decide +kernel
private theorem accepted_329 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox329) tree329 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox329 midpoint_even_329
  simp only [tree329,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox329,candidate_valid h (FixedTape.midBox ibox329),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox329 212 (FixedTape.rowsAux denominator ibox329 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox329) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_329
private noncomputable def tree328 : TapeTree := .centered (candidateRows ibox328) (candidateRows (FixedTape.midBox ibox328))
attribute [irreducible] tree328
private theorem sign_328 : 2*denominator*(computed denominator (FixedTape.midBox ibox328)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox328).gradient k).lo.natAbs ((computed denominator ibox328).gradient k).hi.natAbs : Int)*((ibox328 k).hi-(ibox328 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox328
    (computed denominator ibox328) (computed denominator (FixedTape.midBox ibox328))
    (by decide +kernel)
private theorem midpoint_even_328 : ∀ k, 2 ∣ (ibox328 k).lo+(ibox328 k).hi := by decide +kernel
private theorem accepted_328 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox328) tree328 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox328 midpoint_even_328
  simp only [tree328,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox328,candidate_valid h (FixedTape.midBox ibox328),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox328 212 (FixedTape.rowsAux denominator ibox328 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox328) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_328
private noncomputable def tree327 : TapeTree := .split 0 (((8145174300091725704854793264029425003166433280000000000 : Int) : ℚ)/(denominator : ℚ)) tree328 tree329
attribute [irreducible] tree327
private theorem accepted_327 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox327) tree327 = true := by
  simp only [tree327,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox327 0 (8145174300091725704854793264029425003166433280000000000 : Int) false,decode_split denominator ibox327 0 (8145174300091725704854793264029425003166433280000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_328 h,accepted_329 h⟩
private noncomputable def tree326 : TapeTree := .split 3 (((4781391013124241642840694968107160744807628800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree327 tree330
attribute [irreducible] tree326
private theorem accepted_326 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox326) tree326 = true := by
  simp only [tree326,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox326 3 (4781391013124241642840694968107160744807628800000000000000 : Int) false,decode_split denominator ibox326 3 (4781391013124241642840694968107160744807628800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_327 h,accepted_330 h⟩
private noncomputable def tree325 : TapeTree := .split 0 (((8236693112452306892549790941153351126797516800000000000 : Int) : ℚ)/(denominator : ℚ)) tree326 tree333
attribute [irreducible] tree325
private theorem accepted_325 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox325) tree325 = true := by
  simp only [tree325,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox325 0 (8236693112452306892549790941153351126797516800000000000 : Int) false,decode_split denominator ibox325 0 (8236693112452306892549790941153351126797516800000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_326 h,accepted_333 h⟩
private noncomputable def tree324 : TapeTree := .split 3 (((5737669215749089971408833961728592893769154560000000000000 : Int) : ℚ)/(denominator : ℚ)) tree325 tree336
attribute [irreducible] tree324
private theorem accepted_324 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox324) tree324 = true := by
  simp only [tree324,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox324 3 (5737669215749089971408833961728592893769154560000000000000 : Int) false,decode_split denominator ibox324 3 (5737669215749089971408833961728592893769154560000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_325 h,accepted_336 h⟩
private noncomputable def tree323 : TapeTree := .split 0 (((8419730737173469267939786295401203374059683840000000000 : Int) : ℚ)/(denominator : ℚ)) tree324 tree343
attribute [irreducible] tree323
private theorem accepted_323 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox323) tree323 = true := by
  simp only [tree323,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox323 0 (8419730737173469267939786295401203374059683840000000000 : Int) false,decode_split denominator ibox323 0 (8419730737173469267939786295401203374059683840000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_324 h,accepted_343 h⟩
private noncomputable def tree322 : TapeTree := .centered (candidateRows ibox322) (candidateRows (FixedTape.midBox ibox322))
attribute [irreducible] tree322
private theorem sign_322 : 2*denominator*(computed denominator (FixedTape.midBox ibox322)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox322).gradient k).lo.natAbs ((computed denominator ibox322).gradient k).hi.natAbs : Int)*((ibox322 k).hi-(ibox322 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox322
    (computed denominator ibox322) (computed denominator (FixedTape.midBox ibox322))
    (by decide +kernel)
private theorem midpoint_even_322 : ∀ k, 2 ∣ (ibox322 k).lo+(ibox322 k).hi := by decide +kernel
private theorem accepted_322 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox322) tree322 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox322 midpoint_even_322
  simp only [tree322,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox322,candidate_valid h (FixedTape.midBox ibox322),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox322 212 (FixedTape.rowsAux denominator ibox322 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox322) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_322
private noncomputable def tree321 : TapeTree := .centered (candidateRows ibox321) (candidateRows (FixedTape.midBox ibox321))
attribute [irreducible] tree321
private theorem sign_321 : 2*denominator*(computed denominator (FixedTape.midBox ibox321)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox321).gradient k).lo.natAbs ((computed denominator ibox321).gradient k).hi.natAbs : Int)*((ibox321 k).hi-(ibox321 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox321
    (computed denominator ibox321) (computed denominator (FixedTape.midBox ibox321))
    (by decide +kernel)
private theorem midpoint_even_321 : ∀ k, 2 ∣ (ibox321 k).lo+(ibox321 k).hi := by decide +kernel
private theorem accepted_321 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox321) tree321 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox321 midpoint_even_321
  simp only [tree321,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox321,candidate_valid h (FixedTape.midBox ibox321),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox321 212 (FixedTape.rowsAux denominator ibox321 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox321) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_321
private noncomputable def tree320 : TapeTree := .split 3 (((2868834607874544985704416980864296446884577280000000000000 : Int) : ℚ)/(denominator : ℚ)) tree321 tree322
attribute [irreducible] tree320
private theorem accepted_320 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox320) tree320 = true := by
  simp only [tree320,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox320 3 (2868834607874544985704416980864296446884577280000000000000 : Int) false,decode_split denominator ibox320 3 (2868834607874544985704416980864296446884577280000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_321 h,accepted_322 h⟩
private noncomputable def tree319 : TapeTree := .centered (candidateRows ibox319) (candidateRows (FixedTape.midBox ibox319))
attribute [irreducible] tree319
private theorem sign_319 : 2*denominator*(computed denominator (FixedTape.midBox ibox319)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox319).gradient k).lo.natAbs ((computed denominator ibox319).gradient k).hi.natAbs : Int)*((ibox319 k).hi-(ibox319 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox319
    (computed denominator ibox319) (computed denominator (FixedTape.midBox ibox319))
    (by decide +kernel)
private theorem midpoint_even_319 : ∀ k, 2 ∣ (ibox319 k).lo+(ibox319 k).hi := by decide +kernel
private theorem accepted_319 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox319) tree319 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox319 midpoint_even_319
  simp only [tree319,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox319,candidate_valid h (FixedTape.midBox ibox319),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox319 212 (FixedTape.rowsAux denominator ibox319 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox319) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_319
private noncomputable def tree318 : TapeTree := .centered (candidateRows ibox318) (candidateRows (FixedTape.midBox ibox318))
attribute [irreducible] tree318
private theorem sign_318 : 2*denominator*(computed denominator (FixedTape.midBox ibox318)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox318).gradient k).lo.natAbs ((computed denominator ibox318).gradient k).hi.natAbs : Int)*((ibox318 k).hi-(ibox318 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox318
    (computed denominator ibox318) (computed denominator (FixedTape.midBox ibox318))
    (by decide +kernel)
private theorem midpoint_even_318 : ∀ k, 2 ∣ (ibox318 k).lo+(ibox318 k).hi := by decide +kernel
private theorem accepted_318 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox318) tree318 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox318 midpoint_even_318
  simp only [tree318,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox318,candidate_valid h (FixedTape.midBox ibox318),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox318 212 (FixedTape.rowsAux denominator ibox318 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox318) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_318
private noncomputable def tree317 : TapeTree := .split 3 (((2868834607874544985704416980864296446884577280000000000000 : Int) : ℚ)/(denominator : ℚ)) tree318 tree319
attribute [irreducible] tree317
private theorem accepted_317 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox317) tree317 = true := by
  simp only [tree317,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox317 3 (2868834607874544985704416980864296446884577280000000000000 : Int) false,decode_split denominator ibox317 3 (2868834607874544985704416980864296446884577280000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_318 h,accepted_319 h⟩
private noncomputable def tree316 : TapeTree := .split 0 (((8602768361894631643329781649649055621321850880000000000 : Int) : ℚ)/(denominator : ℚ)) tree317 tree320
attribute [irreducible] tree316
private theorem accepted_316 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox316) tree316 = true := by
  simp only [tree316,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox316 0 (8602768361894631643329781649649055621321850880000000000 : Int) false,decode_split denominator ibox316 0 (8602768361894631643329781649649055621321850880000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_317 h,accepted_320 h⟩
private noncomputable def tree315 : TapeTree := .centered (candidateRows ibox315) (candidateRows (FixedTape.midBox ibox315))
attribute [irreducible] tree315
private theorem sign_315 : 2*denominator*(computed denominator (FixedTape.midBox ibox315)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox315).gradient k).lo.natAbs ((computed denominator ibox315).gradient k).hi.natAbs : Int)*((ibox315 k).hi-(ibox315 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox315
    (computed denominator ibox315) (computed denominator (FixedTape.midBox ibox315))
    (by decide +kernel)
private theorem midpoint_even_315 : ∀ k, 2 ∣ (ibox315 k).lo+(ibox315 k).hi := by decide +kernel
private theorem accepted_315 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox315) tree315 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox315 midpoint_even_315
  simp only [tree315,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox315,candidate_valid h (FixedTape.midBox ibox315),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox315 212 (FixedTape.rowsAux denominator ibox315 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox315) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_315
private noncomputable def tree314 : TapeTree := .centered (candidateRows ibox314) (candidateRows (FixedTape.midBox ibox314))
attribute [irreducible] tree314
private theorem sign_314 : 2*denominator*(computed denominator (FixedTape.midBox ibox314)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox314).gradient k).lo.natAbs ((computed denominator ibox314).gradient k).hi.natAbs : Int)*((ibox314 k).hi-(ibox314 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox314
    (computed denominator ibox314) (computed denominator (FixedTape.midBox ibox314))
    (by decide +kernel)
private theorem midpoint_even_314 : ∀ k, 2 ∣ (ibox314 k).lo+(ibox314 k).hi := by decide +kernel
private theorem accepted_314 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox314) tree314 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox314 midpoint_even_314
  simp only [tree314,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox314,candidate_valid h (FixedTape.midBox ibox314),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox314 212 (FixedTape.rowsAux denominator ibox314 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox314) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_314
private noncomputable def tree313 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree314 tree315
attribute [irreducible] tree313
private theorem accepted_313 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox313) tree313 = true := by
  simp only [tree313,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox313 3 (956278202624848328568138993621432148961525760000000000000 : Int) false,decode_split denominator ibox313 3 (956278202624848328568138993621432148961525760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_314 h,accepted_315 h⟩
private noncomputable def tree312 : TapeTree := .centered (candidateRows ibox312) (candidateRows (FixedTape.midBox ibox312))
attribute [irreducible] tree312
private theorem sign_312 : 2*denominator*(computed denominator (FixedTape.midBox ibox312)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox312).gradient k).lo.natAbs ((computed denominator ibox312).gradient k).hi.natAbs : Int)*((ibox312 k).hi-(ibox312 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox312
    (computed denominator ibox312) (computed denominator (FixedTape.midBox ibox312))
    (by decide +kernel)
private theorem midpoint_even_312 : ∀ k, 2 ∣ (ibox312 k).lo+(ibox312 k).hi := by decide +kernel
private theorem accepted_312 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox312) tree312 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox312 midpoint_even_312
  simp only [tree312,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox312,candidate_valid h (FixedTape.midBox ibox312),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox312 212 (FixedTape.rowsAux denominator ibox312 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox312) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_312
private noncomputable def tree311 : TapeTree := .centered (candidateRows ibox311) (candidateRows (FixedTape.midBox ibox311))
attribute [irreducible] tree311
private theorem sign_311 : 2*denominator*(computed denominator (FixedTape.midBox ibox311)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox311).gradient k).lo.natAbs ((computed denominator ibox311).gradient k).hi.natAbs : Int)*((ibox311 k).hi-(ibox311 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox311
    (computed denominator ibox311) (computed denominator (FixedTape.midBox ibox311))
    (by decide +kernel)
private theorem midpoint_even_311 : ∀ k, 2 ∣ (ibox311 k).lo+(ibox311 k).hi := by decide +kernel
private theorem accepted_311 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox311) tree311 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox311 midpoint_even_311
  simp only [tree311,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox311,candidate_valid h (FixedTape.midBox ibox311),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox311 212 (FixedTape.rowsAux denominator ibox311 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox311) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_311
private noncomputable def tree310 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree311 tree312
attribute [irreducible] tree310
private theorem accepted_310 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox310) tree310 = true := by
  simp only [tree310,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox310 3 (956278202624848328568138993621432148961525760000000000000 : Int) false,decode_split denominator ibox310 3 (956278202624848328568138993621432148961525760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_311 h,accepted_312 h⟩
private noncomputable def tree309 : TapeTree := .split 0 (((8602768361894631643329781649649055621321850880000000000 : Int) : ℚ)/(denominator : ℚ)) tree310 tree313
attribute [irreducible] tree309
private theorem accepted_309 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox309) tree309 = true := by
  simp only [tree309,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox309 0 (8602768361894631643329781649649055621321850880000000000 : Int) false,decode_split denominator ibox309 0 (8602768361894631643329781649649055621321850880000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_310 h,accepted_313 h⟩
private noncomputable def tree308 : TapeTree := .split 3 (((1912556405249696657136277987242864297923051520000000000000 : Int) : ℚ)/(denominator : ℚ)) tree309 tree316
attribute [irreducible] tree308
private theorem accepted_308 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox308) tree308 = true := by
  simp only [tree308,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox308 3 (1912556405249696657136277987242864297923051520000000000000 : Int) false,decode_split denominator ibox308 3 (1912556405249696657136277987242864297923051520000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_309 h,accepted_316 h⟩
private noncomputable def tree307 : TapeTree := .centered (candidateRows ibox307) (candidateRows (FixedTape.midBox ibox307))
attribute [irreducible] tree307
private theorem sign_307 : 2*denominator*(computed denominator (FixedTape.midBox ibox307)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox307).gradient k).lo.natAbs ((computed denominator ibox307).gradient k).hi.natAbs : Int)*((ibox307 k).hi-(ibox307 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox307
    (computed denominator ibox307) (computed denominator (FixedTape.midBox ibox307))
    (by decide +kernel)
private theorem midpoint_even_307 : ∀ k, 2 ∣ (ibox307 k).lo+(ibox307 k).hi := by decide +kernel
private theorem accepted_307 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox307) tree307 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox307 midpoint_even_307
  simp only [tree307,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox307,candidate_valid h (FixedTape.midBox ibox307),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox307 212 (FixedTape.rowsAux denominator ibox307 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox307) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_307
private noncomputable def tree306 : TapeTree := .centered (candidateRows ibox306) (candidateRows (FixedTape.midBox ibox306))
attribute [irreducible] tree306
private theorem sign_306 : 2*denominator*(computed denominator (FixedTape.midBox ibox306)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox306).gradient k).lo.natAbs ((computed denominator ibox306).gradient k).hi.natAbs : Int)*((ibox306 k).hi-(ibox306 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox306
    (computed denominator ibox306) (computed denominator (FixedTape.midBox ibox306))
    (by decide +kernel)
private theorem midpoint_even_306 : ∀ k, 2 ∣ (ibox306 k).lo+(ibox306 k).hi := by decide +kernel
private theorem accepted_306 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox306) tree306 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox306 midpoint_even_306
  simp only [tree306,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox306,candidate_valid h (FixedTape.midBox ibox306),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox306 212 (FixedTape.rowsAux denominator ibox306 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox306) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_306
private noncomputable def tree305 : TapeTree := .split 3 (((2868834607874544985704416980864296446884577280000000000000 : Int) : ℚ)/(denominator : ℚ)) tree306 tree307
attribute [irreducible] tree305
private theorem accepted_305 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox305) tree305 = true := by
  simp only [tree305,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox305 3 (2868834607874544985704416980864296446884577280000000000000 : Int) false,decode_split denominator ibox305 3 (2868834607874544985704416980864296446884577280000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_306 h,accepted_307 h⟩
private noncomputable def tree304 : TapeTree := .centered (candidateRows ibox304) (candidateRows (FixedTape.midBox ibox304))
attribute [irreducible] tree304
private theorem sign_304 : 2*denominator*(computed denominator (FixedTape.midBox ibox304)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox304).gradient k).lo.natAbs ((computed denominator ibox304).gradient k).hi.natAbs : Int)*((ibox304 k).hi-(ibox304 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox304
    (computed denominator ibox304) (computed denominator (FixedTape.midBox ibox304))
    (by decide +kernel)
private theorem midpoint_even_304 : ∀ k, 2 ∣ (ibox304 k).lo+(ibox304 k).hi := by decide +kernel
private theorem accepted_304 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox304) tree304 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox304 midpoint_even_304
  simp only [tree304,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox304,candidate_valid h (FixedTape.midBox ibox304),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox304 212 (FixedTape.rowsAux denominator ibox304 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox304) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_304
private noncomputable def tree303 : TapeTree := .centered (candidateRows ibox303) (candidateRows (FixedTape.midBox ibox303))
attribute [irreducible] tree303
private theorem sign_303 : 2*denominator*(computed denominator (FixedTape.midBox ibox303)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox303).gradient k).lo.natAbs ((computed denominator ibox303).gradient k).hi.natAbs : Int)*((ibox303 k).hi-(ibox303 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox303
    (computed denominator ibox303) (computed denominator (FixedTape.midBox ibox303))
    (by decide +kernel)
private theorem midpoint_even_303 : ∀ k, 2 ∣ (ibox303 k).lo+(ibox303 k).hi := by decide +kernel
private theorem accepted_303 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox303) tree303 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox303 midpoint_even_303
  simp only [tree303,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox303,candidate_valid h (FixedTape.midBox ibox303),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox303 212 (FixedTape.rowsAux denominator ibox303 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox303) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_303
private noncomputable def tree302 : TapeTree := .split 0 (((8145174300091725704854793264029425003166433280000000000 : Int) : ℚ)/(denominator : ℚ)) tree303 tree304
attribute [irreducible] tree302
private theorem accepted_302 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox302) tree302 = true := by
  simp only [tree302,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox302 0 (8145174300091725704854793264029425003166433280000000000 : Int) false,decode_split denominator ibox302 0 (8145174300091725704854793264029425003166433280000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_303 h,accepted_304 h⟩
private noncomputable def tree301 : TapeTree := .centered (candidateRows ibox301) (candidateRows (FixedTape.midBox ibox301))
attribute [irreducible] tree301
private theorem sign_301 : 2*denominator*(computed denominator (FixedTape.midBox ibox301)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox301).gradient k).lo.natAbs ((computed denominator ibox301).gradient k).hi.natAbs : Int)*((ibox301 k).hi-(ibox301 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox301
    (computed denominator ibox301) (computed denominator (FixedTape.midBox ibox301))
    (by decide +kernel)
private theorem midpoint_even_301 : ∀ k, 2 ∣ (ibox301 k).lo+(ibox301 k).hi := by decide +kernel
private theorem accepted_301 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox301) tree301 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox301 midpoint_even_301
  simp only [tree301,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox301,candidate_valid h (FixedTape.midBox ibox301),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox301 212 (FixedTape.rowsAux denominator ibox301 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox301) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_301
private noncomputable def tree300 : TapeTree := .centered (candidateRows ibox300) (candidateRows (FixedTape.midBox ibox300))
attribute [irreducible] tree300
private theorem sign_300 : 2*denominator*(computed denominator (FixedTape.midBox ibox300)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox300).gradient k).lo.natAbs ((computed denominator ibox300).gradient k).hi.natAbs : Int)*((ibox300 k).hi-(ibox300 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox300
    (computed denominator ibox300) (computed denominator (FixedTape.midBox ibox300))
    (by decide +kernel)
private theorem midpoint_even_300 : ∀ k, 2 ∣ (ibox300 k).lo+(ibox300 k).hi := by decide +kernel
private theorem accepted_300 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox300) tree300 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox300 midpoint_even_300
  simp only [tree300,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox300,candidate_valid h (FixedTape.midBox ibox300),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox300 212 (FixedTape.rowsAux denominator ibox300 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox300) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_300
private noncomputable def tree299 : TapeTree := .split 0 (((8145174300091725704854793264029425003166433280000000000 : Int) : ℚ)/(denominator : ℚ)) tree300 tree301
attribute [irreducible] tree299
private theorem accepted_299 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox299) tree299 = true := by
  simp only [tree299,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox299 0 (8145174300091725704854793264029425003166433280000000000 : Int) false,decode_split denominator ibox299 0 (8145174300091725704854793264029425003166433280000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_300 h,accepted_301 h⟩
private noncomputable def tree298 : TapeTree := .split 3 (((2868834607874544985704416980864296446884577280000000000000 : Int) : ℚ)/(denominator : ℚ)) tree299 tree302
attribute [irreducible] tree298
private theorem accepted_298 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox298) tree298 = true := by
  simp only [tree298,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox298 3 (2868834607874544985704416980864296446884577280000000000000 : Int) false,decode_split denominator ibox298 3 (2868834607874544985704416980864296446884577280000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_299 h,accepted_302 h⟩
private noncomputable def tree297 : TapeTree := .split 0 (((8236693112452306892549790941153351126797516800000000000 : Int) : ℚ)/(denominator : ℚ)) tree298 tree305
attribute [irreducible] tree297
private theorem accepted_297 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox297) tree297 = true := by
  simp only [tree297,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox297 0 (8236693112452306892549790941153351126797516800000000000 : Int) false,decode_split denominator ibox297 0 (8236693112452306892549790941153351126797516800000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_298 h,accepted_305 h⟩
private noncomputable def tree296 : TapeTree := .centered (candidateRows ibox296) (candidateRows (FixedTape.midBox ibox296))
attribute [irreducible] tree296
private theorem sign_296 : 2*denominator*(computed denominator (FixedTape.midBox ibox296)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox296).gradient k).lo.natAbs ((computed denominator ibox296).gradient k).hi.natAbs : Int)*((ibox296 k).hi-(ibox296 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox296
    (computed denominator ibox296) (computed denominator (FixedTape.midBox ibox296))
    (by decide +kernel)
private theorem midpoint_even_296 : ∀ k, 2 ∣ (ibox296 k).lo+(ibox296 k).hi := by decide +kernel
private theorem accepted_296 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox296) tree296 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox296 midpoint_even_296
  simp only [tree296,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox296,candidate_valid h (FixedTape.midBox ibox296),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox296 212 (FixedTape.rowsAux denominator ibox296 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox296) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_296
private noncomputable def tree295 : TapeTree := .centered (candidateRows ibox295) (candidateRows (FixedTape.midBox ibox295))
attribute [irreducible] tree295
private theorem sign_295 : 2*denominator*(computed denominator (FixedTape.midBox ibox295)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox295).gradient k).lo.natAbs ((computed denominator ibox295).gradient k).hi.natAbs : Int)*((ibox295 k).hi-(ibox295 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox295
    (computed denominator ibox295) (computed denominator (FixedTape.midBox ibox295))
    (by decide +kernel)
private theorem midpoint_even_295 : ∀ k, 2 ∣ (ibox295 k).lo+(ibox295 k).hi := by decide +kernel
private theorem accepted_295 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox295) tree295 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox295 midpoint_even_295
  simp only [tree295,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox295,candidate_valid h (FixedTape.midBox ibox295),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox295 212 (FixedTape.rowsAux denominator ibox295 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox295) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_295
private noncomputable def tree294 : TapeTree := .split 0 (((8328211924812888080244788618277277250428600320000000000 : Int) : ℚ)/(denominator : ℚ)) tree295 tree296
attribute [irreducible] tree294
private theorem accepted_294 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox294) tree294 = true := by
  simp only [tree294,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox294 0 (8328211924812888080244788618277277250428600320000000000 : Int) false,decode_split denominator ibox294 0 (8328211924812888080244788618277277250428600320000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_295 h,accepted_296 h⟩
private noncomputable def tree293 : TapeTree := .centered (candidateRows ibox293) (candidateRows (FixedTape.midBox ibox293))
attribute [irreducible] tree293
private theorem sign_293 : 2*denominator*(computed denominator (FixedTape.midBox ibox293)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox293).gradient k).lo.natAbs ((computed denominator ibox293).gradient k).hi.natAbs : Int)*((ibox293 k).hi-(ibox293 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox293
    (computed denominator ibox293) (computed denominator (FixedTape.midBox ibox293))
    (by decide +kernel)
private theorem midpoint_even_293 : ∀ k, 2 ∣ (ibox293 k).lo+(ibox293 k).hi := by decide +kernel
private theorem accepted_293 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox293) tree293 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox293 midpoint_even_293
  simp only [tree293,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox293,candidate_valid h (FixedTape.midBox ibox293),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox293 212 (FixedTape.rowsAux denominator ibox293 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox293) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_293
private noncomputable def tree292 : TapeTree := .centered (candidateRows ibox292) (candidateRows (FixedTape.midBox ibox292))
attribute [irreducible] tree292
private theorem sign_292 : 2*denominator*(computed denominator (FixedTape.midBox ibox292)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox292).gradient k).lo.natAbs ((computed denominator ibox292).gradient k).hi.natAbs : Int)*((ibox292 k).hi-(ibox292 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox292
    (computed denominator ibox292) (computed denominator (FixedTape.midBox ibox292))
    (by decide +kernel)
private theorem midpoint_even_292 : ∀ k, 2 ∣ (ibox292 k).lo+(ibox292 k).hi := by decide +kernel
private theorem accepted_292 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox292) tree292 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox292 midpoint_even_292
  simp only [tree292,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox292,candidate_valid h (FixedTape.midBox ibox292),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox292 212 (FixedTape.rowsAux denominator ibox292 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox292) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_292
private noncomputable def tree291 : TapeTree := .split 0 (((8328211924812888080244788618277277250428600320000000000 : Int) : ℚ)/(denominator : ℚ)) tree292 tree293
attribute [irreducible] tree291
private theorem accepted_291 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox291) tree291 = true := by
  simp only [tree291,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox291 0 (8328211924812888080244788618277277250428600320000000000 : Int) false,decode_split denominator ibox291 0 (8328211924812888080244788618277277250428600320000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_292 h,accepted_293 h⟩
private noncomputable def tree290 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree291 tree294
attribute [irreducible] tree290
private theorem accepted_290 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox290) tree290 = true := by
  simp only [tree290,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox290 3 (956278202624848328568138993621432148961525760000000000000 : Int) false,decode_split denominator ibox290 3 (956278202624848328568138993621432148961525760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_291 h,accepted_294 h⟩
private noncomputable def tree289 : TapeTree := .centered (candidateRows ibox289) (candidateRows (FixedTape.midBox ibox289))
attribute [irreducible] tree289
private theorem sign_289 : 2*denominator*(computed denominator (FixedTape.midBox ibox289)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox289).gradient k).lo.natAbs ((computed denominator ibox289).gradient k).hi.natAbs : Int)*((ibox289 k).hi-(ibox289 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox289
    (computed denominator ibox289) (computed denominator (FixedTape.midBox ibox289))
    (by decide +kernel)
private theorem midpoint_even_289 : ∀ k, 2 ∣ (ibox289 k).lo+(ibox289 k).hi := by decide +kernel
private theorem accepted_289 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox289) tree289 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox289 midpoint_even_289
  simp only [tree289,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox289,candidate_valid h (FixedTape.midBox ibox289),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox289 212 (FixedTape.rowsAux denominator ibox289 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox289) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_289
private noncomputable def tree288 : TapeTree := .centered (candidateRows ibox288) (candidateRows (FixedTape.midBox ibox288))
attribute [irreducible] tree288
private theorem sign_288 : 2*denominator*(computed denominator (FixedTape.midBox ibox288)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox288).gradient k).lo.natAbs ((computed denominator ibox288).gradient k).hi.natAbs : Int)*((ibox288 k).hi-(ibox288 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox288
    (computed denominator ibox288) (computed denominator (FixedTape.midBox ibox288))
    (by decide +kernel)
private theorem midpoint_even_288 : ∀ k, 2 ∣ (ibox288 k).lo+(ibox288 k).hi := by decide +kernel
private theorem accepted_288 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox288) tree288 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox288 midpoint_even_288
  simp only [tree288,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox288,candidate_valid h (FixedTape.midBox ibox288),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox288 212 (FixedTape.rowsAux denominator ibox288 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox288) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_288
private noncomputable def tree287 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree288 tree289
attribute [irreducible] tree287
private theorem accepted_287 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox287) tree287 = true := by
  simp only [tree287,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox287 3 (956278202624848328568138993621432148961525760000000000000 : Int) false,decode_split denominator ibox287 3 (956278202624848328568138993621432148961525760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_288 h,accepted_289 h⟩
private noncomputable def tree286 : TapeTree := .centered (candidateRows ibox286) (candidateRows (FixedTape.midBox ibox286))
attribute [irreducible] tree286
private theorem sign_286 : 2*denominator*(computed denominator (FixedTape.midBox ibox286)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox286).gradient k).lo.natAbs ((computed denominator ibox286).gradient k).hi.natAbs : Int)*((ibox286 k).hi-(ibox286 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox286
    (computed denominator ibox286) (computed denominator (FixedTape.midBox ibox286))
    (by decide +kernel)
private theorem midpoint_even_286 : ∀ k, 2 ∣ (ibox286 k).lo+(ibox286 k).hi := by decide +kernel
private theorem accepted_286 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox286) tree286 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox286 midpoint_even_286
  simp only [tree286,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox286,candidate_valid h (FixedTape.midBox ibox286),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox286 212 (FixedTape.rowsAux denominator ibox286 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox286) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_286
private noncomputable def tree285 : TapeTree := .centered (candidateRows ibox285) (candidateRows (FixedTape.midBox ibox285))
attribute [irreducible] tree285
private theorem sign_285 : 2*denominator*(computed denominator (FixedTape.midBox ibox285)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox285).gradient k).lo.natAbs ((computed denominator ibox285).gradient k).hi.natAbs : Int)*((ibox285 k).hi-(ibox285 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox285
    (computed denominator ibox285) (computed denominator (FixedTape.midBox ibox285))
    (by decide +kernel)
private theorem midpoint_even_285 : ∀ k, 2 ∣ (ibox285 k).lo+(ibox285 k).hi := by decide +kernel
private theorem accepted_285 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox285) tree285 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox285 midpoint_even_285
  simp only [tree285,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox285,candidate_valid h (FixedTape.midBox ibox285),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox285 212 (FixedTape.rowsAux denominator ibox285 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox285) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_285
private noncomputable def tree284 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree285 tree286
attribute [irreducible] tree284
private theorem accepted_284 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox284) tree284 = true := by
  simp only [tree284,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox284 3 (956278202624848328568138993621432148961525760000000000000 : Int) false,decode_split denominator ibox284 3 (956278202624848328568138993621432148961525760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_285 h,accepted_286 h⟩
private noncomputable def tree283 : TapeTree := .split 0 (((8145174300091725704854793264029425003166433280000000000 : Int) : ℚ)/(denominator : ℚ)) tree284 tree287
attribute [irreducible] tree283
private theorem accepted_283 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox283) tree283 = true := by
  simp only [tree283,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox283 0 (8145174300091725704854793264029425003166433280000000000 : Int) false,decode_split denominator ibox283 0 (8145174300091725704854793264029425003166433280000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_284 h,accepted_287 h⟩
private noncomputable def tree282 : TapeTree := .split 0 (((8236693112452306892549790941153351126797516800000000000 : Int) : ℚ)/(denominator : ℚ)) tree283 tree290
attribute [irreducible] tree282
private theorem accepted_282 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox282) tree282 = true := by
  simp only [tree282,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox282 0 (8236693112452306892549790941153351126797516800000000000 : Int) false,decode_split denominator ibox282 0 (8236693112452306892549790941153351126797516800000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_283 h,accepted_290 h⟩
private noncomputable def tree281 : TapeTree := .split 3 (((1912556405249696657136277987242864297923051520000000000000 : Int) : ℚ)/(denominator : ℚ)) tree282 tree297
attribute [irreducible] tree281
private theorem accepted_281 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox281) tree281 = true := by
  simp only [tree281,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox281 3 (1912556405249696657136277987242864297923051520000000000000 : Int) false,decode_split denominator ibox281 3 (1912556405249696657136277987242864297923051520000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_282 h,accepted_297 h⟩
private noncomputable def tree280 : TapeTree := .split 0 (((8419730737173469267939786295401203374059683840000000000 : Int) : ℚ)/(denominator : ℚ)) tree281 tree308
attribute [irreducible] tree280
private theorem accepted_280 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox280) tree280 = true := by
  simp only [tree280,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox280 0 (8419730737173469267939786295401203374059683840000000000 : Int) false,decode_split denominator ibox280 0 (8419730737173469267939786295401203374059683840000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_281 h,accepted_308 h⟩
private noncomputable def tree279 : TapeTree := .split 3 (((3825112810499393314272555974485728595846103040000000000000 : Int) : ℚ)/(denominator : ℚ)) tree280 tree323
attribute [irreducible] tree279
private theorem accepted_279 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox279) tree279 = true := by
  simp only [tree279,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox279 3 (3825112810499393314272555974485728595846103040000000000000 : Int) false,decode_split denominator ibox279 3 (3825112810499393314272555974485728595846103040000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_280 h,accepted_323 h⟩
private noncomputable def tree278 : TapeTree := .split 3 (((7650225620998786628545111948971457191692206080000000000000 : Int) : ℚ)/(denominator : ℚ)) tree279 tree358
attribute [irreducible] tree278
private theorem accepted_278 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox278) tree278 = true := by
  simp only [tree278,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox278 3 (7650225620998786628545111948971457191692206080000000000000 : Int) false,decode_split denominator ibox278 3 (7650225620998786628545111948971457191692206080000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_279 h,accepted_358 h⟩
private noncomputable def tree277 : TapeTree := .face 1 false (candidateRows ibox277) tree278
attribute [irreducible] tree277
private theorem sign_277 : ((computed denominator ibox277).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_277 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox277) tree277 = true := by
  simp only [tree277,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox277,?_,accepted_278 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox277)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox277).gradient 1).hi) denominator_positive).1 sign_277
private noncomputable def tree276 : TapeTree := .centered (candidateRows ibox276) (candidateRows (FixedTape.midBox ibox276))
attribute [irreducible] tree276
private theorem sign_276 : 2*denominator*(computed denominator (FixedTape.midBox ibox276)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox276).gradient k).lo.natAbs ((computed denominator ibox276).gradient k).hi.natAbs : Int)*((ibox276 k).hi-(ibox276 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox276
    (computed denominator ibox276) (computed denominator (FixedTape.midBox ibox276))
    (by decide +kernel)
private theorem midpoint_even_276 : ∀ k, 2 ∣ (ibox276 k).lo+(ibox276 k).hi := by decide +kernel
private theorem accepted_276 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox276) tree276 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox276 midpoint_even_276
  simp only [tree276,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox276,candidate_valid h (FixedTape.midBox ibox276),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox276 212 (FixedTape.rowsAux denominator ibox276 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox276) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_276
private noncomputable def tree275 : TapeTree := .centered (candidateRows ibox275) (candidateRows (FixedTape.midBox ibox275))
attribute [irreducible] tree275
private theorem sign_275 : 2*denominator*(computed denominator (FixedTape.midBox ibox275)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox275).gradient k).lo.natAbs ((computed denominator ibox275).gradient k).hi.natAbs : Int)*((ibox275 k).hi-(ibox275 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox275
    (computed denominator ibox275) (computed denominator (FixedTape.midBox ibox275))
    (by decide +kernel)
private theorem midpoint_even_275 : ∀ k, 2 ∣ (ibox275 k).lo+(ibox275 k).hi := by decide +kernel
private theorem accepted_275 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox275) tree275 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox275 midpoint_even_275
  simp only [tree275,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox275,candidate_valid h (FixedTape.midBox ibox275),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox275 212 (FixedTape.rowsAux denominator ibox275 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox275) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_275
private noncomputable def tree274 : TapeTree := .split 0 (((7870617863009982141769800232657646632273182720000000000 : Int) : ℚ)/(denominator : ℚ)) tree275 tree276
attribute [irreducible] tree274
private theorem accepted_274 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox274) tree274 = true := by
  simp only [tree274,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox274 0 (7870617863009982141769800232657646632273182720000000000 : Int) false,decode_split denominator ibox274 0 (7870617863009982141769800232657646632273182720000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_275 h,accepted_276 h⟩
private noncomputable def tree273 : TapeTree := .centered (candidateRows ibox273) (candidateRows (FixedTape.midBox ibox273))
attribute [irreducible] tree273
private theorem sign_273 : 2*denominator*(computed denominator (FixedTape.midBox ibox273)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox273).gradient k).lo.natAbs ((computed denominator ibox273).gradient k).hi.natAbs : Int)*((ibox273 k).hi-(ibox273 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox273
    (computed denominator ibox273) (computed denominator (FixedTape.midBox ibox273))
    (by decide +kernel)
private theorem midpoint_even_273 : ∀ k, 2 ∣ (ibox273 k).lo+(ibox273 k).hi := by decide +kernel
private theorem accepted_273 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox273) tree273 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox273 midpoint_even_273
  simp only [tree273,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox273,candidate_valid h (FixedTape.midBox ibox273),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox273 212 (FixedTape.rowsAux denominator ibox273 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox273) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_273
private noncomputable def tree272 : TapeTree := .centered (candidateRows ibox272) (candidateRows (FixedTape.midBox ibox272))
attribute [irreducible] tree272
private theorem sign_272 : 2*denominator*(computed denominator (FixedTape.midBox ibox272)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox272).gradient k).lo.natAbs ((computed denominator ibox272).gradient k).hi.natAbs : Int)*((ibox272 k).hi-(ibox272 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox272
    (computed denominator ibox272) (computed denominator (FixedTape.midBox ibox272))
    (by decide +kernel)
private theorem midpoint_even_272 : ∀ k, 2 ∣ (ibox272 k).lo+(ibox272 k).hi := by decide +kernel
private theorem accepted_272 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox272) tree272 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox272 midpoint_even_272
  simp only [tree272,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox272,candidate_valid h (FixedTape.midBox ibox272),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox272 212 (FixedTape.rowsAux denominator ibox272 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox272) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_272
private noncomputable def tree271 : TapeTree := .centered (candidateRows ibox271) (candidateRows (FixedTape.midBox ibox271))
attribute [irreducible] tree271
private theorem sign_271 : 2*denominator*(computed denominator (FixedTape.midBox ibox271)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox271).gradient k).lo.natAbs ((computed denominator ibox271).gradient k).hi.natAbs : Int)*((ibox271 k).hi-(ibox271 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox271
    (computed denominator ibox271) (computed denominator (FixedTape.midBox ibox271))
    (by decide +kernel)
private theorem midpoint_even_271 : ∀ k, 2 ∣ (ibox271 k).lo+(ibox271 k).hi := by decide +kernel
private theorem accepted_271 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox271) tree271 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox271 midpoint_even_271
  simp only [tree271,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox271,candidate_valid h (FixedTape.midBox ibox271),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox271 212 (FixedTape.rowsAux denominator ibox271 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox271) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_271
private noncomputable def tree270 : TapeTree := .split 0 (((7779099050649400954074802555533720508642099200000000000 : Int) : ℚ)/(denominator : ℚ)) tree271 tree272
attribute [irreducible] tree270
private theorem accepted_270 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox270) tree270 = true := by
  simp only [tree270,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox270 0 (7779099050649400954074802555533720508642099200000000000 : Int) false,decode_split denominator ibox270 0 (7779099050649400954074802555533720508642099200000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_271 h,accepted_272 h⟩
private noncomputable def tree269 : TapeTree := .split 0 (((7870617863009982141769800232657646632273182720000000000 : Int) : ℚ)/(denominator : ℚ)) tree270 tree273
attribute [irreducible] tree269
private theorem accepted_269 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox269) tree269 = true := by
  simp only [tree269,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox269 0 (7870617863009982141769800232657646632273182720000000000 : Int) false,decode_split denominator ibox269 0 (7870617863009982141769800232657646632273182720000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_270 h,accepted_273 h⟩
private noncomputable def tree268 : TapeTree := .split 3 (((14344173039372724928522084904321482234422886400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree269 tree274
attribute [irreducible] tree268
private theorem accepted_268 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox268) tree268 = true := by
  simp only [tree268,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox268 3 (14344173039372724928522084904321482234422886400000000000000 : Int) false,decode_split denominator ibox268 3 (14344173039372724928522084904321482234422886400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_269 h,accepted_274 h⟩
private noncomputable def tree267 : TapeTree := .centered (candidateRows ibox267) (candidateRows (FixedTape.midBox ibox267))
attribute [irreducible] tree267
private theorem sign_267 : 2*denominator*(computed denominator (FixedTape.midBox ibox267)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox267).gradient k).lo.natAbs ((computed denominator ibox267).gradient k).hi.natAbs : Int)*((ibox267 k).hi-(ibox267 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox267
    (computed denominator ibox267) (computed denominator (FixedTape.midBox ibox267))
    (by decide +kernel)
private theorem midpoint_even_267 : ∀ k, 2 ∣ (ibox267 k).lo+(ibox267 k).hi := by decide +kernel
private theorem accepted_267 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox267) tree267 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox267 midpoint_even_267
  simp only [tree267,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox267,candidate_valid h (FixedTape.midBox ibox267),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox267 212 (FixedTape.rowsAux denominator ibox267 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox267) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_267
private noncomputable def tree266 : TapeTree := .centered (candidateRows ibox266) (candidateRows (FixedTape.midBox ibox266))
attribute [irreducible] tree266
private theorem sign_266 : 2*denominator*(computed denominator (FixedTape.midBox ibox266)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox266).gradient k).lo.natAbs ((computed denominator ibox266).gradient k).hi.natAbs : Int)*((ibox266 k).hi-(ibox266 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox266
    (computed denominator ibox266) (computed denominator (FixedTape.midBox ibox266))
    (by decide +kernel)
private theorem midpoint_even_266 : ∀ k, 2 ∣ (ibox266 k).lo+(ibox266 k).hi := by decide +kernel
private theorem accepted_266 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox266) tree266 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox266 midpoint_even_266
  simp only [tree266,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox266,candidate_valid h (FixedTape.midBox ibox266),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox266 212 (FixedTape.rowsAux denominator ibox266 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox266) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_266
private noncomputable def tree265 : TapeTree := .split 3 (((14822312140685149092806154401132198308903649280000000000000 : Int) : ℚ)/(denominator : ℚ)) tree266 tree267
attribute [irreducible] tree265
private theorem accepted_265 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox265) tree265 = true := by
  simp only [tree265,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox265 3 (14822312140685149092806154401132198308903649280000000000000 : Int) false,decode_split denominator ibox265 3 (14822312140685149092806154401132198308903649280000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_266 h,accepted_267 h⟩
private noncomputable def tree264 : TapeTree := .centered (candidateRows ibox264) (candidateRows (FixedTape.midBox ibox264))
attribute [irreducible] tree264
private theorem sign_264 : 2*denominator*(computed denominator (FixedTape.midBox ibox264)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox264).gradient k).lo.natAbs ((computed denominator ibox264).gradient k).hi.natAbs : Int)*((ibox264 k).hi-(ibox264 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox264
    (computed denominator ibox264) (computed denominator (FixedTape.midBox ibox264))
    (by decide +kernel)
private theorem midpoint_even_264 : ∀ k, 2 ∣ (ibox264 k).lo+(ibox264 k).hi := by decide +kernel
private theorem accepted_264 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox264) tree264 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox264 midpoint_even_264
  simp only [tree264,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox264,candidate_valid h (FixedTape.midBox ibox264),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox264 212 (FixedTape.rowsAux denominator ibox264 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox264) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_264
private noncomputable def tree263 : TapeTree := .centered (candidateRows ibox263) (candidateRows (FixedTape.midBox ibox263))
attribute [irreducible] tree263
private theorem sign_263 : 2*denominator*(computed denominator (FixedTape.midBox ibox263)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox263).gradient k).lo.natAbs ((computed denominator ibox263).gradient k).hi.natAbs : Int)*((ibox263 k).hi-(ibox263 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox263
    (computed denominator ibox263) (computed denominator (FixedTape.midBox ibox263))
    (by decide +kernel)
private theorem midpoint_even_263 : ∀ k, 2 ∣ (ibox263 k).lo+(ibox263 k).hi := by decide +kernel
private theorem accepted_263 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox263) tree263 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox263 midpoint_even_263
  simp only [tree263,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox263,candidate_valid h (FixedTape.midBox ibox263),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox263 212 (FixedTape.rowsAux denominator ibox263 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox263) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_263
private noncomputable def tree262 : TapeTree := .split 3 (((14822312140685149092806154401132198308903649280000000000000 : Int) : ℚ)/(denominator : ℚ)) tree263 tree264
attribute [irreducible] tree262
private theorem accepted_262 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox262) tree262 = true := by
  simp only [tree262,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox262 3 (14822312140685149092806154401132198308903649280000000000000 : Int) false,decode_split denominator ibox262 3 (14822312140685149092806154401132198308903649280000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_263 h,accepted_264 h⟩
private noncomputable def tree261 : TapeTree := .split 0 (((7504542613567657390989809524161942137748848640000000000 : Int) : ℚ)/(denominator : ℚ)) tree262 tree265
attribute [irreducible] tree261
private theorem accepted_261 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox261) tree261 = true := by
  simp only [tree261,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox261 0 (7504542613567657390989809524161942137748848640000000000 : Int) false,decode_split denominator ibox261 0 (7504542613567657390989809524161942137748848640000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_262 h,accepted_265 h⟩
private noncomputable def tree260 : TapeTree := .centered (candidateRows ibox260) (candidateRows (FixedTape.midBox ibox260))
attribute [irreducible] tree260
private theorem sign_260 : 2*denominator*(computed denominator (FixedTape.midBox ibox260)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox260).gradient k).lo.natAbs ((computed denominator ibox260).gradient k).hi.natAbs : Int)*((ibox260 k).hi-(ibox260 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox260
    (computed denominator ibox260) (computed denominator (FixedTape.midBox ibox260))
    (by decide +kernel)
private theorem midpoint_even_260 : ∀ k, 2 ∣ (ibox260 k).lo+(ibox260 k).hi := by decide +kernel
private theorem accepted_260 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox260) tree260 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox260 midpoint_even_260
  simp only [tree260,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox260,candidate_valid h (FixedTape.midBox ibox260),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox260 212 (FixedTape.rowsAux denominator ibox260 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox260) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_260
private noncomputable def tree259 : TapeTree := .centered (candidateRows ibox259) (candidateRows (FixedTape.midBox ibox259))
attribute [irreducible] tree259
private theorem sign_259 : 2*denominator*(computed denominator (FixedTape.midBox ibox259)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox259).gradient k).lo.natAbs ((computed denominator ibox259).gradient k).hi.natAbs : Int)*((ibox259 k).hi-(ibox259 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox259
    (computed denominator ibox259) (computed denominator (FixedTape.midBox ibox259))
    (by decide +kernel)
private theorem midpoint_even_259 : ∀ k, 2 ∣ (ibox259 k).lo+(ibox259 k).hi := by decide +kernel
private theorem accepted_259 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox259) tree259 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox259 midpoint_even_259
  simp only [tree259,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox259,candidate_valid h (FixedTape.midBox ibox259),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox259 212 (FixedTape.rowsAux denominator ibox259 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox259) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_259
private noncomputable def tree258 : TapeTree := .split 0 (((7596061425928238578684807201285868261379932160000000000 : Int) : ℚ)/(denominator : ℚ)) tree259 tree260
attribute [irreducible] tree258
private theorem accepted_258 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox258) tree258 = true := by
  simp only [tree258,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox258 0 (7596061425928238578684807201285868261379932160000000000 : Int) false,decode_split denominator ibox258 0 (7596061425928238578684807201285868261379932160000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_259 h,accepted_260 h⟩
private noncomputable def tree257 : TapeTree := .centered (candidateRows ibox257) (candidateRows (FixedTape.midBox ibox257))
attribute [irreducible] tree257
private theorem sign_257 : 2*denominator*(computed denominator (FixedTape.midBox ibox257)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox257).gradient k).lo.natAbs ((computed denominator ibox257).gradient k).hi.natAbs : Int)*((ibox257 k).hi-(ibox257 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox257
    (computed denominator ibox257) (computed denominator (FixedTape.midBox ibox257))
    (by decide +kernel)
private theorem midpoint_even_257 : ∀ k, 2 ∣ (ibox257 k).lo+(ibox257 k).hi := by decide +kernel
private theorem accepted_257 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox257) tree257 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox257 midpoint_even_257
  simp only [tree257,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox257,candidate_valid h (FixedTape.midBox ibox257),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox257 212 (FixedTape.rowsAux denominator ibox257 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox257) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_257
private noncomputable def tree256 : TapeTree := .centered (candidateRows ibox256) (candidateRows (FixedTape.midBox ibox256))
attribute [irreducible] tree256
private theorem sign_256 : 2*denominator*(computed denominator (FixedTape.midBox ibox256)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox256).gradient k).lo.natAbs ((computed denominator ibox256).gradient k).hi.natAbs : Int)*((ibox256 k).hi-(ibox256 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox256
    (computed denominator ibox256) (computed denominator (FixedTape.midBox ibox256))
    (by decide +kernel)
private theorem midpoint_even_256 : ∀ k, 2 ∣ (ibox256 k).lo+(ibox256 k).hi := by decide +kernel
private theorem accepted_256 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox256) tree256 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox256 midpoint_even_256
  simp only [tree256,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox256,candidate_valid h (FixedTape.midBox ibox256),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox256 212 (FixedTape.rowsAux denominator ibox256 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox256) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_256
private noncomputable def tree255 : TapeTree := .split 0 (((7413023801207076203294811847038016014117765120000000000 : Int) : ℚ)/(denominator : ℚ)) tree256 tree257
attribute [irreducible] tree255
private theorem accepted_255 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox255) tree255 = true := by
  simp only [tree255,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox255 0 (7413023801207076203294811847038016014117765120000000000 : Int) false,decode_split denominator ibox255 0 (7413023801207076203294811847038016014117765120000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_256 h,accepted_257 h⟩
private noncomputable def tree254 : TapeTree := .split 0 (((7504542613567657390989809524161942137748848640000000000 : Int) : ℚ)/(denominator : ℚ)) tree255 tree258
attribute [irreducible] tree254
private theorem accepted_254 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox254) tree254 = true := by
  simp only [tree254,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox254 0 (7504542613567657390989809524161942137748848640000000000 : Int) false,decode_split denominator ibox254 0 (7504542613567657390989809524161942137748848640000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_255 h,accepted_258 h⟩
private noncomputable def tree253 : TapeTree := .split 3 (((14344173039372724928522084904321482234422886400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree254 tree261
attribute [irreducible] tree253
private theorem accepted_253 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox253) tree253 = true := by
  simp only [tree253,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox253 3 (14344173039372724928522084904321482234422886400000000000000 : Int) false,decode_split denominator ibox253 3 (14344173039372724928522084904321482234422886400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_254 h,accepted_261 h⟩
private noncomputable def tree252 : TapeTree := .split 0 (((7687580238288819766379804878409794385011015680000000000 : Int) : ℚ)/(denominator : ℚ)) tree253 tree268
attribute [irreducible] tree252
private theorem accepted_252 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox252) tree252 = true := by
  simp only [tree252,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox252 0 (7687580238288819766379804878409794385011015680000000000 : Int) false,decode_split denominator ibox252 0 (7687580238288819766379804878409794385011015680000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_253 h,accepted_268 h⟩
private noncomputable def tree251 : TapeTree := .centered (candidateRows ibox251) (candidateRows (FixedTape.midBox ibox251))
attribute [irreducible] tree251
private theorem sign_251 : 2*denominator*(computed denominator (FixedTape.midBox ibox251)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox251).gradient k).lo.natAbs ((computed denominator ibox251).gradient k).hi.natAbs : Int)*((ibox251 k).hi-(ibox251 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox251
    (computed denominator ibox251) (computed denominator (FixedTape.midBox ibox251))
    (by decide +kernel)
private theorem midpoint_even_251 : ∀ k, 2 ∣ (ibox251 k).lo+(ibox251 k).hi := by decide +kernel
private theorem accepted_251 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox251) tree251 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox251 midpoint_even_251
  simp only [tree251,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox251,candidate_valid h (FixedTape.midBox ibox251),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox251 212 (FixedTape.rowsAux denominator ibox251 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox251) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_251
private noncomputable def tree250 : TapeTree := .centered (candidateRows ibox250) (candidateRows (FixedTape.midBox ibox250))
attribute [irreducible] tree250
private theorem sign_250 : 2*denominator*(computed denominator (FixedTape.midBox ibox250)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox250).gradient k).lo.natAbs ((computed denominator ibox250).gradient k).hi.natAbs : Int)*((ibox250 k).hi-(ibox250 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox250
    (computed denominator ibox250) (computed denominator (FixedTape.midBox ibox250))
    (by decide +kernel)
private theorem midpoint_even_250 : ∀ k, 2 ∣ (ibox250 k).lo+(ibox250 k).hi := by decide +kernel
private theorem accepted_250 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox250) tree250 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox250 midpoint_even_250
  simp only [tree250,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox250,candidate_valid h (FixedTape.midBox ibox250),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox250 212 (FixedTape.rowsAux denominator ibox250 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox250) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_250
private noncomputable def tree249 : TapeTree := .split 3 (((12431616634123028271385806917078617936499834880000000000000 : Int) : ℚ)/(denominator : ℚ)) tree250 tree251
attribute [irreducible] tree249
private theorem accepted_249 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox249) tree249 = true := by
  simp only [tree249,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox249 3 (12431616634123028271385806917078617936499834880000000000000 : Int) false,decode_split denominator ibox249 3 (12431616634123028271385806917078617936499834880000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_250 h,accepted_251 h⟩
private noncomputable def tree248 : TapeTree := .centered (candidateRows ibox248) (candidateRows (FixedTape.midBox ibox248))
attribute [irreducible] tree248
private theorem sign_248 : 2*denominator*(computed denominator (FixedTape.midBox ibox248)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox248).gradient k).lo.natAbs ((computed denominator ibox248).gradient k).hi.natAbs : Int)*((ibox248 k).hi-(ibox248 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox248
    (computed denominator ibox248) (computed denominator (FixedTape.midBox ibox248))
    (by decide +kernel)
private theorem midpoint_even_248 : ∀ k, 2 ∣ (ibox248 k).lo+(ibox248 k).hi := by decide +kernel
private theorem accepted_248 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox248) tree248 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox248 midpoint_even_248
  simp only [tree248,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox248,candidate_valid h (FixedTape.midBox ibox248),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox248 212 (FixedTape.rowsAux denominator ibox248 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox248) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_248
private noncomputable def tree247 : TapeTree := .centered (candidateRows ibox247) (candidateRows (FixedTape.midBox ibox247))
attribute [irreducible] tree247
private theorem sign_247 : 2*denominator*(computed denominator (FixedTape.midBox ibox247)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox247).gradient k).lo.natAbs ((computed denominator ibox247).gradient k).hi.natAbs : Int)*((ibox247 k).hi-(ibox247 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox247
    (computed denominator ibox247) (computed denominator (FixedTape.midBox ibox247))
    (by decide +kernel)
private theorem midpoint_even_247 : ∀ k, 2 ∣ (ibox247 k).lo+(ibox247 k).hi := by decide +kernel
private theorem accepted_247 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox247) tree247 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox247 midpoint_even_247
  simp only [tree247,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox247,candidate_valid h (FixedTape.midBox ibox247),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox247 212 (FixedTape.rowsAux denominator ibox247 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox247) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_247
private noncomputable def tree246 : TapeTree := .split 0 (((7779099050649400954074802555533720508642099200000000000 : Int) : ℚ)/(denominator : ℚ)) tree247 tree248
attribute [irreducible] tree246
private theorem accepted_246 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox246) tree246 = true := by
  simp only [tree246,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox246 0 (7779099050649400954074802555533720508642099200000000000 : Int) false,decode_split denominator ibox246 0 (7779099050649400954074802555533720508642099200000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_247 h,accepted_248 h⟩
private noncomputable def tree245 : TapeTree := .centered (candidateRows ibox245) (candidateRows (FixedTape.midBox ibox245))
attribute [irreducible] tree245
private theorem sign_245 : 2*denominator*(computed denominator (FixedTape.midBox ibox245)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox245).gradient k).lo.natAbs ((computed denominator ibox245).gradient k).hi.natAbs : Int)*((ibox245 k).hi-(ibox245 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox245
    (computed denominator ibox245) (computed denominator (FixedTape.midBox ibox245))
    (by decide +kernel)
private theorem midpoint_even_245 : ∀ k, 2 ∣ (ibox245 k).lo+(ibox245 k).hi := by decide +kernel
private theorem accepted_245 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox245) tree245 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox245 midpoint_even_245
  simp only [tree245,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox245,candidate_valid h (FixedTape.midBox ibox245),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox245 212 (FixedTape.rowsAux denominator ibox245 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox245) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_245
private noncomputable def tree244 : TapeTree := .centered (candidateRows ibox244) (candidateRows (FixedTape.midBox ibox244))
attribute [irreducible] tree244
private theorem sign_244 : 2*denominator*(computed denominator (FixedTape.midBox ibox244)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox244).gradient k).lo.natAbs ((computed denominator ibox244).gradient k).hi.natAbs : Int)*((ibox244 k).hi-(ibox244 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox244
    (computed denominator ibox244) (computed denominator (FixedTape.midBox ibox244))
    (by decide +kernel)
private theorem midpoint_even_244 : ∀ k, 2 ∣ (ibox244 k).lo+(ibox244 k).hi := by decide +kernel
private theorem accepted_244 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox244) tree244 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox244 midpoint_even_244
  simp only [tree244,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox244,candidate_valid h (FixedTape.midBox ibox244),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox244 212 (FixedTape.rowsAux denominator ibox244 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox244) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_244
private noncomputable def tree243 : TapeTree := .split 0 (((7779099050649400954074802555533720508642099200000000000 : Int) : ℚ)/(denominator : ℚ)) tree244 tree245
attribute [irreducible] tree243
private theorem accepted_243 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox243) tree243 = true := by
  simp only [tree243,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox243 0 (7779099050649400954074802555533720508642099200000000000 : Int) false,decode_split denominator ibox243 0 (7779099050649400954074802555533720508642099200000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_244 h,accepted_245 h⟩
private noncomputable def tree242 : TapeTree := .split 3 (((12431616634123028271385806917078617936499834880000000000000 : Int) : ℚ)/(denominator : ℚ)) tree243 tree246
attribute [irreducible] tree242
private theorem accepted_242 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox242) tree242 = true := by
  simp only [tree242,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox242 3 (12431616634123028271385806917078617936499834880000000000000 : Int) false,decode_split denominator ibox242 3 (12431616634123028271385806917078617936499834880000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_243 h,accepted_246 h⟩
private noncomputable def tree241 : TapeTree := .split 0 (((7870617863009982141769800232657646632273182720000000000 : Int) : ℚ)/(denominator : ℚ)) tree242 tree249
attribute [irreducible] tree241
private theorem accepted_241 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox241) tree241 = true := by
  simp only [tree241,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox241 0 (7870617863009982141769800232657646632273182720000000000 : Int) false,decode_split denominator ibox241 0 (7870617863009982141769800232657646632273182720000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_242 h,accepted_249 h⟩
private noncomputable def tree240 : TapeTree := .centered (candidateRows ibox240) (candidateRows (FixedTape.midBox ibox240))
attribute [irreducible] tree240
private theorem sign_240 : 2*denominator*(computed denominator (FixedTape.midBox ibox240)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox240).gradient k).lo.natAbs ((computed denominator ibox240).gradient k).hi.natAbs : Int)*((ibox240 k).hi-(ibox240 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox240
    (computed denominator ibox240) (computed denominator (FixedTape.midBox ibox240))
    (by decide +kernel)
private theorem midpoint_even_240 : ∀ k, 2 ∣ (ibox240 k).lo+(ibox240 k).hi := by decide +kernel
private theorem accepted_240 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox240) tree240 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox240 midpoint_even_240
  simp only [tree240,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox240,candidate_valid h (FixedTape.midBox ibox240),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox240 212 (FixedTape.rowsAux denominator ibox240 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox240) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_240
private noncomputable def tree239 : TapeTree := .centered (candidateRows ibox239) (candidateRows (FixedTape.midBox ibox239))
attribute [irreducible] tree239
private theorem sign_239 : 2*denominator*(computed denominator (FixedTape.midBox ibox239)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox239).gradient k).lo.natAbs ((computed denominator ibox239).gradient k).hi.natAbs : Int)*((ibox239 k).hi-(ibox239 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox239
    (computed denominator ibox239) (computed denominator (FixedTape.midBox ibox239))
    (by decide +kernel)
private theorem midpoint_even_239 : ∀ k, 2 ∣ (ibox239 k).lo+(ibox239 k).hi := by decide +kernel
private theorem accepted_239 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox239) tree239 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox239 midpoint_even_239
  simp only [tree239,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox239,candidate_valid h (FixedTape.midBox ibox239),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox239 212 (FixedTape.rowsAux denominator ibox239 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox239) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_239
private noncomputable def tree238 : TapeTree := .split 0 (((7596061425928238578684807201285868261379932160000000000 : Int) : ℚ)/(denominator : ℚ)) tree239 tree240
attribute [irreducible] tree238
private theorem accepted_238 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox238) tree238 = true := by
  simp only [tree238,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox238 0 (7596061425928238578684807201285868261379932160000000000 : Int) false,decode_split denominator ibox238 0 (7596061425928238578684807201285868261379932160000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_239 h,accepted_240 h⟩
private noncomputable def tree237 : TapeTree := .centered (candidateRows ibox237) (candidateRows (FixedTape.midBox ibox237))
attribute [irreducible] tree237
private theorem sign_237 : 2*denominator*(computed denominator (FixedTape.midBox ibox237)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox237).gradient k).lo.natAbs ((computed denominator ibox237).gradient k).hi.natAbs : Int)*((ibox237 k).hi-(ibox237 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox237
    (computed denominator ibox237) (computed denominator (FixedTape.midBox ibox237))
    (by decide +kernel)
private theorem midpoint_even_237 : ∀ k, 2 ∣ (ibox237 k).lo+(ibox237 k).hi := by decide +kernel
private theorem accepted_237 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox237) tree237 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox237 midpoint_even_237
  simp only [tree237,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox237,candidate_valid h (FixedTape.midBox ibox237),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox237 212 (FixedTape.rowsAux denominator ibox237 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox237) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_237
private noncomputable def tree236 : TapeTree := .centered (candidateRows ibox236) (candidateRows (FixedTape.midBox ibox236))
attribute [irreducible] tree236
private theorem sign_236 : 2*denominator*(computed denominator (FixedTape.midBox ibox236)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox236).gradient k).lo.natAbs ((computed denominator ibox236).gradient k).hi.natAbs : Int)*((ibox236 k).hi-(ibox236 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox236
    (computed denominator ibox236) (computed denominator (FixedTape.midBox ibox236))
    (by decide +kernel)
private theorem midpoint_even_236 : ∀ k, 2 ∣ (ibox236 k).lo+(ibox236 k).hi := by decide +kernel
private theorem accepted_236 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox236) tree236 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox236 midpoint_even_236
  simp only [tree236,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox236,candidate_valid h (FixedTape.midBox ibox236),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox236 212 (FixedTape.rowsAux denominator ibox236 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox236) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_236
private noncomputable def tree235 : TapeTree := .split 0 (((7596061425928238578684807201285868261379932160000000000 : Int) : ℚ)/(denominator : ℚ)) tree236 tree237
attribute [irreducible] tree235
private theorem accepted_235 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox235) tree235 = true := by
  simp only [tree235,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox235 0 (7596061425928238578684807201285868261379932160000000000 : Int) false,decode_split denominator ibox235 0 (7596061425928238578684807201285868261379932160000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_236 h,accepted_237 h⟩
private noncomputable def tree234 : TapeTree := .split 3 (((12431616634123028271385806917078617936499834880000000000000 : Int) : ℚ)/(denominator : ℚ)) tree235 tree238
attribute [irreducible] tree234
private theorem accepted_234 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox234) tree234 = true := by
  simp only [tree234,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox234 3 (12431616634123028271385806917078617936499834880000000000000 : Int) false,decode_split denominator ibox234 3 (12431616634123028271385806917078617936499834880000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_235 h,accepted_238 h⟩
private noncomputable def tree233 : TapeTree := .centered (candidateRows ibox233) (candidateRows (FixedTape.midBox ibox233))
attribute [irreducible] tree233
private theorem sign_233 : 2*denominator*(computed denominator (FixedTape.midBox ibox233)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox233).gradient k).lo.natAbs ((computed denominator ibox233).gradient k).hi.natAbs : Int)*((ibox233 k).hi-(ibox233 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox233
    (computed denominator ibox233) (computed denominator (FixedTape.midBox ibox233))
    (by decide +kernel)
private theorem midpoint_even_233 : ∀ k, 2 ∣ (ibox233 k).lo+(ibox233 k).hi := by decide +kernel
private theorem accepted_233 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox233) tree233 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox233 midpoint_even_233
  simp only [tree233,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox233,candidate_valid h (FixedTape.midBox ibox233),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox233 212 (FixedTape.rowsAux denominator ibox233 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox233) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_233
private noncomputable def tree232 : TapeTree := .centered (candidateRows ibox232) (candidateRows (FixedTape.midBox ibox232))
attribute [irreducible] tree232
private theorem sign_232 : 2*denominator*(computed denominator (FixedTape.midBox ibox232)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox232).gradient k).lo.natAbs ((computed denominator ibox232).gradient k).hi.natAbs : Int)*((ibox232 k).hi-(ibox232 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox232
    (computed denominator ibox232) (computed denominator (FixedTape.midBox ibox232))
    (by decide +kernel)
private theorem midpoint_even_232 : ∀ k, 2 ∣ (ibox232 k).lo+(ibox232 k).hi := by decide +kernel
private theorem accepted_232 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox232) tree232 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox232 midpoint_even_232
  simp only [tree232,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox232,candidate_valid h (FixedTape.midBox ibox232),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox232 212 (FixedTape.rowsAux denominator ibox232 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox232) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_232
private noncomputable def tree231 : TapeTree := .split 0 (((7413023801207076203294811847038016014117765120000000000 : Int) : ℚ)/(denominator : ℚ)) tree232 tree233
attribute [irreducible] tree231
private theorem accepted_231 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox231) tree231 = true := by
  simp only [tree231,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox231 0 (7413023801207076203294811847038016014117765120000000000 : Int) false,decode_split denominator ibox231 0 (7413023801207076203294811847038016014117765120000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_232 h,accepted_233 h⟩
private noncomputable def tree230 : TapeTree := .centered (candidateRows ibox230) (candidateRows (FixedTape.midBox ibox230))
attribute [irreducible] tree230
private theorem sign_230 : 2*denominator*(computed denominator (FixedTape.midBox ibox230)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox230).gradient k).lo.natAbs ((computed denominator ibox230).gradient k).hi.natAbs : Int)*((ibox230 k).hi-(ibox230 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox230
    (computed denominator ibox230) (computed denominator (FixedTape.midBox ibox230))
    (by decide +kernel)
private theorem midpoint_even_230 : ∀ k, 2 ∣ (ibox230 k).lo+(ibox230 k).hi := by decide +kernel
private theorem accepted_230 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox230) tree230 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox230 midpoint_even_230
  simp only [tree230,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox230,candidate_valid h (FixedTape.midBox ibox230),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox230 212 (FixedTape.rowsAux denominator ibox230 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox230) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_230
private noncomputable def tree229 : TapeTree := .centered (candidateRows ibox229) (candidateRows (FixedTape.midBox ibox229))
attribute [irreducible] tree229
private theorem sign_229 : 2*denominator*(computed denominator (FixedTape.midBox ibox229)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox229).gradient k).lo.natAbs ((computed denominator ibox229).gradient k).hi.natAbs : Int)*((ibox229 k).hi-(ibox229 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox229
    (computed denominator ibox229) (computed denominator (FixedTape.midBox ibox229))
    (by decide +kernel)
private theorem midpoint_even_229 : ∀ k, 2 ∣ (ibox229 k).lo+(ibox229 k).hi := by decide +kernel
private theorem accepted_229 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox229) tree229 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox229 midpoint_even_229
  simp only [tree229,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox229,candidate_valid h (FixedTape.midBox ibox229),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox229 212 (FixedTape.rowsAux denominator ibox229 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox229) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_229
private noncomputable def tree228 : TapeTree := .split 0 (((7413023801207076203294811847038016014117765120000000000 : Int) : ℚ)/(denominator : ℚ)) tree229 tree230
attribute [irreducible] tree228
private theorem accepted_228 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox228) tree228 = true := by
  simp only [tree228,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox228 0 (7413023801207076203294811847038016014117765120000000000 : Int) false,decode_split denominator ibox228 0 (7413023801207076203294811847038016014117765120000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_229 h,accepted_230 h⟩
private noncomputable def tree227 : TapeTree := .split 3 (((12431616634123028271385806917078617936499834880000000000000 : Int) : ℚ)/(denominator : ℚ)) tree228 tree231
attribute [irreducible] tree227
private theorem accepted_227 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox227) tree227 = true := by
  simp only [tree227,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox227 3 (12431616634123028271385806917078617936499834880000000000000 : Int) false,decode_split denominator ibox227 3 (12431616634123028271385806917078617936499834880000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_228 h,accepted_231 h⟩
private noncomputable def tree226 : TapeTree := .split 0 (((7504542613567657390989809524161942137748848640000000000 : Int) : ℚ)/(denominator : ℚ)) tree227 tree234
attribute [irreducible] tree226
private theorem accepted_226 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox226) tree226 = true := by
  simp only [tree226,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox226 0 (7504542613567657390989809524161942137748848640000000000 : Int) false,decode_split denominator ibox226 0 (7504542613567657390989809524161942137748848640000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_227 h,accepted_234 h⟩
private noncomputable def tree225 : TapeTree := .split 0 (((7687580238288819766379804878409794385011015680000000000 : Int) : ℚ)/(denominator : ℚ)) tree226 tree241
attribute [irreducible] tree225
private theorem accepted_225 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox225) tree225 = true := by
  simp only [tree225,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox225 0 (7687580238288819766379804878409794385011015680000000000 : Int) false,decode_split denominator ibox225 0 (7687580238288819766379804878409794385011015680000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_226 h,accepted_241 h⟩
private noncomputable def tree224 : TapeTree := .split 3 (((13387894836747876599953945910700050085461360640000000000000 : Int) : ℚ)/(denominator : ℚ)) tree225 tree252
attribute [irreducible] tree224
private theorem accepted_224 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox224) tree224 = true := by
  simp only [tree224,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox224 3 (13387894836747876599953945910700050085461360640000000000000 : Int) false,decode_split denominator ibox224 3 (13387894836747876599953945910700050085461360640000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_225 h,accepted_252 h⟩
private noncomputable def tree223 : TapeTree := .centered (candidateRows ibox223) (candidateRows (FixedTape.midBox ibox223))
attribute [irreducible] tree223
private theorem sign_223 : 2*denominator*(computed denominator (FixedTape.midBox ibox223)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox223).gradient k).lo.natAbs ((computed denominator ibox223).gradient k).hi.natAbs : Int)*((ibox223 k).hi-(ibox223 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox223
    (computed denominator ibox223) (computed denominator (FixedTape.midBox ibox223))
    (by decide +kernel)
private theorem midpoint_even_223 : ∀ k, 2 ∣ (ibox223 k).lo+(ibox223 k).hi := by decide +kernel
private theorem accepted_223 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox223) tree223 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox223 midpoint_even_223
  simp only [tree223,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox223,candidate_valid h (FixedTape.midBox ibox223),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox223 212 (FixedTape.rowsAux denominator ibox223 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox223) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_223
private noncomputable def tree222 : TapeTree := .centered (candidateRows ibox222) (candidateRows (FixedTape.midBox ibox222))
attribute [irreducible] tree222
private theorem sign_222 : 2*denominator*(computed denominator (FixedTape.midBox ibox222)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox222).gradient k).lo.natAbs ((computed denominator ibox222).gradient k).hi.natAbs : Int)*((ibox222 k).hi-(ibox222 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox222
    (computed denominator ibox222) (computed denominator (FixedTape.midBox ibox222))
    (by decide +kernel)
private theorem midpoint_even_222 : ∀ k, 2 ∣ (ibox222 k).lo+(ibox222 k).hi := by decide +kernel
private theorem accepted_222 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox222) tree222 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox222 midpoint_even_222
  simp only [tree222,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox222,candidate_valid h (FixedTape.midBox ibox222),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox222 212 (FixedTape.rowsAux denominator ibox222 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox222) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_222
private noncomputable def tree221 : TapeTree := .split 3 (((10519060228873331614249528929835753638576783360000000000000 : Int) : ℚ)/(denominator : ℚ)) tree222 tree223
attribute [irreducible] tree221
private theorem accepted_221 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox221) tree221 = true := by
  simp only [tree221,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox221 3 (10519060228873331614249528929835753638576783360000000000000 : Int) false,decode_split denominator ibox221 3 (10519060228873331614249528929835753638576783360000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_222 h,accepted_223 h⟩
private noncomputable def tree220 : TapeTree := .centered (candidateRows ibox220) (candidateRows (FixedTape.midBox ibox220))
attribute [irreducible] tree220
private theorem sign_220 : 2*denominator*(computed denominator (FixedTape.midBox ibox220)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox220).gradient k).lo.natAbs ((computed denominator ibox220).gradient k).hi.natAbs : Int)*((ibox220 k).hi-(ibox220 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox220
    (computed denominator ibox220) (computed denominator (FixedTape.midBox ibox220))
    (by decide +kernel)
private theorem midpoint_even_220 : ∀ k, 2 ∣ (ibox220 k).lo+(ibox220 k).hi := by decide +kernel
private theorem accepted_220 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox220) tree220 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox220 midpoint_even_220
  simp only [tree220,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox220,candidate_valid h (FixedTape.midBox ibox220),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox220 212 (FixedTape.rowsAux denominator ibox220 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox220) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_220
private noncomputable def tree219 : TapeTree := .centered (candidateRows ibox219) (candidateRows (FixedTape.midBox ibox219))
attribute [irreducible] tree219
private theorem sign_219 : 2*denominator*(computed denominator (FixedTape.midBox ibox219)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox219).gradient k).lo.natAbs ((computed denominator ibox219).gradient k).hi.natAbs : Int)*((ibox219 k).hi-(ibox219 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox219
    (computed denominator ibox219) (computed denominator (FixedTape.midBox ibox219))
    (by decide +kernel)
private theorem midpoint_even_219 : ∀ k, 2 ∣ (ibox219 k).lo+(ibox219 k).hi := by decide +kernel
private theorem accepted_219 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox219) tree219 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox219 midpoint_even_219
  simp only [tree219,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox219,candidate_valid h (FixedTape.midBox ibox219),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox219 212 (FixedTape.rowsAux denominator ibox219 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox219) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_219
private noncomputable def tree218 : TapeTree := .split 0 (((7779099050649400954074802555533720508642099200000000000 : Int) : ℚ)/(denominator : ℚ)) tree219 tree220
attribute [irreducible] tree218
private theorem accepted_218 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox218) tree218 = true := by
  simp only [tree218,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox218 0 (7779099050649400954074802555533720508642099200000000000 : Int) false,decode_split denominator ibox218 0 (7779099050649400954074802555533720508642099200000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_219 h,accepted_220 h⟩
private noncomputable def tree217 : TapeTree := .centered (candidateRows ibox217) (candidateRows (FixedTape.midBox ibox217))
attribute [irreducible] tree217
private theorem sign_217 : 2*denominator*(computed denominator (FixedTape.midBox ibox217)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox217).gradient k).lo.natAbs ((computed denominator ibox217).gradient k).hi.natAbs : Int)*((ibox217 k).hi-(ibox217 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox217
    (computed denominator ibox217) (computed denominator (FixedTape.midBox ibox217))
    (by decide +kernel)
private theorem midpoint_even_217 : ∀ k, 2 ∣ (ibox217 k).lo+(ibox217 k).hi := by decide +kernel
private theorem accepted_217 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox217) tree217 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox217 midpoint_even_217
  simp only [tree217,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox217,candidate_valid h (FixedTape.midBox ibox217),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox217 212 (FixedTape.rowsAux denominator ibox217 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox217) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_217
private noncomputable def tree216 : TapeTree := .centered (candidateRows ibox216) (candidateRows (FixedTape.midBox ibox216))
attribute [irreducible] tree216
private theorem sign_216 : 2*denominator*(computed denominator (FixedTape.midBox ibox216)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox216).gradient k).lo.natAbs ((computed denominator ibox216).gradient k).hi.natAbs : Int)*((ibox216 k).hi-(ibox216 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox216
    (computed denominator ibox216) (computed denominator (FixedTape.midBox ibox216))
    (by decide +kernel)
private theorem midpoint_even_216 : ∀ k, 2 ∣ (ibox216 k).lo+(ibox216 k).hi := by decide +kernel
private theorem accepted_216 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox216) tree216 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox216 midpoint_even_216
  simp only [tree216,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox216,candidate_valid h (FixedTape.midBox ibox216),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox216 212 (FixedTape.rowsAux denominator ibox216 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox216) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_216
private noncomputable def tree215 : TapeTree := .split 0 (((7779099050649400954074802555533720508642099200000000000 : Int) : ℚ)/(denominator : ℚ)) tree216 tree217
attribute [irreducible] tree215
private theorem accepted_215 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox215) tree215 = true := by
  simp only [tree215,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox215 0 (7779099050649400954074802555533720508642099200000000000 : Int) false,decode_split denominator ibox215 0 (7779099050649400954074802555533720508642099200000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_216 h,accepted_217 h⟩
private noncomputable def tree214 : TapeTree := .split 3 (((10519060228873331614249528929835753638576783360000000000000 : Int) : ℚ)/(denominator : ℚ)) tree215 tree218
attribute [irreducible] tree214
private theorem accepted_214 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox214) tree214 = true := by
  simp only [tree214,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox214 3 (10519060228873331614249528929835753638576783360000000000000 : Int) false,decode_split denominator ibox214 3 (10519060228873331614249528929835753638576783360000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_215 h,accepted_218 h⟩
private noncomputable def tree213 : TapeTree := .split 0 (((7870617863009982141769800232657646632273182720000000000 : Int) : ℚ)/(denominator : ℚ)) tree214 tree221
attribute [irreducible] tree213
private theorem accepted_213 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox213) tree213 = true := by
  simp only [tree213,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox213 0 (7870617863009982141769800232657646632273182720000000000 : Int) false,decode_split denominator ibox213 0 (7870617863009982141769800232657646632273182720000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_214 h,accepted_221 h⟩
private noncomputable def tree212 : TapeTree := .centered (candidateRows ibox212) (candidateRows (FixedTape.midBox ibox212))
attribute [irreducible] tree212
private theorem sign_212 : 2*denominator*(computed denominator (FixedTape.midBox ibox212)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox212).gradient k).lo.natAbs ((computed denominator ibox212).gradient k).hi.natAbs : Int)*((ibox212 k).hi-(ibox212 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox212
    (computed denominator ibox212) (computed denominator (FixedTape.midBox ibox212))
    (by decide +kernel)
private theorem midpoint_even_212 : ∀ k, 2 ∣ (ibox212 k).lo+(ibox212 k).hi := by decide +kernel
private theorem accepted_212 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox212) tree212 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox212 midpoint_even_212
  simp only [tree212,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox212,candidate_valid h (FixedTape.midBox ibox212),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox212 212 (FixedTape.rowsAux denominator ibox212 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox212) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_212
private noncomputable def tree211 : TapeTree := .centered (candidateRows ibox211) (candidateRows (FixedTape.midBox ibox211))
attribute [irreducible] tree211
private theorem sign_211 : 2*denominator*(computed denominator (FixedTape.midBox ibox211)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox211).gradient k).lo.natAbs ((computed denominator ibox211).gradient k).hi.natAbs : Int)*((ibox211 k).hi-(ibox211 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox211
    (computed denominator ibox211) (computed denominator (FixedTape.midBox ibox211))
    (by decide +kernel)
private theorem midpoint_even_211 : ∀ k, 2 ∣ (ibox211 k).lo+(ibox211 k).hi := by decide +kernel
private theorem accepted_211 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox211) tree211 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox211 midpoint_even_211
  simp only [tree211,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox211,candidate_valid h (FixedTape.midBox ibox211),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox211 212 (FixedTape.rowsAux denominator ibox211 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox211) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_211
private noncomputable def tree210 : TapeTree := .split 0 (((7962136675370563329464797909781572755904266240000000000 : Int) : ℚ)/(denominator : ℚ)) tree211 tree212
attribute [irreducible] tree210
private theorem accepted_210 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox210) tree210 = true := by
  simp only [tree210,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox210 0 (7962136675370563329464797909781572755904266240000000000 : Int) false,decode_split denominator ibox210 0 (7962136675370563329464797909781572755904266240000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_211 h,accepted_212 h⟩
private noncomputable def tree209 : TapeTree := .centered (candidateRows ibox209) (candidateRows (FixedTape.midBox ibox209))
attribute [irreducible] tree209
private theorem sign_209 : 2*denominator*(computed denominator (FixedTape.midBox ibox209)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox209).gradient k).lo.natAbs ((computed denominator ibox209).gradient k).hi.natAbs : Int)*((ibox209 k).hi-(ibox209 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox209
    (computed denominator ibox209) (computed denominator (FixedTape.midBox ibox209))
    (by decide +kernel)
private theorem midpoint_even_209 : ∀ k, 2 ∣ (ibox209 k).lo+(ibox209 k).hi := by decide +kernel
private theorem accepted_209 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox209) tree209 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox209 midpoint_even_209
  simp only [tree209,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox209,candidate_valid h (FixedTape.midBox ibox209),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox209 212 (FixedTape.rowsAux denominator ibox209 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox209) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_209
private noncomputable def tree208 : TapeTree := .centered (candidateRows ibox208) (candidateRows (FixedTape.midBox ibox208))
attribute [irreducible] tree208
private theorem sign_208 : 2*denominator*(computed denominator (FixedTape.midBox ibox208)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox208).gradient k).lo.natAbs ((computed denominator ibox208).gradient k).hi.natAbs : Int)*((ibox208 k).hi-(ibox208 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox208
    (computed denominator ibox208) (computed denominator (FixedTape.midBox ibox208))
    (by decide +kernel)
private theorem midpoint_even_208 : ∀ k, 2 ∣ (ibox208 k).lo+(ibox208 k).hi := by decide +kernel
private theorem accepted_208 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox208) tree208 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox208 midpoint_even_208
  simp only [tree208,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox208,candidate_valid h (FixedTape.midBox ibox208),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox208 212 (FixedTape.rowsAux denominator ibox208 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox208) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_208
private noncomputable def tree207 : TapeTree := .split 0 (((7962136675370563329464797909781572755904266240000000000 : Int) : ℚ)/(denominator : ℚ)) tree208 tree209
attribute [irreducible] tree207
private theorem accepted_207 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox207) tree207 = true := by
  simp only [tree207,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox207 0 (7962136675370563329464797909781572755904266240000000000 : Int) false,decode_split denominator ibox207 0 (7962136675370563329464797909781572755904266240000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_208 h,accepted_209 h⟩
private noncomputable def tree206 : TapeTree := .split 3 (((8606503823623634957113250942592889340653731840000000000000 : Int) : ℚ)/(denominator : ℚ)) tree207 tree210
attribute [irreducible] tree206
private theorem accepted_206 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox206) tree206 = true := by
  simp only [tree206,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox206 3 (8606503823623634957113250942592889340653731840000000000000 : Int) false,decode_split denominator ibox206 3 (8606503823623634957113250942592889340653731840000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_207 h,accepted_210 h⟩
private noncomputable def tree205 : TapeTree := .centered (candidateRows ibox205) (candidateRows (FixedTape.midBox ibox205))
attribute [irreducible] tree205
private theorem sign_205 : 2*denominator*(computed denominator (FixedTape.midBox ibox205)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox205).gradient k).lo.natAbs ((computed denominator ibox205).gradient k).hi.natAbs : Int)*((ibox205 k).hi-(ibox205 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox205
    (computed denominator ibox205) (computed denominator (FixedTape.midBox ibox205))
    (by decide +kernel)
private theorem midpoint_even_205 : ∀ k, 2 ∣ (ibox205 k).lo+(ibox205 k).hi := by decide +kernel
private theorem accepted_205 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox205) tree205 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox205 midpoint_even_205
  simp only [tree205,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox205,candidate_valid h (FixedTape.midBox ibox205),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox205 212 (FixedTape.rowsAux denominator ibox205 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox205) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_205
private noncomputable def tree204 : TapeTree := .centered (candidateRows ibox204) (candidateRows (FixedTape.midBox ibox204))
attribute [irreducible] tree204
private theorem sign_204 : 2*denominator*(computed denominator (FixedTape.midBox ibox204)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox204).gradient k).lo.natAbs ((computed denominator ibox204).gradient k).hi.natAbs : Int)*((ibox204 k).hi-(ibox204 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox204
    (computed denominator ibox204) (computed denominator (FixedTape.midBox ibox204))
    (by decide +kernel)
private theorem midpoint_even_204 : ∀ k, 2 ∣ (ibox204 k).lo+(ibox204 k).hi := by decide +kernel
private theorem accepted_204 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox204) tree204 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox204 midpoint_even_204
  simp only [tree204,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox204,candidate_valid h (FixedTape.midBox ibox204),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox204 212 (FixedTape.rowsAux denominator ibox204 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox204) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_204
private noncomputable def tree203 : TapeTree := .split 0 (((7779099050649400954074802555533720508642099200000000000 : Int) : ℚ)/(denominator : ℚ)) tree204 tree205
attribute [irreducible] tree203
private theorem accepted_203 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox203) tree203 = true := by
  simp only [tree203,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox203 0 (7779099050649400954074802555533720508642099200000000000 : Int) false,decode_split denominator ibox203 0 (7779099050649400954074802555533720508642099200000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_204 h,accepted_205 h⟩
private noncomputable def tree202 : TapeTree := .centered (candidateRows ibox202) (candidateRows (FixedTape.midBox ibox202))
attribute [irreducible] tree202
private theorem sign_202 : 2*denominator*(computed denominator (FixedTape.midBox ibox202)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox202).gradient k).lo.natAbs ((computed denominator ibox202).gradient k).hi.natAbs : Int)*((ibox202 k).hi-(ibox202 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox202
    (computed denominator ibox202) (computed denominator (FixedTape.midBox ibox202))
    (by decide +kernel)
private theorem midpoint_even_202 : ∀ k, 2 ∣ (ibox202 k).lo+(ibox202 k).hi := by decide +kernel
private theorem accepted_202 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox202) tree202 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox202 midpoint_even_202
  simp only [tree202,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox202,candidate_valid h (FixedTape.midBox ibox202),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox202 212 (FixedTape.rowsAux denominator ibox202 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox202) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_202
private noncomputable def tree201 : TapeTree := .centered (candidateRows ibox201) (candidateRows (FixedTape.midBox ibox201))
attribute [irreducible] tree201
private theorem sign_201 : 2*denominator*(computed denominator (FixedTape.midBox ibox201)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox201).gradient k).lo.natAbs ((computed denominator ibox201).gradient k).hi.natAbs : Int)*((ibox201 k).hi-(ibox201 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox201
    (computed denominator ibox201) (computed denominator (FixedTape.midBox ibox201))
    (by decide +kernel)
private theorem midpoint_even_201 : ∀ k, 2 ∣ (ibox201 k).lo+(ibox201 k).hi := by decide +kernel
private theorem accepted_201 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox201) tree201 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox201 midpoint_even_201
  simp only [tree201,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox201,candidate_valid h (FixedTape.midBox ibox201),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox201 212 (FixedTape.rowsAux denominator ibox201 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox201) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_201
private noncomputable def tree200 : TapeTree := .split 0 (((7779099050649400954074802555533720508642099200000000000 : Int) : ℚ)/(denominator : ℚ)) tree201 tree202
attribute [irreducible] tree200
private theorem accepted_200 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox200) tree200 = true := by
  simp only [tree200,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox200 0 (7779099050649400954074802555533720508642099200000000000 : Int) false,decode_split denominator ibox200 0 (7779099050649400954074802555533720508642099200000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_201 h,accepted_202 h⟩
private noncomputable def tree199 : TapeTree := .split 3 (((8606503823623634957113250942592889340653731840000000000000 : Int) : ℚ)/(denominator : ℚ)) tree200 tree203
attribute [irreducible] tree199
private theorem accepted_199 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox199) tree199 = true := by
  simp only [tree199,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox199 3 (8606503823623634957113250942592889340653731840000000000000 : Int) false,decode_split denominator ibox199 3 (8606503823623634957113250942592889340653731840000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_200 h,accepted_203 h⟩
private noncomputable def tree198 : TapeTree := .split 0 (((7870617863009982141769800232657646632273182720000000000 : Int) : ℚ)/(denominator : ℚ)) tree199 tree206
attribute [irreducible] tree198
private theorem accepted_198 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox198) tree198 = true := by
  simp only [tree198,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox198 0 (7870617863009982141769800232657646632273182720000000000 : Int) false,decode_split denominator ibox198 0 (7870617863009982141769800232657646632273182720000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_199 h,accepted_206 h⟩
private noncomputable def tree197 : TapeTree := .split 3 (((9562782026248483285681389936214321489615257600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree198 tree213
attribute [irreducible] tree197
private theorem accepted_197 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox197) tree197 = true := by
  simp only [tree197,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox197 3 (9562782026248483285681389936214321489615257600000000000000 : Int) false,decode_split denominator ibox197 3 (9562782026248483285681389936214321489615257600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_198 h,accepted_213 h⟩
private noncomputable def tree196 : TapeTree := .centered (candidateRows ibox196) (candidateRows (FixedTape.midBox ibox196))
attribute [irreducible] tree196
private theorem sign_196 : 2*denominator*(computed denominator (FixedTape.midBox ibox196)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox196).gradient k).lo.natAbs ((computed denominator ibox196).gradient k).hi.natAbs : Int)*((ibox196 k).hi-(ibox196 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox196
    (computed denominator ibox196) (computed denominator (FixedTape.midBox ibox196))
    (by decide +kernel)
private theorem midpoint_even_196 : ∀ k, 2 ∣ (ibox196 k).lo+(ibox196 k).hi := by decide +kernel
private theorem accepted_196 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox196) tree196 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox196 midpoint_even_196
  simp only [tree196,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox196,candidate_valid h (FixedTape.midBox ibox196),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox196 212 (FixedTape.rowsAux denominator ibox196 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox196) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_196
private noncomputable def tree195 : TapeTree := .centered (candidateRows ibox195) (candidateRows (FixedTape.midBox ibox195))
attribute [irreducible] tree195
private theorem sign_195 : 2*denominator*(computed denominator (FixedTape.midBox ibox195)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox195).gradient k).lo.natAbs ((computed denominator ibox195).gradient k).hi.natAbs : Int)*((ibox195 k).hi-(ibox195 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox195
    (computed denominator ibox195) (computed denominator (FixedTape.midBox ibox195))
    (by decide +kernel)
private theorem midpoint_even_195 : ∀ k, 2 ∣ (ibox195 k).lo+(ibox195 k).hi := by decide +kernel
private theorem accepted_195 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox195) tree195 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox195 midpoint_even_195
  simp only [tree195,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox195,candidate_valid h (FixedTape.midBox ibox195),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox195 212 (FixedTape.rowsAux denominator ibox195 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox195) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_195
private noncomputable def tree194 : TapeTree := .split 0 (((7596061425928238578684807201285868261379932160000000000 : Int) : ℚ)/(denominator : ℚ)) tree195 tree196
attribute [irreducible] tree194
private theorem accepted_194 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox194) tree194 = true := by
  simp only [tree194,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox194 0 (7596061425928238578684807201285868261379932160000000000 : Int) false,decode_split denominator ibox194 0 (7596061425928238578684807201285868261379932160000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_195 h,accepted_196 h⟩
private noncomputable def tree193 : TapeTree := .centered (candidateRows ibox193) (candidateRows (FixedTape.midBox ibox193))
attribute [irreducible] tree193
private theorem sign_193 : 2*denominator*(computed denominator (FixedTape.midBox ibox193)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox193).gradient k).lo.natAbs ((computed denominator ibox193).gradient k).hi.natAbs : Int)*((ibox193 k).hi-(ibox193 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox193
    (computed denominator ibox193) (computed denominator (FixedTape.midBox ibox193))
    (by decide +kernel)
private theorem midpoint_even_193 : ∀ k, 2 ∣ (ibox193 k).lo+(ibox193 k).hi := by decide +kernel
private theorem accepted_193 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox193) tree193 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox193 midpoint_even_193
  simp only [tree193,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox193,candidate_valid h (FixedTape.midBox ibox193),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox193 212 (FixedTape.rowsAux denominator ibox193 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox193) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_193
private noncomputable def tree192 : TapeTree := .centered (candidateRows ibox192) (candidateRows (FixedTape.midBox ibox192))
attribute [irreducible] tree192
private theorem sign_192 : 2*denominator*(computed denominator (FixedTape.midBox ibox192)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox192).gradient k).lo.natAbs ((computed denominator ibox192).gradient k).hi.natAbs : Int)*((ibox192 k).hi-(ibox192 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox192
    (computed denominator ibox192) (computed denominator (FixedTape.midBox ibox192))
    (by decide +kernel)
private theorem midpoint_even_192 : ∀ k, 2 ∣ (ibox192 k).lo+(ibox192 k).hi := by decide +kernel
private theorem accepted_192 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox192) tree192 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox192 midpoint_even_192
  simp only [tree192,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox192,candidate_valid h (FixedTape.midBox ibox192),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox192 212 (FixedTape.rowsAux denominator ibox192 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox192) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_192
private noncomputable def tree191 : TapeTree := .split 0 (((7596061425928238578684807201285868261379932160000000000 : Int) : ℚ)/(denominator : ℚ)) tree192 tree193
attribute [irreducible] tree191
private theorem accepted_191 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox191) tree191 = true := by
  simp only [tree191,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox191 0 (7596061425928238578684807201285868261379932160000000000 : Int) false,decode_split denominator ibox191 0 (7596061425928238578684807201285868261379932160000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_192 h,accepted_193 h⟩
private noncomputable def tree190 : TapeTree := .split 3 (((10519060228873331614249528929835753638576783360000000000000 : Int) : ℚ)/(denominator : ℚ)) tree191 tree194
attribute [irreducible] tree190
private theorem accepted_190 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox190) tree190 = true := by
  simp only [tree190,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox190 3 (10519060228873331614249528929835753638576783360000000000000 : Int) false,decode_split denominator ibox190 3 (10519060228873331614249528929835753638576783360000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_191 h,accepted_194 h⟩
private noncomputable def tree189 : TapeTree := .centered (candidateRows ibox189) (candidateRows (FixedTape.midBox ibox189))
attribute [irreducible] tree189
private theorem sign_189 : 2*denominator*(computed denominator (FixedTape.midBox ibox189)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox189).gradient k).lo.natAbs ((computed denominator ibox189).gradient k).hi.natAbs : Int)*((ibox189 k).hi-(ibox189 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox189
    (computed denominator ibox189) (computed denominator (FixedTape.midBox ibox189))
    (by decide +kernel)
private theorem midpoint_even_189 : ∀ k, 2 ∣ (ibox189 k).lo+(ibox189 k).hi := by decide +kernel
private theorem accepted_189 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox189) tree189 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox189 midpoint_even_189
  simp only [tree189,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox189,candidate_valid h (FixedTape.midBox ibox189),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox189 212 (FixedTape.rowsAux denominator ibox189 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox189) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_189
private noncomputable def tree188 : TapeTree := .centered (candidateRows ibox188) (candidateRows (FixedTape.midBox ibox188))
attribute [irreducible] tree188
private theorem sign_188 : 2*denominator*(computed denominator (FixedTape.midBox ibox188)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox188).gradient k).lo.natAbs ((computed denominator ibox188).gradient k).hi.natAbs : Int)*((ibox188 k).hi-(ibox188 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox188
    (computed denominator ibox188) (computed denominator (FixedTape.midBox ibox188))
    (by decide +kernel)
private theorem midpoint_even_188 : ∀ k, 2 ∣ (ibox188 k).lo+(ibox188 k).hi := by decide +kernel
private theorem accepted_188 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox188) tree188 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox188 midpoint_even_188
  simp only [tree188,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox188,candidate_valid h (FixedTape.midBox ibox188),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox188 212 (FixedTape.rowsAux denominator ibox188 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox188) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_188
private noncomputable def tree187 : TapeTree := .split 0 (((7413023801207076203294811847038016014117765120000000000 : Int) : ℚ)/(denominator : ℚ)) tree188 tree189
attribute [irreducible] tree187
private theorem accepted_187 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox187) tree187 = true := by
  simp only [tree187,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox187 0 (7413023801207076203294811847038016014117765120000000000 : Int) false,decode_split denominator ibox187 0 (7413023801207076203294811847038016014117765120000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_188 h,accepted_189 h⟩
private noncomputable def tree186 : TapeTree := .centered (candidateRows ibox186) (candidateRows (FixedTape.midBox ibox186))
attribute [irreducible] tree186
private theorem sign_186 : 2*denominator*(computed denominator (FixedTape.midBox ibox186)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox186).gradient k).lo.natAbs ((computed denominator ibox186).gradient k).hi.natAbs : Int)*((ibox186 k).hi-(ibox186 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox186
    (computed denominator ibox186) (computed denominator (FixedTape.midBox ibox186))
    (by decide +kernel)
private theorem midpoint_even_186 : ∀ k, 2 ∣ (ibox186 k).lo+(ibox186 k).hi := by decide +kernel
private theorem accepted_186 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox186) tree186 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox186 midpoint_even_186
  simp only [tree186,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox186,candidate_valid h (FixedTape.midBox ibox186),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox186 212 (FixedTape.rowsAux denominator ibox186 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox186) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_186
private noncomputable def tree185 : TapeTree := .centered (candidateRows ibox185) (candidateRows (FixedTape.midBox ibox185))
attribute [irreducible] tree185
private theorem sign_185 : 2*denominator*(computed denominator (FixedTape.midBox ibox185)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox185).gradient k).lo.natAbs ((computed denominator ibox185).gradient k).hi.natAbs : Int)*((ibox185 k).hi-(ibox185 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox185
    (computed denominator ibox185) (computed denominator (FixedTape.midBox ibox185))
    (by decide +kernel)
private theorem midpoint_even_185 : ∀ k, 2 ∣ (ibox185 k).lo+(ibox185 k).hi := by decide +kernel
private theorem accepted_185 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox185) tree185 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox185 midpoint_even_185
  simp only [tree185,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox185,candidate_valid h (FixedTape.midBox ibox185),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox185 212 (FixedTape.rowsAux denominator ibox185 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox185) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_185
private noncomputable def tree184 : TapeTree := .split 0 (((7413023801207076203294811847038016014117765120000000000 : Int) : ℚ)/(denominator : ℚ)) tree185 tree186
attribute [irreducible] tree184
private theorem accepted_184 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox184) tree184 = true := by
  simp only [tree184,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox184 0 (7413023801207076203294811847038016014117765120000000000 : Int) false,decode_split denominator ibox184 0 (7413023801207076203294811847038016014117765120000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_185 h,accepted_186 h⟩
private noncomputable def tree183 : TapeTree := .split 3 (((10519060228873331614249528929835753638576783360000000000000 : Int) : ℚ)/(denominator : ℚ)) tree184 tree187
attribute [irreducible] tree183
private theorem accepted_183 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox183) tree183 = true := by
  simp only [tree183,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox183 3 (10519060228873331614249528929835753638576783360000000000000 : Int) false,decode_split denominator ibox183 3 (10519060228873331614249528929835753638576783360000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_184 h,accepted_187 h⟩
private noncomputable def tree182 : TapeTree := .split 0 (((7504542613567657390989809524161942137748848640000000000 : Int) : ℚ)/(denominator : ℚ)) tree183 tree190
attribute [irreducible] tree182
private theorem accepted_182 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox182) tree182 = true := by
  simp only [tree182,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox182 0 (7504542613567657390989809524161942137748848640000000000 : Int) false,decode_split denominator ibox182 0 (7504542613567657390989809524161942137748848640000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_183 h,accepted_190 h⟩
private noncomputable def tree181 : TapeTree := .centered (candidateRows ibox181) (candidateRows (FixedTape.midBox ibox181))
attribute [irreducible] tree181
private theorem sign_181 : 2*denominator*(computed denominator (FixedTape.midBox ibox181)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox181).gradient k).lo.natAbs ((computed denominator ibox181).gradient k).hi.natAbs : Int)*((ibox181 k).hi-(ibox181 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox181
    (computed denominator ibox181) (computed denominator (FixedTape.midBox ibox181))
    (by decide +kernel)
private theorem midpoint_even_181 : ∀ k, 2 ∣ (ibox181 k).lo+(ibox181 k).hi := by decide +kernel
private theorem accepted_181 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox181) tree181 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox181 midpoint_even_181
  simp only [tree181,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox181,candidate_valid h (FixedTape.midBox ibox181),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox181 212 (FixedTape.rowsAux denominator ibox181 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox181) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_181
private noncomputable def tree180 : TapeTree := .centered (candidateRows ibox180) (candidateRows (FixedTape.midBox ibox180))
attribute [irreducible] tree180
private theorem sign_180 : 2*denominator*(computed denominator (FixedTape.midBox ibox180)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox180).gradient k).lo.natAbs ((computed denominator ibox180).gradient k).hi.natAbs : Int)*((ibox180 k).hi-(ibox180 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox180
    (computed denominator ibox180) (computed denominator (FixedTape.midBox ibox180))
    (by decide +kernel)
private theorem midpoint_even_180 : ∀ k, 2 ∣ (ibox180 k).lo+(ibox180 k).hi := by decide +kernel
private theorem accepted_180 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox180) tree180 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox180 midpoint_even_180
  simp only [tree180,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox180,candidate_valid h (FixedTape.midBox ibox180),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox180 212 (FixedTape.rowsAux denominator ibox180 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox180) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_180
private noncomputable def tree179 : TapeTree := .split 0 (((7596061425928238578684807201285868261379932160000000000 : Int) : ℚ)/(denominator : ℚ)) tree180 tree181
attribute [irreducible] tree179
private theorem accepted_179 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox179) tree179 = true := by
  simp only [tree179,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox179 0 (7596061425928238578684807201285868261379932160000000000 : Int) false,decode_split denominator ibox179 0 (7596061425928238578684807201285868261379932160000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_180 h,accepted_181 h⟩
private noncomputable def tree178 : TapeTree := .centered (candidateRows ibox178) (candidateRows (FixedTape.midBox ibox178))
attribute [irreducible] tree178
private theorem sign_178 : 2*denominator*(computed denominator (FixedTape.midBox ibox178)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox178).gradient k).lo.natAbs ((computed denominator ibox178).gradient k).hi.natAbs : Int)*((ibox178 k).hi-(ibox178 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox178
    (computed denominator ibox178) (computed denominator (FixedTape.midBox ibox178))
    (by decide +kernel)
private theorem midpoint_even_178 : ∀ k, 2 ∣ (ibox178 k).lo+(ibox178 k).hi := by decide +kernel
private theorem accepted_178 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox178) tree178 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox178 midpoint_even_178
  simp only [tree178,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox178,candidate_valid h (FixedTape.midBox ibox178),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox178 212 (FixedTape.rowsAux denominator ibox178 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox178) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_178
private noncomputable def tree177 : TapeTree := .centered (candidateRows ibox177) (candidateRows (FixedTape.midBox ibox177))
attribute [irreducible] tree177
private theorem sign_177 : 2*denominator*(computed denominator (FixedTape.midBox ibox177)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox177).gradient k).lo.natAbs ((computed denominator ibox177).gradient k).hi.natAbs : Int)*((ibox177 k).hi-(ibox177 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox177
    (computed denominator ibox177) (computed denominator (FixedTape.midBox ibox177))
    (by decide +kernel)
private theorem midpoint_even_177 : ∀ k, 2 ∣ (ibox177 k).lo+(ibox177 k).hi := by decide +kernel
private theorem accepted_177 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox177) tree177 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox177 midpoint_even_177
  simp only [tree177,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox177,candidate_valid h (FixedTape.midBox ibox177),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox177 212 (FixedTape.rowsAux denominator ibox177 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox177) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_177
private noncomputable def tree176 : TapeTree := .split 0 (((7596061425928238578684807201285868261379932160000000000 : Int) : ℚ)/(denominator : ℚ)) tree177 tree178
attribute [irreducible] tree176
private theorem accepted_176 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox176) tree176 = true := by
  simp only [tree176,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox176 0 (7596061425928238578684807201285868261379932160000000000 : Int) false,decode_split denominator ibox176 0 (7596061425928238578684807201285868261379932160000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_177 h,accepted_178 h⟩
private noncomputable def tree175 : TapeTree := .split 3 (((8606503823623634957113250942592889340653731840000000000000 : Int) : ℚ)/(denominator : ℚ)) tree176 tree179
attribute [irreducible] tree175
private theorem accepted_175 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox175) tree175 = true := by
  simp only [tree175,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox175 3 (8606503823623634957113250942592889340653731840000000000000 : Int) false,decode_split denominator ibox175 3 (8606503823623634957113250942592889340653731840000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_176 h,accepted_179 h⟩
private noncomputable def tree174 : TapeTree := .centered (candidateRows ibox174) (candidateRows (FixedTape.midBox ibox174))
attribute [irreducible] tree174
private theorem sign_174 : 2*denominator*(computed denominator (FixedTape.midBox ibox174)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox174).gradient k).lo.natAbs ((computed denominator ibox174).gradient k).hi.natAbs : Int)*((ibox174 k).hi-(ibox174 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox174
    (computed denominator ibox174) (computed denominator (FixedTape.midBox ibox174))
    (by decide +kernel)
private theorem midpoint_even_174 : ∀ k, 2 ∣ (ibox174 k).lo+(ibox174 k).hi := by decide +kernel
private theorem accepted_174 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox174) tree174 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox174 midpoint_even_174
  simp only [tree174,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox174,candidate_valid h (FixedTape.midBox ibox174),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox174 212 (FixedTape.rowsAux denominator ibox174 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox174) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_174
private noncomputable def tree173 : TapeTree := .centered (candidateRows ibox173) (candidateRows (FixedTape.midBox ibox173))
attribute [irreducible] tree173
private theorem sign_173 : 2*denominator*(computed denominator (FixedTape.midBox ibox173)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox173).gradient k).lo.natAbs ((computed denominator ibox173).gradient k).hi.natAbs : Int)*((ibox173 k).hi-(ibox173 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox173
    (computed denominator ibox173) (computed denominator (FixedTape.midBox ibox173))
    (by decide +kernel)
private theorem midpoint_even_173 : ∀ k, 2 ∣ (ibox173 k).lo+(ibox173 k).hi := by decide +kernel
private theorem accepted_173 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox173) tree173 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox173 midpoint_even_173
  simp only [tree173,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox173,candidate_valid h (FixedTape.midBox ibox173),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox173 212 (FixedTape.rowsAux denominator ibox173 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox173) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_173
private noncomputable def tree172 : TapeTree := .split 0 (((7413023801207076203294811847038016014117765120000000000 : Int) : ℚ)/(denominator : ℚ)) tree173 tree174
attribute [irreducible] tree172
private theorem accepted_172 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox172) tree172 = true := by
  simp only [tree172,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox172 0 (7413023801207076203294811847038016014117765120000000000 : Int) false,decode_split denominator ibox172 0 (7413023801207076203294811847038016014117765120000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_173 h,accepted_174 h⟩
private noncomputable def tree171 : TapeTree := .centered (candidateRows ibox171) (candidateRows (FixedTape.midBox ibox171))
attribute [irreducible] tree171
private theorem sign_171 : 2*denominator*(computed denominator (FixedTape.midBox ibox171)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox171).gradient k).lo.natAbs ((computed denominator ibox171).gradient k).hi.natAbs : Int)*((ibox171 k).hi-(ibox171 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox171
    (computed denominator ibox171) (computed denominator (FixedTape.midBox ibox171))
    (by decide +kernel)
private theorem midpoint_even_171 : ∀ k, 2 ∣ (ibox171 k).lo+(ibox171 k).hi := by decide +kernel
private theorem accepted_171 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox171) tree171 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox171 midpoint_even_171
  simp only [tree171,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox171,candidate_valid h (FixedTape.midBox ibox171),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox171 212 (FixedTape.rowsAux denominator ibox171 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox171) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_171
private noncomputable def tree170 : TapeTree := .centered (candidateRows ibox170) (candidateRows (FixedTape.midBox ibox170))
attribute [irreducible] tree170
private theorem sign_170 : 2*denominator*(computed denominator (FixedTape.midBox ibox170)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox170).gradient k).lo.natAbs ((computed denominator ibox170).gradient k).hi.natAbs : Int)*((ibox170 k).hi-(ibox170 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox170
    (computed denominator ibox170) (computed denominator (FixedTape.midBox ibox170))
    (by decide +kernel)
private theorem midpoint_even_170 : ∀ k, 2 ∣ (ibox170 k).lo+(ibox170 k).hi := by decide +kernel
private theorem accepted_170 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox170) tree170 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox170 midpoint_even_170
  simp only [tree170,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox170,candidate_valid h (FixedTape.midBox ibox170),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox170 212 (FixedTape.rowsAux denominator ibox170 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox170) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_170
private noncomputable def tree169 : TapeTree := .split 0 (((7413023801207076203294811847038016014117765120000000000 : Int) : ℚ)/(denominator : ℚ)) tree170 tree171
attribute [irreducible] tree169
private theorem accepted_169 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox169) tree169 = true := by
  simp only [tree169,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox169 0 (7413023801207076203294811847038016014117765120000000000 : Int) false,decode_split denominator ibox169 0 (7413023801207076203294811847038016014117765120000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_170 h,accepted_171 h⟩
private noncomputable def tree168 : TapeTree := .split 3 (((8606503823623634957113250942592889340653731840000000000000 : Int) : ℚ)/(denominator : ℚ)) tree169 tree172
attribute [irreducible] tree168
private theorem accepted_168 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox168) tree168 = true := by
  simp only [tree168,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox168 3 (8606503823623634957113250942592889340653731840000000000000 : Int) false,decode_split denominator ibox168 3 (8606503823623634957113250942592889340653731840000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_169 h,accepted_172 h⟩
private noncomputable def tree167 : TapeTree := .split 0 (((7504542613567657390989809524161942137748848640000000000 : Int) : ℚ)/(denominator : ℚ)) tree168 tree175
attribute [irreducible] tree167
private theorem accepted_167 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox167) tree167 = true := by
  simp only [tree167,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox167 0 (7504542613567657390989809524161942137748848640000000000 : Int) false,decode_split denominator ibox167 0 (7504542613567657390989809524161942137748848640000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_168 h,accepted_175 h⟩
private noncomputable def tree166 : TapeTree := .split 3 (((9562782026248483285681389936214321489615257600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree167 tree182
attribute [irreducible] tree166
private theorem accepted_166 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox166) tree166 = true := by
  simp only [tree166,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox166 3 (9562782026248483285681389936214321489615257600000000000000 : Int) false,decode_split denominator ibox166 3 (9562782026248483285681389936214321489615257600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_167 h,accepted_182 h⟩
private noncomputable def tree165 : TapeTree := .split 0 (((7687580238288819766379804878409794385011015680000000000 : Int) : ℚ)/(denominator : ℚ)) tree166 tree197
attribute [irreducible] tree165
private theorem accepted_165 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox165) tree165 = true := by
  simp only [tree165,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox165 0 (7687580238288819766379804878409794385011015680000000000 : Int) false,decode_split denominator ibox165 0 (7687580238288819766379804878409794385011015680000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_166 h,accepted_197 h⟩
private noncomputable def tree164 : TapeTree := .split 3 (((11475338431498179942817667923457185787538309120000000000000 : Int) : ℚ)/(denominator : ℚ)) tree165 tree224
attribute [irreducible] tree164
private theorem accepted_164 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox164) tree164 = true := by
  simp only [tree164,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox164 3 (11475338431498179942817667923457185787538309120000000000000 : Int) false,decode_split denominator ibox164 3 (11475338431498179942817667923457185787538309120000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_165 h,accepted_224 h⟩
private noncomputable def tree163 : TapeTree := .centered (candidateRows ibox163) (candidateRows (FixedTape.midBox ibox163))
attribute [irreducible] tree163
private theorem sign_163 : 2*denominator*(computed denominator (FixedTape.midBox ibox163)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox163).gradient k).lo.natAbs ((computed denominator ibox163).gradient k).hi.natAbs : Int)*((ibox163 k).hi-(ibox163 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox163
    (computed denominator ibox163) (computed denominator (FixedTape.midBox ibox163))
    (by decide +kernel)
private theorem midpoint_even_163 : ∀ k, 2 ∣ (ibox163 k).lo+(ibox163 k).hi := by decide +kernel
private theorem accepted_163 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox163) tree163 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox163 midpoint_even_163
  simp only [tree163,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox163,candidate_valid h (FixedTape.midBox ibox163),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox163 212 (FixedTape.rowsAux denominator ibox163 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox163) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_163
private noncomputable def tree162 : TapeTree := .centered (candidateRows ibox162) (candidateRows (FixedTape.midBox ibox162))
attribute [irreducible] tree162
private theorem sign_162 : 2*denominator*(computed denominator (FixedTape.midBox ibox162)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox162).gradient k).lo.natAbs ((computed denominator ibox162).gradient k).hi.natAbs : Int)*((ibox162 k).hi-(ibox162 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox162
    (computed denominator ibox162) (computed denominator (FixedTape.midBox ibox162))
    (by decide +kernel)
private theorem midpoint_even_162 : ∀ k, 2 ∣ (ibox162 k).lo+(ibox162 k).hi := by decide +kernel
private theorem accepted_162 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox162) tree162 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox162 midpoint_even_162
  simp only [tree162,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox162,candidate_valid h (FixedTape.midBox ibox162),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox162 212 (FixedTape.rowsAux denominator ibox162 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox162) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_162
private noncomputable def tree161 : TapeTree := .split 0 (((7962136675370563329464797909781572755904266240000000000 : Int) : ℚ)/(denominator : ℚ)) tree162 tree163
attribute [irreducible] tree161
private theorem accepted_161 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox161) tree161 = true := by
  simp only [tree161,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox161 0 (7962136675370563329464797909781572755904266240000000000 : Int) false,decode_split denominator ibox161 0 (7962136675370563329464797909781572755904266240000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_162 h,accepted_163 h⟩
private noncomputable def tree160 : TapeTree := .centered (candidateRows ibox160) (candidateRows (FixedTape.midBox ibox160))
attribute [irreducible] tree160
private theorem sign_160 : 2*denominator*(computed denominator (FixedTape.midBox ibox160)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox160).gradient k).lo.natAbs ((computed denominator ibox160).gradient k).hi.natAbs : Int)*((ibox160 k).hi-(ibox160 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox160
    (computed denominator ibox160) (computed denominator (FixedTape.midBox ibox160))
    (by decide +kernel)
private theorem midpoint_even_160 : ∀ k, 2 ∣ (ibox160 k).lo+(ibox160 k).hi := by decide +kernel
private theorem accepted_160 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox160) tree160 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox160 midpoint_even_160
  simp only [tree160,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox160,candidate_valid h (FixedTape.midBox ibox160),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox160 212 (FixedTape.rowsAux denominator ibox160 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox160) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_160
private noncomputable def tree159 : TapeTree := .centered (candidateRows ibox159) (candidateRows (FixedTape.midBox ibox159))
attribute [irreducible] tree159
private theorem sign_159 : 2*denominator*(computed denominator (FixedTape.midBox ibox159)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox159).gradient k).lo.natAbs ((computed denominator ibox159).gradient k).hi.natAbs : Int)*((ibox159 k).hi-(ibox159 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox159
    (computed denominator ibox159) (computed denominator (FixedTape.midBox ibox159))
    (by decide +kernel)
private theorem midpoint_even_159 : ∀ k, 2 ∣ (ibox159 k).lo+(ibox159 k).hi := by decide +kernel
private theorem accepted_159 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox159) tree159 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox159 midpoint_even_159
  simp only [tree159,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox159,candidate_valid h (FixedTape.midBox ibox159),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox159 212 (FixedTape.rowsAux denominator ibox159 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox159) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_159
private noncomputable def tree158 : TapeTree := .split 0 (((7962136675370563329464797909781572755904266240000000000 : Int) : ℚ)/(denominator : ℚ)) tree159 tree160
attribute [irreducible] tree158
private theorem accepted_158 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox158) tree158 = true := by
  simp only [tree158,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox158 0 (7962136675370563329464797909781572755904266240000000000 : Int) false,decode_split denominator ibox158 0 (7962136675370563329464797909781572755904266240000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_159 h,accepted_160 h⟩
private noncomputable def tree157 : TapeTree := .split 3 (((6693947418373938299976972955350025042730680320000000000000 : Int) : ℚ)/(denominator : ℚ)) tree158 tree161
attribute [irreducible] tree157
private theorem accepted_157 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox157) tree157 = true := by
  simp only [tree157,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox157 3 (6693947418373938299976972955350025042730680320000000000000 : Int) false,decode_split denominator ibox157 3 (6693947418373938299976972955350025042730680320000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_158 h,accepted_161 h⟩
private noncomputable def tree156 : TapeTree := .centered (candidateRows ibox156) (candidateRows (FixedTape.midBox ibox156))
attribute [irreducible] tree156
private theorem sign_156 : 2*denominator*(computed denominator (FixedTape.midBox ibox156)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox156).gradient k).lo.natAbs ((computed denominator ibox156).gradient k).hi.natAbs : Int)*((ibox156 k).hi-(ibox156 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox156
    (computed denominator ibox156) (computed denominator (FixedTape.midBox ibox156))
    (by decide +kernel)
private theorem midpoint_even_156 : ∀ k, 2 ∣ (ibox156 k).lo+(ibox156 k).hi := by decide +kernel
private theorem accepted_156 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox156) tree156 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox156 midpoint_even_156
  simp only [tree156,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox156,candidate_valid h (FixedTape.midBox ibox156),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox156 212 (FixedTape.rowsAux denominator ibox156 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox156) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_156
private noncomputable def tree155 : TapeTree := .centered (candidateRows ibox155) (candidateRows (FixedTape.midBox ibox155))
attribute [irreducible] tree155
private theorem sign_155 : 2*denominator*(computed denominator (FixedTape.midBox ibox155)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox155).gradient k).lo.natAbs ((computed denominator ibox155).gradient k).hi.natAbs : Int)*((ibox155 k).hi-(ibox155 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox155
    (computed denominator ibox155) (computed denominator (FixedTape.midBox ibox155))
    (by decide +kernel)
private theorem midpoint_even_155 : ∀ k, 2 ∣ (ibox155 k).lo+(ibox155 k).hi := by decide +kernel
private theorem accepted_155 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox155) tree155 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox155 midpoint_even_155
  simp only [tree155,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox155,candidate_valid h (FixedTape.midBox ibox155),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox155 212 (FixedTape.rowsAux denominator ibox155 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox155) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_155
private noncomputable def tree154 : TapeTree := .split 0 (((7779099050649400954074802555533720508642099200000000000 : Int) : ℚ)/(denominator : ℚ)) tree155 tree156
attribute [irreducible] tree154
private theorem accepted_154 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox154) tree154 = true := by
  simp only [tree154,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox154 0 (7779099050649400954074802555533720508642099200000000000 : Int) false,decode_split denominator ibox154 0 (7779099050649400954074802555533720508642099200000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_155 h,accepted_156 h⟩
private noncomputable def tree153 : TapeTree := .centered (candidateRows ibox153) (candidateRows (FixedTape.midBox ibox153))
attribute [irreducible] tree153
private theorem sign_153 : 2*denominator*(computed denominator (FixedTape.midBox ibox153)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox153).gradient k).lo.natAbs ((computed denominator ibox153).gradient k).hi.natAbs : Int)*((ibox153 k).hi-(ibox153 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox153
    (computed denominator ibox153) (computed denominator (FixedTape.midBox ibox153))
    (by decide +kernel)
private theorem midpoint_even_153 : ∀ k, 2 ∣ (ibox153 k).lo+(ibox153 k).hi := by decide +kernel
private theorem accepted_153 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox153) tree153 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox153 midpoint_even_153
  simp only [tree153,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox153,candidate_valid h (FixedTape.midBox ibox153),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox153 212 (FixedTape.rowsAux denominator ibox153 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox153) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_153
private noncomputable def tree152 : TapeTree := .centered (candidateRows ibox152) (candidateRows (FixedTape.midBox ibox152))
attribute [irreducible] tree152
private theorem sign_152 : 2*denominator*(computed denominator (FixedTape.midBox ibox152)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox152).gradient k).lo.natAbs ((computed denominator ibox152).gradient k).hi.natAbs : Int)*((ibox152 k).hi-(ibox152 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox152
    (computed denominator ibox152) (computed denominator (FixedTape.midBox ibox152))
    (by decide +kernel)
private theorem midpoint_even_152 : ∀ k, 2 ∣ (ibox152 k).lo+(ibox152 k).hi := by decide +kernel
private theorem accepted_152 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox152) tree152 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox152 midpoint_even_152
  simp only [tree152,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox152,candidate_valid h (FixedTape.midBox ibox152),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox152 212 (FixedTape.rowsAux denominator ibox152 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox152) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_152
private noncomputable def tree151 : TapeTree := .split 0 (((7779099050649400954074802555533720508642099200000000000 : Int) : ℚ)/(denominator : ℚ)) tree152 tree153
attribute [irreducible] tree151
private theorem accepted_151 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox151) tree151 = true := by
  simp only [tree151,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox151 0 (7779099050649400954074802555533720508642099200000000000 : Int) false,decode_split denominator ibox151 0 (7779099050649400954074802555533720508642099200000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_152 h,accepted_153 h⟩
private noncomputable def tree150 : TapeTree := .split 3 (((6693947418373938299976972955350025042730680320000000000000 : Int) : ℚ)/(denominator : ℚ)) tree151 tree154
attribute [irreducible] tree150
private theorem accepted_150 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox150) tree150 = true := by
  simp only [tree150,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox150 3 (6693947418373938299976972955350025042730680320000000000000 : Int) false,decode_split denominator ibox150 3 (6693947418373938299976972955350025042730680320000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_151 h,accepted_154 h⟩
private noncomputable def tree149 : TapeTree := .split 0 (((7870617863009982141769800232657646632273182720000000000 : Int) : ℚ)/(denominator : ℚ)) tree150 tree157
attribute [irreducible] tree149
private theorem accepted_149 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox149) tree149 = true := by
  simp only [tree149,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox149 0 (7870617863009982141769800232657646632273182720000000000 : Int) false,decode_split denominator ibox149 0 (7870617863009982141769800232657646632273182720000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_150 h,accepted_157 h⟩
private noncomputable def tree148 : TapeTree := .centered (candidateRows ibox148) (candidateRows (FixedTape.midBox ibox148))
attribute [irreducible] tree148
private theorem sign_148 : 2*denominator*(computed denominator (FixedTape.midBox ibox148)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox148).gradient k).lo.natAbs ((computed denominator ibox148).gradient k).hi.natAbs : Int)*((ibox148 k).hi-(ibox148 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox148
    (computed denominator ibox148) (computed denominator (FixedTape.midBox ibox148))
    (by decide +kernel)
private theorem midpoint_even_148 : ∀ k, 2 ∣ (ibox148 k).lo+(ibox148 k).hi := by decide +kernel
private theorem accepted_148 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox148) tree148 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox148 midpoint_even_148
  simp only [tree148,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox148,candidate_valid h (FixedTape.midBox ibox148),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox148 212 (FixedTape.rowsAux denominator ibox148 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox148) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_148
private noncomputable def tree147 : TapeTree := .centered (candidateRows ibox147) (candidateRows (FixedTape.midBox ibox147))
attribute [irreducible] tree147
private theorem sign_147 : 2*denominator*(computed denominator (FixedTape.midBox ibox147)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox147).gradient k).lo.natAbs ((computed denominator ibox147).gradient k).hi.natAbs : Int)*((ibox147 k).hi-(ibox147 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox147
    (computed denominator ibox147) (computed denominator (FixedTape.midBox ibox147))
    (by decide +kernel)
private theorem midpoint_even_147 : ∀ k, 2 ∣ (ibox147 k).lo+(ibox147 k).hi := by decide +kernel
private theorem accepted_147 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox147) tree147 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox147 midpoint_even_147
  simp only [tree147,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox147,candidate_valid h (FixedTape.midBox ibox147),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox147 212 (FixedTape.rowsAux denominator ibox147 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox147) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_147
private noncomputable def tree146 : TapeTree := .split 0 (((7962136675370563329464797909781572755904266240000000000 : Int) : ℚ)/(denominator : ℚ)) tree147 tree148
attribute [irreducible] tree146
private theorem accepted_146 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox146) tree146 = true := by
  simp only [tree146,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox146 0 (7962136675370563329464797909781572755904266240000000000 : Int) false,decode_split denominator ibox146 0 (7962136675370563329464797909781572755904266240000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_147 h,accepted_148 h⟩
private noncomputable def tree145 : TapeTree := .centered (candidateRows ibox145) (candidateRows (FixedTape.midBox ibox145))
attribute [irreducible] tree145
private theorem sign_145 : 2*denominator*(computed denominator (FixedTape.midBox ibox145)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox145).gradient k).lo.natAbs ((computed denominator ibox145).gradient k).hi.natAbs : Int)*((ibox145 k).hi-(ibox145 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox145
    (computed denominator ibox145) (computed denominator (FixedTape.midBox ibox145))
    (by decide +kernel)
private theorem midpoint_even_145 : ∀ k, 2 ∣ (ibox145 k).lo+(ibox145 k).hi := by decide +kernel
private theorem accepted_145 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox145) tree145 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox145 midpoint_even_145
  simp only [tree145,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox145,candidate_valid h (FixedTape.midBox ibox145),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox145 212 (FixedTape.rowsAux denominator ibox145 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox145) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_145
private noncomputable def tree144 : TapeTree := .centered (candidateRows ibox144) (candidateRows (FixedTape.midBox ibox144))
attribute [irreducible] tree144
private theorem sign_144 : 2*denominator*(computed denominator (FixedTape.midBox ibox144)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox144).gradient k).lo.natAbs ((computed denominator ibox144).gradient k).hi.natAbs : Int)*((ibox144 k).hi-(ibox144 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox144
    (computed denominator ibox144) (computed denominator (FixedTape.midBox ibox144))
    (by decide +kernel)
private theorem midpoint_even_144 : ∀ k, 2 ∣ (ibox144 k).lo+(ibox144 k).hi := by decide +kernel
private theorem accepted_144 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox144) tree144 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox144 midpoint_even_144
  simp only [tree144,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox144,candidate_valid h (FixedTape.midBox ibox144),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox144 212 (FixedTape.rowsAux denominator ibox144 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox144) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_144
private noncomputable def tree143 : TapeTree := .split 0 (((7962136675370563329464797909781572755904266240000000000 : Int) : ℚ)/(denominator : ℚ)) tree144 tree145
attribute [irreducible] tree143
private theorem accepted_143 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox143) tree143 = true := by
  simp only [tree143,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox143 0 (7962136675370563329464797909781572755904266240000000000 : Int) false,decode_split denominator ibox143 0 (7962136675370563329464797909781572755904266240000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_144 h,accepted_145 h⟩
private noncomputable def tree142 : TapeTree := .split 3 (((4781391013124241642840694968107160744807628800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree143 tree146
attribute [irreducible] tree142
private theorem accepted_142 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox142) tree142 = true := by
  simp only [tree142,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox142 3 (4781391013124241642840694968107160744807628800000000000000 : Int) false,decode_split denominator ibox142 3 (4781391013124241642840694968107160744807628800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_143 h,accepted_146 h⟩
private noncomputable def tree141 : TapeTree := .centered (candidateRows ibox141) (candidateRows (FixedTape.midBox ibox141))
attribute [irreducible] tree141
private theorem sign_141 : 2*denominator*(computed denominator (FixedTape.midBox ibox141)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox141).gradient k).lo.natAbs ((computed denominator ibox141).gradient k).hi.natAbs : Int)*((ibox141 k).hi-(ibox141 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox141
    (computed denominator ibox141) (computed denominator (FixedTape.midBox ibox141))
    (by decide +kernel)
private theorem midpoint_even_141 : ∀ k, 2 ∣ (ibox141 k).lo+(ibox141 k).hi := by decide +kernel
private theorem accepted_141 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox141) tree141 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox141 midpoint_even_141
  simp only [tree141,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox141,candidate_valid h (FixedTape.midBox ibox141),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox141 212 (FixedTape.rowsAux denominator ibox141 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox141) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_141
private noncomputable def tree140 : TapeTree := .centered (candidateRows ibox140) (candidateRows (FixedTape.midBox ibox140))
attribute [irreducible] tree140
private theorem sign_140 : 2*denominator*(computed denominator (FixedTape.midBox ibox140)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox140).gradient k).lo.natAbs ((computed denominator ibox140).gradient k).hi.natAbs : Int)*((ibox140 k).hi-(ibox140 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox140
    (computed denominator ibox140) (computed denominator (FixedTape.midBox ibox140))
    (by decide +kernel)
private theorem midpoint_even_140 : ∀ k, 2 ∣ (ibox140 k).lo+(ibox140 k).hi := by decide +kernel
private theorem accepted_140 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox140) tree140 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox140 midpoint_even_140
  simp only [tree140,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox140,candidate_valid h (FixedTape.midBox ibox140),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox140 212 (FixedTape.rowsAux denominator ibox140 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox140) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_140
private noncomputable def tree139 : TapeTree := .split 0 (((7779099050649400954074802555533720508642099200000000000 : Int) : ℚ)/(denominator : ℚ)) tree140 tree141
attribute [irreducible] tree139
private theorem accepted_139 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox139) tree139 = true := by
  simp only [tree139,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox139 0 (7779099050649400954074802555533720508642099200000000000 : Int) false,decode_split denominator ibox139 0 (7779099050649400954074802555533720508642099200000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_140 h,accepted_141 h⟩
private noncomputable def tree138 : TapeTree := .centered (candidateRows ibox138) (candidateRows (FixedTape.midBox ibox138))
attribute [irreducible] tree138
private theorem sign_138 : 2*denominator*(computed denominator (FixedTape.midBox ibox138)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox138).gradient k).lo.natAbs ((computed denominator ibox138).gradient k).hi.natAbs : Int)*((ibox138 k).hi-(ibox138 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox138
    (computed denominator ibox138) (computed denominator (FixedTape.midBox ibox138))
    (by decide +kernel)
private theorem midpoint_even_138 : ∀ k, 2 ∣ (ibox138 k).lo+(ibox138 k).hi := by decide +kernel
private theorem accepted_138 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox138) tree138 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox138 midpoint_even_138
  simp only [tree138,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox138,candidate_valid h (FixedTape.midBox ibox138),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox138 212 (FixedTape.rowsAux denominator ibox138 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox138) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_138
private noncomputable def tree137 : TapeTree := .centered (candidateRows ibox137) (candidateRows (FixedTape.midBox ibox137))
attribute [irreducible] tree137
private theorem sign_137 : 2*denominator*(computed denominator (FixedTape.midBox ibox137)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox137).gradient k).lo.natAbs ((computed denominator ibox137).gradient k).hi.natAbs : Int)*((ibox137 k).hi-(ibox137 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox137
    (computed denominator ibox137) (computed denominator (FixedTape.midBox ibox137))
    (by decide +kernel)
private theorem midpoint_even_137 : ∀ k, 2 ∣ (ibox137 k).lo+(ibox137 k).hi := by decide +kernel
private theorem accepted_137 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox137) tree137 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox137 midpoint_even_137
  simp only [tree137,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox137,candidate_valid h (FixedTape.midBox ibox137),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox137 212 (FixedTape.rowsAux denominator ibox137 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox137) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_137
private noncomputable def tree136 : TapeTree := .split 0 (((7779099050649400954074802555533720508642099200000000000 : Int) : ℚ)/(denominator : ℚ)) tree137 tree138
attribute [irreducible] tree136
private theorem accepted_136 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox136) tree136 = true := by
  simp only [tree136,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox136 0 (7779099050649400954074802555533720508642099200000000000 : Int) false,decode_split denominator ibox136 0 (7779099050649400954074802555533720508642099200000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_137 h,accepted_138 h⟩
private noncomputable def tree135 : TapeTree := .split 3 (((4781391013124241642840694968107160744807628800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree136 tree139
attribute [irreducible] tree135
private theorem accepted_135 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox135) tree135 = true := by
  simp only [tree135,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox135 3 (4781391013124241642840694968107160744807628800000000000000 : Int) false,decode_split denominator ibox135 3 (4781391013124241642840694968107160744807628800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_136 h,accepted_139 h⟩
private noncomputable def tree134 : TapeTree := .split 0 (((7870617863009982141769800232657646632273182720000000000 : Int) : ℚ)/(denominator : ℚ)) tree135 tree142
attribute [irreducible] tree134
private theorem accepted_134 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox134) tree134 = true := by
  simp only [tree134,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox134 0 (7870617863009982141769800232657646632273182720000000000 : Int) false,decode_split denominator ibox134 0 (7870617863009982141769800232657646632273182720000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_135 h,accepted_142 h⟩
private noncomputable def tree133 : TapeTree := .split 3 (((5737669215749089971408833961728592893769154560000000000000 : Int) : ℚ)/(denominator : ℚ)) tree134 tree149
attribute [irreducible] tree133
private theorem accepted_133 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox133) tree133 = true := by
  simp only [tree133,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox133 3 (5737669215749089971408833961728592893769154560000000000000 : Int) false,decode_split denominator ibox133 3 (5737669215749089971408833961728592893769154560000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_134 h,accepted_149 h⟩
private noncomputable def tree132 : TapeTree := .centered (candidateRows ibox132) (candidateRows (FixedTape.midBox ibox132))
attribute [irreducible] tree132
private theorem sign_132 : 2*denominator*(computed denominator (FixedTape.midBox ibox132)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox132).gradient k).lo.natAbs ((computed denominator ibox132).gradient k).hi.natAbs : Int)*((ibox132 k).hi-(ibox132 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox132
    (computed denominator ibox132) (computed denominator (FixedTape.midBox ibox132))
    (by decide +kernel)
private theorem midpoint_even_132 : ∀ k, 2 ∣ (ibox132 k).lo+(ibox132 k).hi := by decide +kernel
private theorem accepted_132 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox132) tree132 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox132 midpoint_even_132
  simp only [tree132,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox132,candidate_valid h (FixedTape.midBox ibox132),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox132 212 (FixedTape.rowsAux denominator ibox132 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox132) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_132
private noncomputable def tree131 : TapeTree := .centered (candidateRows ibox131) (candidateRows (FixedTape.midBox ibox131))
attribute [irreducible] tree131
private theorem sign_131 : 2*denominator*(computed denominator (FixedTape.midBox ibox131)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox131).gradient k).lo.natAbs ((computed denominator ibox131).gradient k).hi.natAbs : Int)*((ibox131 k).hi-(ibox131 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox131
    (computed denominator ibox131) (computed denominator (FixedTape.midBox ibox131))
    (by decide +kernel)
private theorem midpoint_even_131 : ∀ k, 2 ∣ (ibox131 k).lo+(ibox131 k).hi := by decide +kernel
private theorem accepted_131 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox131) tree131 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox131 midpoint_even_131
  simp only [tree131,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox131,candidate_valid h (FixedTape.midBox ibox131),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox131 212 (FixedTape.rowsAux denominator ibox131 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox131) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_131
private noncomputable def tree130 : TapeTree := .split 0 (((7596061425928238578684807201285868261379932160000000000 : Int) : ℚ)/(denominator : ℚ)) tree131 tree132
attribute [irreducible] tree130
private theorem accepted_130 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox130) tree130 = true := by
  simp only [tree130,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox130 0 (7596061425928238578684807201285868261379932160000000000 : Int) false,decode_split denominator ibox130 0 (7596061425928238578684807201285868261379932160000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_131 h,accepted_132 h⟩
private noncomputable def tree129 : TapeTree := .centered (candidateRows ibox129) (candidateRows (FixedTape.midBox ibox129))
attribute [irreducible] tree129
private theorem sign_129 : 2*denominator*(computed denominator (FixedTape.midBox ibox129)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox129).gradient k).lo.natAbs ((computed denominator ibox129).gradient k).hi.natAbs : Int)*((ibox129 k).hi-(ibox129 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox129
    (computed denominator ibox129) (computed denominator (FixedTape.midBox ibox129))
    (by decide +kernel)
private theorem midpoint_even_129 : ∀ k, 2 ∣ (ibox129 k).lo+(ibox129 k).hi := by decide +kernel
private theorem accepted_129 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox129) tree129 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox129 midpoint_even_129
  simp only [tree129,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox129,candidate_valid h (FixedTape.midBox ibox129),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox129 212 (FixedTape.rowsAux denominator ibox129 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox129) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_129
private noncomputable def tree128 : TapeTree := .centered (candidateRows ibox128) (candidateRows (FixedTape.midBox ibox128))
attribute [irreducible] tree128
private theorem sign_128 : 2*denominator*(computed denominator (FixedTape.midBox ibox128)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox128).gradient k).lo.natAbs ((computed denominator ibox128).gradient k).hi.natAbs : Int)*((ibox128 k).hi-(ibox128 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox128
    (computed denominator ibox128) (computed denominator (FixedTape.midBox ibox128))
    (by decide +kernel)
private theorem midpoint_even_128 : ∀ k, 2 ∣ (ibox128 k).lo+(ibox128 k).hi := by decide +kernel
private theorem accepted_128 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox128) tree128 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox128 midpoint_even_128
  simp only [tree128,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox128,candidate_valid h (FixedTape.midBox ibox128),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox128 212 (FixedTape.rowsAux denominator ibox128 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox128) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_128
private noncomputable def tree127 : TapeTree := .split 0 (((7596061425928238578684807201285868261379932160000000000 : Int) : ℚ)/(denominator : ℚ)) tree128 tree129
attribute [irreducible] tree127
private theorem accepted_127 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox127) tree127 = true := by
  simp only [tree127,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox127 0 (7596061425928238578684807201285868261379932160000000000 : Int) false,decode_split denominator ibox127 0 (7596061425928238578684807201285868261379932160000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_128 h,accepted_129 h⟩
private noncomputable def tree126 : TapeTree := .split 3 (((6693947418373938299976972955350025042730680320000000000000 : Int) : ℚ)/(denominator : ℚ)) tree127 tree130
attribute [irreducible] tree126
private theorem accepted_126 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox126) tree126 = true := by
  simp only [tree126,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox126 3 (6693947418373938299976972955350025042730680320000000000000 : Int) false,decode_split denominator ibox126 3 (6693947418373938299976972955350025042730680320000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_127 h,accepted_130 h⟩
private noncomputable def tree125 : TapeTree := .centered (candidateRows ibox125) (candidateRows (FixedTape.midBox ibox125))
attribute [irreducible] tree125
private theorem sign_125 : 2*denominator*(computed denominator (FixedTape.midBox ibox125)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox125).gradient k).lo.natAbs ((computed denominator ibox125).gradient k).hi.natAbs : Int)*((ibox125 k).hi-(ibox125 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox125
    (computed denominator ibox125) (computed denominator (FixedTape.midBox ibox125))
    (by decide +kernel)
private theorem midpoint_even_125 : ∀ k, 2 ∣ (ibox125 k).lo+(ibox125 k).hi := by decide +kernel
private theorem accepted_125 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox125) tree125 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox125 midpoint_even_125
  simp only [tree125,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox125,candidate_valid h (FixedTape.midBox ibox125),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox125 212 (FixedTape.rowsAux denominator ibox125 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox125) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_125
private noncomputable def tree124 : TapeTree := .centered (candidateRows ibox124) (candidateRows (FixedTape.midBox ibox124))
attribute [irreducible] tree124
private theorem sign_124 : 2*denominator*(computed denominator (FixedTape.midBox ibox124)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox124).gradient k).lo.natAbs ((computed denominator ibox124).gradient k).hi.natAbs : Int)*((ibox124 k).hi-(ibox124 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox124
    (computed denominator ibox124) (computed denominator (FixedTape.midBox ibox124))
    (by decide +kernel)
private theorem midpoint_even_124 : ∀ k, 2 ∣ (ibox124 k).lo+(ibox124 k).hi := by decide +kernel
private theorem accepted_124 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox124) tree124 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox124 midpoint_even_124
  simp only [tree124,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox124,candidate_valid h (FixedTape.midBox ibox124),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox124 212 (FixedTape.rowsAux denominator ibox124 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox124) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_124
private noncomputable def tree123 : TapeTree := .split 0 (((7413023801207076203294811847038016014117765120000000000 : Int) : ℚ)/(denominator : ℚ)) tree124 tree125
attribute [irreducible] tree123
private theorem accepted_123 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox123) tree123 = true := by
  simp only [tree123,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox123 0 (7413023801207076203294811847038016014117765120000000000 : Int) false,decode_split denominator ibox123 0 (7413023801207076203294811847038016014117765120000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_124 h,accepted_125 h⟩
private noncomputable def tree122 : TapeTree := .centered (candidateRows ibox122) (candidateRows (FixedTape.midBox ibox122))
attribute [irreducible] tree122
private theorem sign_122 : 2*denominator*(computed denominator (FixedTape.midBox ibox122)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox122).gradient k).lo.natAbs ((computed denominator ibox122).gradient k).hi.natAbs : Int)*((ibox122 k).hi-(ibox122 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox122
    (computed denominator ibox122) (computed denominator (FixedTape.midBox ibox122))
    (by decide +kernel)
private theorem midpoint_even_122 : ∀ k, 2 ∣ (ibox122 k).lo+(ibox122 k).hi := by decide +kernel
private theorem accepted_122 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox122) tree122 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox122 midpoint_even_122
  simp only [tree122,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox122,candidate_valid h (FixedTape.midBox ibox122),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox122 212 (FixedTape.rowsAux denominator ibox122 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox122) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_122
private noncomputable def tree121 : TapeTree := .centered (candidateRows ibox121) (candidateRows (FixedTape.midBox ibox121))
attribute [irreducible] tree121
private theorem sign_121 : 2*denominator*(computed denominator (FixedTape.midBox ibox121)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox121).gradient k).lo.natAbs ((computed denominator ibox121).gradient k).hi.natAbs : Int)*((ibox121 k).hi-(ibox121 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox121
    (computed denominator ibox121) (computed denominator (FixedTape.midBox ibox121))
    (by decide +kernel)
private theorem midpoint_even_121 : ∀ k, 2 ∣ (ibox121 k).lo+(ibox121 k).hi := by decide +kernel
private theorem accepted_121 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox121) tree121 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox121 midpoint_even_121
  simp only [tree121,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox121,candidate_valid h (FixedTape.midBox ibox121),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox121 212 (FixedTape.rowsAux denominator ibox121 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox121) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_121
private noncomputable def tree120 : TapeTree := .split 0 (((7413023801207076203294811847038016014117765120000000000 : Int) : ℚ)/(denominator : ℚ)) tree121 tree122
attribute [irreducible] tree120
private theorem accepted_120 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox120) tree120 = true := by
  simp only [tree120,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox120 0 (7413023801207076203294811847038016014117765120000000000 : Int) false,decode_split denominator ibox120 0 (7413023801207076203294811847038016014117765120000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_121 h,accepted_122 h⟩
private noncomputable def tree119 : TapeTree := .split 3 (((6693947418373938299976972955350025042730680320000000000000 : Int) : ℚ)/(denominator : ℚ)) tree120 tree123
attribute [irreducible] tree119
private theorem accepted_119 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox119) tree119 = true := by
  simp only [tree119,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox119 3 (6693947418373938299976972955350025042730680320000000000000 : Int) false,decode_split denominator ibox119 3 (6693947418373938299976972955350025042730680320000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_120 h,accepted_123 h⟩
private noncomputable def tree118 : TapeTree := .split 0 (((7504542613567657390989809524161942137748848640000000000 : Int) : ℚ)/(denominator : ℚ)) tree119 tree126
attribute [irreducible] tree118
private theorem accepted_118 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox118) tree118 = true := by
  simp only [tree118,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox118 0 (7504542613567657390989809524161942137748848640000000000 : Int) false,decode_split denominator ibox118 0 (7504542613567657390989809524161942137748848640000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_119 h,accepted_126 h⟩
private noncomputable def tree117 : TapeTree := .centered (candidateRows ibox117) (candidateRows (FixedTape.midBox ibox117))
attribute [irreducible] tree117
private theorem sign_117 : 2*denominator*(computed denominator (FixedTape.midBox ibox117)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox117).gradient k).lo.natAbs ((computed denominator ibox117).gradient k).hi.natAbs : Int)*((ibox117 k).hi-(ibox117 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox117
    (computed denominator ibox117) (computed denominator (FixedTape.midBox ibox117))
    (by decide +kernel)
private theorem midpoint_even_117 : ∀ k, 2 ∣ (ibox117 k).lo+(ibox117 k).hi := by decide +kernel
private theorem accepted_117 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox117) tree117 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox117 midpoint_even_117
  simp only [tree117,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox117,candidate_valid h (FixedTape.midBox ibox117),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox117 212 (FixedTape.rowsAux denominator ibox117 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox117) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_117
private noncomputable def tree116 : TapeTree := .centered (candidateRows ibox116) (candidateRows (FixedTape.midBox ibox116))
attribute [irreducible] tree116
private theorem sign_116 : 2*denominator*(computed denominator (FixedTape.midBox ibox116)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox116).gradient k).lo.natAbs ((computed denominator ibox116).gradient k).hi.natAbs : Int)*((ibox116 k).hi-(ibox116 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox116
    (computed denominator ibox116) (computed denominator (FixedTape.midBox ibox116))
    (by decide +kernel)
private theorem midpoint_even_116 : ∀ k, 2 ∣ (ibox116 k).lo+(ibox116 k).hi := by decide +kernel
private theorem accepted_116 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox116) tree116 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox116 midpoint_even_116
  simp only [tree116,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox116,candidate_valid h (FixedTape.midBox ibox116),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox116 212 (FixedTape.rowsAux denominator ibox116 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox116) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_116
private noncomputable def tree115 : TapeTree := .split 0 (((7596061425928238578684807201285868261379932160000000000 : Int) : ℚ)/(denominator : ℚ)) tree116 tree117
attribute [irreducible] tree115
private theorem accepted_115 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox115) tree115 = true := by
  simp only [tree115,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox115 0 (7596061425928238578684807201285868261379932160000000000 : Int) false,decode_split denominator ibox115 0 (7596061425928238578684807201285868261379932160000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_116 h,accepted_117 h⟩
private noncomputable def tree114 : TapeTree := .centered (candidateRows ibox114) (candidateRows (FixedTape.midBox ibox114))
attribute [irreducible] tree114
private theorem sign_114 : 2*denominator*(computed denominator (FixedTape.midBox ibox114)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox114).gradient k).lo.natAbs ((computed denominator ibox114).gradient k).hi.natAbs : Int)*((ibox114 k).hi-(ibox114 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox114
    (computed denominator ibox114) (computed denominator (FixedTape.midBox ibox114))
    (by decide +kernel)
private theorem midpoint_even_114 : ∀ k, 2 ∣ (ibox114 k).lo+(ibox114 k).hi := by decide +kernel
private theorem accepted_114 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox114) tree114 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox114 midpoint_even_114
  simp only [tree114,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox114,candidate_valid h (FixedTape.midBox ibox114),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox114 212 (FixedTape.rowsAux denominator ibox114 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox114) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_114
private noncomputable def tree113 : TapeTree := .centered (candidateRows ibox113) (candidateRows (FixedTape.midBox ibox113))
attribute [irreducible] tree113
private theorem sign_113 : 2*denominator*(computed denominator (FixedTape.midBox ibox113)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox113).gradient k).lo.natAbs ((computed denominator ibox113).gradient k).hi.natAbs : Int)*((ibox113 k).hi-(ibox113 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox113
    (computed denominator ibox113) (computed denominator (FixedTape.midBox ibox113))
    (by decide +kernel)
private theorem midpoint_even_113 : ∀ k, 2 ∣ (ibox113 k).lo+(ibox113 k).hi := by decide +kernel
private theorem accepted_113 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox113) tree113 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox113 midpoint_even_113
  simp only [tree113,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox113,candidate_valid h (FixedTape.midBox ibox113),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox113 212 (FixedTape.rowsAux denominator ibox113 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox113) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_113
private noncomputable def tree112 : TapeTree := .split 0 (((7596061425928238578684807201285868261379932160000000000 : Int) : ℚ)/(denominator : ℚ)) tree113 tree114
attribute [irreducible] tree112
private theorem accepted_112 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox112) tree112 = true := by
  simp only [tree112,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox112 0 (7596061425928238578684807201285868261379932160000000000 : Int) false,decode_split denominator ibox112 0 (7596061425928238578684807201285868261379932160000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_113 h,accepted_114 h⟩
private noncomputable def tree111 : TapeTree := .split 3 (((4781391013124241642840694968107160744807628800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree112 tree115
attribute [irreducible] tree111
private theorem accepted_111 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox111) tree111 = true := by
  simp only [tree111,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox111 3 (4781391013124241642840694968107160744807628800000000000000 : Int) false,decode_split denominator ibox111 3 (4781391013124241642840694968107160744807628800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_112 h,accepted_115 h⟩
private noncomputable def tree110 : TapeTree := .centered (candidateRows ibox110) (candidateRows (FixedTape.midBox ibox110))
attribute [irreducible] tree110
private theorem sign_110 : 2*denominator*(computed denominator (FixedTape.midBox ibox110)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox110).gradient k).lo.natAbs ((computed denominator ibox110).gradient k).hi.natAbs : Int)*((ibox110 k).hi-(ibox110 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox110
    (computed denominator ibox110) (computed denominator (FixedTape.midBox ibox110))
    (by decide +kernel)
private theorem midpoint_even_110 : ∀ k, 2 ∣ (ibox110 k).lo+(ibox110 k).hi := by decide +kernel
private theorem accepted_110 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox110) tree110 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox110 midpoint_even_110
  simp only [tree110,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox110,candidate_valid h (FixedTape.midBox ibox110),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox110 212 (FixedTape.rowsAux denominator ibox110 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox110) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_110
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
private noncomputable def tree108 : TapeTree := .split 0 (((7413023801207076203294811847038016014117765120000000000 : Int) : ℚ)/(denominator : ℚ)) tree109 tree110
attribute [irreducible] tree108
private theorem accepted_108 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox108) tree108 = true := by
  simp only [tree108,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox108 0 (7413023801207076203294811847038016014117765120000000000 : Int) false,decode_split denominator ibox108 0 (7413023801207076203294811847038016014117765120000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_109 h,accepted_110 h⟩
private noncomputable def tree107 : TapeTree := .centered (candidateRows ibox107) (candidateRows (FixedTape.midBox ibox107))
attribute [irreducible] tree107
private theorem sign_107 : 2*denominator*(computed denominator (FixedTape.midBox ibox107)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox107).gradient k).lo.natAbs ((computed denominator ibox107).gradient k).hi.natAbs : Int)*((ibox107 k).hi-(ibox107 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox107
    (computed denominator ibox107) (computed denominator (FixedTape.midBox ibox107))
    (by decide +kernel)
private theorem midpoint_even_107 : ∀ k, 2 ∣ (ibox107 k).lo+(ibox107 k).hi := by decide +kernel
private theorem accepted_107 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox107) tree107 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox107 midpoint_even_107
  simp only [tree107,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox107,candidate_valid h (FixedTape.midBox ibox107),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox107 212 (FixedTape.rowsAux denominator ibox107 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox107) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_107
private noncomputable def tree106 : TapeTree := .centered (candidateRows ibox106) (candidateRows (FixedTape.midBox ibox106))
attribute [irreducible] tree106
private theorem sign_106 : 2*denominator*(computed denominator (FixedTape.midBox ibox106)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox106).gradient k).lo.natAbs ((computed denominator ibox106).gradient k).hi.natAbs : Int)*((ibox106 k).hi-(ibox106 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox106
    (computed denominator ibox106) (computed denominator (FixedTape.midBox ibox106))
    (by decide +kernel)
private theorem midpoint_even_106 : ∀ k, 2 ∣ (ibox106 k).lo+(ibox106 k).hi := by decide +kernel
private theorem accepted_106 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox106) tree106 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox106 midpoint_even_106
  simp only [tree106,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox106,candidate_valid h (FixedTape.midBox ibox106),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox106 212 (FixedTape.rowsAux denominator ibox106 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox106) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_106
private noncomputable def tree105 : TapeTree := .split 0 (((7413023801207076203294811847038016014117765120000000000 : Int) : ℚ)/(denominator : ℚ)) tree106 tree107
attribute [irreducible] tree105
private theorem accepted_105 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox105) tree105 = true := by
  simp only [tree105,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox105 0 (7413023801207076203294811847038016014117765120000000000 : Int) false,decode_split denominator ibox105 0 (7413023801207076203294811847038016014117765120000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_106 h,accepted_107 h⟩
private noncomputable def tree104 : TapeTree := .split 3 (((4781391013124241642840694968107160744807628800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree105 tree108
attribute [irreducible] tree104
private theorem accepted_104 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox104) tree104 = true := by
  simp only [tree104,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox104 3 (4781391013124241642840694968107160744807628800000000000000 : Int) false,decode_split denominator ibox104 3 (4781391013124241642840694968107160744807628800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_105 h,accepted_108 h⟩
private noncomputable def tree103 : TapeTree := .split 0 (((7504542613567657390989809524161942137748848640000000000 : Int) : ℚ)/(denominator : ℚ)) tree104 tree111
attribute [irreducible] tree103
private theorem accepted_103 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox103) tree103 = true := by
  simp only [tree103,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox103 0 (7504542613567657390989809524161942137748848640000000000 : Int) false,decode_split denominator ibox103 0 (7504542613567657390989809524161942137748848640000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_104 h,accepted_111 h⟩
private noncomputable def tree102 : TapeTree := .split 3 (((5737669215749089971408833961728592893769154560000000000000 : Int) : ℚ)/(denominator : ℚ)) tree103 tree118
attribute [irreducible] tree102
private theorem accepted_102 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox102) tree102 = true := by
  simp only [tree102,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox102 3 (5737669215749089971408833961728592893769154560000000000000 : Int) false,decode_split denominator ibox102 3 (5737669215749089971408833961728592893769154560000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_103 h,accepted_118 h⟩
private noncomputable def tree101 : TapeTree := .split 0 (((7687580238288819766379804878409794385011015680000000000 : Int) : ℚ)/(denominator : ℚ)) tree102 tree133
attribute [irreducible] tree101
private theorem accepted_101 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox101) tree101 = true := by
  simp only [tree101,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox101 0 (7687580238288819766379804878409794385011015680000000000 : Int) false,decode_split denominator ibox101 0 (7687580238288819766379804878409794385011015680000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_102 h,accepted_133 h⟩
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
private noncomputable def tree99 : TapeTree := .centered (candidateRows ibox99) (candidateRows (FixedTape.midBox ibox99))
attribute [irreducible] tree99
private theorem sign_99 : 2*denominator*(computed denominator (FixedTape.midBox ibox99)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox99).gradient k).lo.natAbs ((computed denominator ibox99).gradient k).hi.natAbs : Int)*((ibox99 k).hi-(ibox99 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox99
    (computed denominator ibox99) (computed denominator (FixedTape.midBox ibox99))
    (by decide +kernel)
private theorem midpoint_even_99 : ∀ k, 2 ∣ (ibox99 k).lo+(ibox99 k).hi := by decide +kernel
private theorem accepted_99 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox99) tree99 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox99 midpoint_even_99
  simp only [tree99,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox99,candidate_valid h (FixedTape.midBox ibox99),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox99 212 (FixedTape.rowsAux denominator ibox99 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox99) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_99
private noncomputable def tree98 : TapeTree := .split 0 (((7962136675370563329464797909781572755904266240000000000 : Int) : ℚ)/(denominator : ℚ)) tree99 tree100
attribute [irreducible] tree98
private theorem accepted_98 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox98) tree98 = true := by
  simp only [tree98,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox98 0 (7962136675370563329464797909781572755904266240000000000 : Int) false,decode_split denominator ibox98 0 (7962136675370563329464797909781572755904266240000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_99 h,accepted_100 h⟩
private noncomputable def tree97 : TapeTree := .centered (candidateRows ibox97) (candidateRows (FixedTape.midBox ibox97))
attribute [irreducible] tree97
private theorem sign_97 : 2*denominator*(computed denominator (FixedTape.midBox ibox97)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox97).gradient k).lo.natAbs ((computed denominator ibox97).gradient k).hi.natAbs : Int)*((ibox97 k).hi-(ibox97 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox97
    (computed denominator ibox97) (computed denominator (FixedTape.midBox ibox97))
    (by decide +kernel)
private theorem midpoint_even_97 : ∀ k, 2 ∣ (ibox97 k).lo+(ibox97 k).hi := by decide +kernel
private theorem accepted_97 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox97) tree97 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox97 midpoint_even_97
  simp only [tree97,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox97,candidate_valid h (FixedTape.midBox ibox97),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox97 212 (FixedTape.rowsAux denominator ibox97 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox97) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_97
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
private noncomputable def tree95 : TapeTree := .split 0 (((7962136675370563329464797909781572755904266240000000000 : Int) : ℚ)/(denominator : ℚ)) tree96 tree97
attribute [irreducible] tree95
private theorem accepted_95 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox95) tree95 = true := by
  simp only [tree95,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox95 0 (7962136675370563329464797909781572755904266240000000000 : Int) false,decode_split denominator ibox95 0 (7962136675370563329464797909781572755904266240000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_96 h,accepted_97 h⟩
private noncomputable def tree94 : TapeTree := .split 3 (((2868834607874544985704416980864296446884577280000000000000 : Int) : ℚ)/(denominator : ℚ)) tree95 tree98
attribute [irreducible] tree94
private theorem accepted_94 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox94) tree94 = true := by
  simp only [tree94,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox94 3 (2868834607874544985704416980864296446884577280000000000000 : Int) false,decode_split denominator ibox94 3 (2868834607874544985704416980864296446884577280000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_95 h,accepted_98 h⟩
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
private noncomputable def tree92 : TapeTree := .centered (candidateRows ibox92) (candidateRows (FixedTape.midBox ibox92))
attribute [irreducible] tree92
private theorem sign_92 : 2*denominator*(computed denominator (FixedTape.midBox ibox92)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox92).gradient k).lo.natAbs ((computed denominator ibox92).gradient k).hi.natAbs : Int)*((ibox92 k).hi-(ibox92 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox92
    (computed denominator ibox92) (computed denominator (FixedTape.midBox ibox92))
    (by decide +kernel)
private theorem midpoint_even_92 : ∀ k, 2 ∣ (ibox92 k).lo+(ibox92 k).hi := by decide +kernel
private theorem accepted_92 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox92) tree92 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox92 midpoint_even_92
  simp only [tree92,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox92,candidate_valid h (FixedTape.midBox ibox92),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox92 212 (FixedTape.rowsAux denominator ibox92 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox92) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_92
private noncomputable def tree91 : TapeTree := .split 0 (((7779099050649400954074802555533720508642099200000000000 : Int) : ℚ)/(denominator : ℚ)) tree92 tree93
attribute [irreducible] tree91
private theorem accepted_91 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox91) tree91 = true := by
  simp only [tree91,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox91 0 (7779099050649400954074802555533720508642099200000000000 : Int) false,decode_split denominator ibox91 0 (7779099050649400954074802555533720508642099200000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_92 h,accepted_93 h⟩
private noncomputable def tree90 : TapeTree := .centered (candidateRows ibox90) (candidateRows (FixedTape.midBox ibox90))
attribute [irreducible] tree90
private theorem sign_90 : 2*denominator*(computed denominator (FixedTape.midBox ibox90)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox90).gradient k).lo.natAbs ((computed denominator ibox90).gradient k).hi.natAbs : Int)*((ibox90 k).hi-(ibox90 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox90
    (computed denominator ibox90) (computed denominator (FixedTape.midBox ibox90))
    (by decide +kernel)
private theorem midpoint_even_90 : ∀ k, 2 ∣ (ibox90 k).lo+(ibox90 k).hi := by decide +kernel
private theorem accepted_90 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox90) tree90 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox90 midpoint_even_90
  simp only [tree90,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox90,candidate_valid h (FixedTape.midBox ibox90),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox90 212 (FixedTape.rowsAux denominator ibox90 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox90) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_90
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
private noncomputable def tree88 : TapeTree := .split 0 (((7779099050649400954074802555533720508642099200000000000 : Int) : ℚ)/(denominator : ℚ)) tree89 tree90
attribute [irreducible] tree88
private theorem accepted_88 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox88) tree88 = true := by
  simp only [tree88,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox88 0 (7779099050649400954074802555533720508642099200000000000 : Int) false,decode_split denominator ibox88 0 (7779099050649400954074802555533720508642099200000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_89 h,accepted_90 h⟩
private noncomputable def tree87 : TapeTree := .split 3 (((2868834607874544985704416980864296446884577280000000000000 : Int) : ℚ)/(denominator : ℚ)) tree88 tree91
attribute [irreducible] tree87
private theorem accepted_87 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox87) tree87 = true := by
  simp only [tree87,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox87 3 (2868834607874544985704416980864296446884577280000000000000 : Int) false,decode_split denominator ibox87 3 (2868834607874544985704416980864296446884577280000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_88 h,accepted_91 h⟩
private noncomputable def tree86 : TapeTree := .split 0 (((7870617863009982141769800232657646632273182720000000000 : Int) : ℚ)/(denominator : ℚ)) tree87 tree94
attribute [irreducible] tree86
private theorem accepted_86 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox86) tree86 = true := by
  simp only [tree86,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox86 0 (7870617863009982141769800232657646632273182720000000000 : Int) false,decode_split denominator ibox86 0 (7870617863009982141769800232657646632273182720000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_87 h,accepted_94 h⟩
private noncomputable def tree85 : TapeTree := .centered (candidateRows ibox85) (candidateRows (FixedTape.midBox ibox85))
attribute [irreducible] tree85
private theorem sign_85 : 2*denominator*(computed denominator (FixedTape.midBox ibox85)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox85).gradient k).lo.natAbs ((computed denominator ibox85).gradient k).hi.natAbs : Int)*((ibox85 k).hi-(ibox85 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox85
    (computed denominator ibox85) (computed denominator (FixedTape.midBox ibox85))
    (by decide +kernel)
private theorem midpoint_even_85 : ∀ k, 2 ∣ (ibox85 k).lo+(ibox85 k).hi := by decide +kernel
private theorem accepted_85 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox85) tree85 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox85 midpoint_even_85
  simp only [tree85,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox85,candidate_valid h (FixedTape.midBox ibox85),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox85 212 (FixedTape.rowsAux denominator ibox85 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox85) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_85
private noncomputable def tree84 : TapeTree := .centered (candidateRows ibox84) (candidateRows (FixedTape.midBox ibox84))
attribute [irreducible] tree84
private theorem sign_84 : 2*denominator*(computed denominator (FixedTape.midBox ibox84)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox84).gradient k).lo.natAbs ((computed denominator ibox84).gradient k).hi.natAbs : Int)*((ibox84 k).hi-(ibox84 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox84
    (computed denominator ibox84) (computed denominator (FixedTape.midBox ibox84))
    (by decide +kernel)
private theorem midpoint_even_84 : ∀ k, 2 ∣ (ibox84 k).lo+(ibox84 k).hi := by decide +kernel
private theorem accepted_84 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox84) tree84 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox84 midpoint_even_84
  simp only [tree84,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox84,candidate_valid h (FixedTape.midBox ibox84),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox84 212 (FixedTape.rowsAux denominator ibox84 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox84) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_84
private noncomputable def tree83 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree84 tree85
attribute [irreducible] tree83
private theorem accepted_83 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox83) tree83 = true := by
  simp only [tree83,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox83 3 (956278202624848328568138993621432148961525760000000000000 : Int) false,decode_split denominator ibox83 3 (956278202624848328568138993621432148961525760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_84 h,accepted_85 h⟩
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
private noncomputable def tree81 : TapeTree := .centered (candidateRows ibox81) (candidateRows (FixedTape.midBox ibox81))
attribute [irreducible] tree81
private theorem sign_81 : 2*denominator*(computed denominator (FixedTape.midBox ibox81)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox81).gradient k).lo.natAbs ((computed denominator ibox81).gradient k).hi.natAbs : Int)*((ibox81 k).hi-(ibox81 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox81
    (computed denominator ibox81) (computed denominator (FixedTape.midBox ibox81))
    (by decide +kernel)
private theorem midpoint_even_81 : ∀ k, 2 ∣ (ibox81 k).lo+(ibox81 k).hi := by decide +kernel
private theorem accepted_81 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox81) tree81 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox81 midpoint_even_81
  simp only [tree81,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox81,candidate_valid h (FixedTape.midBox ibox81),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox81 212 (FixedTape.rowsAux denominator ibox81 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox81) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_81
private noncomputable def tree80 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree81 tree82
attribute [irreducible] tree80
private theorem accepted_80 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox80) tree80 = true := by
  simp only [tree80,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox80 3 (956278202624848328568138993621432148961525760000000000000 : Int) false,decode_split denominator ibox80 3 (956278202624848328568138993621432148961525760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_81 h,accepted_82 h⟩
private noncomputable def tree79 : TapeTree := .split 0 (((7962136675370563329464797909781572755904266240000000000 : Int) : ℚ)/(denominator : ℚ)) tree80 tree83
attribute [irreducible] tree79
private theorem accepted_79 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox79) tree79 = true := by
  simp only [tree79,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox79 0 (7962136675370563329464797909781572755904266240000000000 : Int) false,decode_split denominator ibox79 0 (7962136675370563329464797909781572755904266240000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_80 h,accepted_83 h⟩
private noncomputable def tree78 : TapeTree := .centered (candidateRows ibox78) (candidateRows (FixedTape.midBox ibox78))
attribute [irreducible] tree78
private theorem sign_78 : 2*denominator*(computed denominator (FixedTape.midBox ibox78)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox78).gradient k).lo.natAbs ((computed denominator ibox78).gradient k).hi.natAbs : Int)*((ibox78 k).hi-(ibox78 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox78
    (computed denominator ibox78) (computed denominator (FixedTape.midBox ibox78))
    (by decide +kernel)
private theorem midpoint_even_78 : ∀ k, 2 ∣ (ibox78 k).lo+(ibox78 k).hi := by decide +kernel
private theorem accepted_78 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox78) tree78 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox78 midpoint_even_78
  simp only [tree78,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox78,candidate_valid h (FixedTape.midBox ibox78),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox78 212 (FixedTape.rowsAux denominator ibox78 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox78) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_78
private noncomputable def tree77 : TapeTree := .centered (candidateRows ibox77) (candidateRows (FixedTape.midBox ibox77))
attribute [irreducible] tree77
private theorem sign_77 : 2*denominator*(computed denominator (FixedTape.midBox ibox77)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox77).gradient k).lo.natAbs ((computed denominator ibox77).gradient k).hi.natAbs : Int)*((ibox77 k).hi-(ibox77 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox77
    (computed denominator ibox77) (computed denominator (FixedTape.midBox ibox77))
    (by decide +kernel)
private theorem midpoint_even_77 : ∀ k, 2 ∣ (ibox77 k).lo+(ibox77 k).hi := by decide +kernel
private theorem accepted_77 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox77) tree77 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox77 midpoint_even_77
  simp only [tree77,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox77,candidate_valid h (FixedTape.midBox ibox77),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox77 212 (FixedTape.rowsAux denominator ibox77 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox77) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_77
private noncomputable def tree76 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree77 tree78
attribute [irreducible] tree76
private theorem accepted_76 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox76) tree76 = true := by
  simp only [tree76,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox76 3 (956278202624848328568138993621432148961525760000000000000 : Int) false,decode_split denominator ibox76 3 (956278202624848328568138993621432148961525760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_77 h,accepted_78 h⟩
private noncomputable def tree75 : TapeTree := .centered (candidateRows ibox75) (candidateRows (FixedTape.midBox ibox75))
attribute [irreducible] tree75
private theorem sign_75 : 2*denominator*(computed denominator (FixedTape.midBox ibox75)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox75).gradient k).lo.natAbs ((computed denominator ibox75).gradient k).hi.natAbs : Int)*((ibox75 k).hi-(ibox75 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox75
    (computed denominator ibox75) (computed denominator (FixedTape.midBox ibox75))
    (by decide +kernel)
private theorem midpoint_even_75 : ∀ k, 2 ∣ (ibox75 k).lo+(ibox75 k).hi := by decide +kernel
private theorem accepted_75 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox75) tree75 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox75 midpoint_even_75
  simp only [tree75,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox75,candidate_valid h (FixedTape.midBox ibox75),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox75 212 (FixedTape.rowsAux denominator ibox75 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox75) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_75
private noncomputable def tree74 : TapeTree := .centered (candidateRows ibox74) (candidateRows (FixedTape.midBox ibox74))
attribute [irreducible] tree74
private theorem sign_74 : 2*denominator*(computed denominator (FixedTape.midBox ibox74)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox74).gradient k).lo.natAbs ((computed denominator ibox74).gradient k).hi.natAbs : Int)*((ibox74 k).hi-(ibox74 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox74
    (computed denominator ibox74) (computed denominator (FixedTape.midBox ibox74))
    (by decide +kernel)
private theorem midpoint_even_74 : ∀ k, 2 ∣ (ibox74 k).lo+(ibox74 k).hi := by decide +kernel
private theorem accepted_74 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox74) tree74 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox74 midpoint_even_74
  simp only [tree74,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox74,candidate_valid h (FixedTape.midBox ibox74),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox74 212 (FixedTape.rowsAux denominator ibox74 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox74) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_74
private noncomputable def tree73 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree74 tree75
attribute [irreducible] tree73
private theorem accepted_73 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox73) tree73 = true := by
  simp only [tree73,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox73 3 (956278202624848328568138993621432148961525760000000000000 : Int) false,decode_split denominator ibox73 3 (956278202624848328568138993621432148961525760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_74 h,accepted_75 h⟩
private noncomputable def tree72 : TapeTree := .split 0 (((7779099050649400954074802555533720508642099200000000000 : Int) : ℚ)/(denominator : ℚ)) tree73 tree76
attribute [irreducible] tree72
private theorem accepted_72 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox72) tree72 = true := by
  simp only [tree72,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox72 0 (7779099050649400954074802555533720508642099200000000000 : Int) false,decode_split denominator ibox72 0 (7779099050649400954074802555533720508642099200000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_73 h,accepted_76 h⟩
private noncomputable def tree71 : TapeTree := .split 0 (((7870617863009982141769800232657646632273182720000000000 : Int) : ℚ)/(denominator : ℚ)) tree72 tree79
attribute [irreducible] tree71
private theorem accepted_71 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox71) tree71 = true := by
  simp only [tree71,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox71 0 (7870617863009982141769800232657646632273182720000000000 : Int) false,decode_split denominator ibox71 0 (7870617863009982141769800232657646632273182720000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_72 h,accepted_79 h⟩
private noncomputable def tree70 : TapeTree := .split 3 (((1912556405249696657136277987242864297923051520000000000000 : Int) : ℚ)/(denominator : ℚ)) tree71 tree86
attribute [irreducible] tree70
private theorem accepted_70 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox70) tree70 = true := by
  simp only [tree70,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox70 3 (1912556405249696657136277987242864297923051520000000000000 : Int) false,decode_split denominator ibox70 3 (1912556405249696657136277987242864297923051520000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_71 h,accepted_86 h⟩
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
private noncomputable def tree68 : TapeTree := .centered (candidateRows ibox68) (candidateRows (FixedTape.midBox ibox68))
attribute [irreducible] tree68
private theorem sign_68 : 2*denominator*(computed denominator (FixedTape.midBox ibox68)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox68).gradient k).lo.natAbs ((computed denominator ibox68).gradient k).hi.natAbs : Int)*((ibox68 k).hi-(ibox68 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox68
    (computed denominator ibox68) (computed denominator (FixedTape.midBox ibox68))
    (by decide +kernel)
private theorem midpoint_even_68 : ∀ k, 2 ∣ (ibox68 k).lo+(ibox68 k).hi := by decide +kernel
private theorem accepted_68 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox68) tree68 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox68 midpoint_even_68
  simp only [tree68,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox68,candidate_valid h (FixedTape.midBox ibox68),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox68 212 (FixedTape.rowsAux denominator ibox68 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox68) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_68
private noncomputable def tree67 : TapeTree := .split 3 (((2868834607874544985704416980864296446884577280000000000000 : Int) : ℚ)/(denominator : ℚ)) tree68 tree69
attribute [irreducible] tree67
private theorem accepted_67 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox67) tree67 = true := by
  simp only [tree67,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox67 3 (2868834607874544985704416980864296446884577280000000000000 : Int) false,decode_split denominator ibox67 3 (2868834607874544985704416980864296446884577280000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_68 h,accepted_69 h⟩
private noncomputable def tree66 : TapeTree := .centered (candidateRows ibox66) (candidateRows (FixedTape.midBox ibox66))
attribute [irreducible] tree66
private theorem sign_66 : 2*denominator*(computed denominator (FixedTape.midBox ibox66)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox66).gradient k).lo.natAbs ((computed denominator ibox66).gradient k).hi.natAbs : Int)*((ibox66 k).hi-(ibox66 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox66
    (computed denominator ibox66) (computed denominator (FixedTape.midBox ibox66))
    (by decide +kernel)
private theorem midpoint_even_66 : ∀ k, 2 ∣ (ibox66 k).lo+(ibox66 k).hi := by decide +kernel
private theorem accepted_66 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox66) tree66 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox66 midpoint_even_66
  simp only [tree66,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox66,candidate_valid h (FixedTape.midBox ibox66),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox66 212 (FixedTape.rowsAux denominator ibox66 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox66) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_66
private noncomputable def tree65 : TapeTree := .centered (candidateRows ibox65) (candidateRows (FixedTape.midBox ibox65))
attribute [irreducible] tree65
private theorem sign_65 : 2*denominator*(computed denominator (FixedTape.midBox ibox65)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox65).gradient k).lo.natAbs ((computed denominator ibox65).gradient k).hi.natAbs : Int)*((ibox65 k).hi-(ibox65 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox65
    (computed denominator ibox65) (computed denominator (FixedTape.midBox ibox65))
    (by decide +kernel)
private theorem midpoint_even_65 : ∀ k, 2 ∣ (ibox65 k).lo+(ibox65 k).hi := by decide +kernel
private theorem accepted_65 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox65) tree65 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox65 midpoint_even_65
  simp only [tree65,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox65,candidate_valid h (FixedTape.midBox ibox65),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox65 212 (FixedTape.rowsAux denominator ibox65 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox65) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_65
private noncomputable def tree64 : TapeTree := .split 3 (((2868834607874544985704416980864296446884577280000000000000 : Int) : ℚ)/(denominator : ℚ)) tree65 tree66
attribute [irreducible] tree64
private theorem accepted_64 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox64) tree64 = true := by
  simp only [tree64,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox64 3 (2868834607874544985704416980864296446884577280000000000000 : Int) false,decode_split denominator ibox64 3 (2868834607874544985704416980864296446884577280000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_65 h,accepted_66 h⟩
private noncomputable def tree63 : TapeTree := .split 0 (((7596061425928238578684807201285868261379932160000000000 : Int) : ℚ)/(denominator : ℚ)) tree64 tree67
attribute [irreducible] tree63
private theorem accepted_63 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox63) tree63 = true := by
  simp only [tree63,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox63 0 (7596061425928238578684807201285868261379932160000000000 : Int) false,decode_split denominator ibox63 0 (7596061425928238578684807201285868261379932160000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_64 h,accepted_67 h⟩
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
private noncomputable def tree60 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree61 tree62
attribute [irreducible] tree60
private theorem accepted_60 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox60) tree60 = true := by
  simp only [tree60,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox60 3 (956278202624848328568138993621432148961525760000000000000 : Int) false,decode_split denominator ibox60 3 (956278202624848328568138993621432148961525760000000000000 : Int) true]
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
private noncomputable def tree57 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree58 tree59
attribute [irreducible] tree57
private theorem accepted_57 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox57) tree57 = true := by
  simp only [tree57,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox57 3 (956278202624848328568138993621432148961525760000000000000 : Int) false,decode_split denominator ibox57 3 (956278202624848328568138993621432148961525760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_58 h,accepted_59 h⟩
private noncomputable def tree56 : TapeTree := .split 0 (((7596061425928238578684807201285868261379932160000000000 : Int) : ℚ)/(denominator : ℚ)) tree57 tree60
attribute [irreducible] tree56
private theorem accepted_56 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox56) tree56 = true := by
  simp only [tree56,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox56 0 (7596061425928238578684807201285868261379932160000000000 : Int) false,decode_split denominator ibox56 0 (7596061425928238578684807201285868261379932160000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_57 h,accepted_60 h⟩
private noncomputable def tree55 : TapeTree := .split 3 (((1912556405249696657136277987242864297923051520000000000000 : Int) : ℚ)/(denominator : ℚ)) tree56 tree63
attribute [irreducible] tree55
private theorem accepted_55 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox55) tree55 = true := by
  simp only [tree55,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox55 3 (1912556405249696657136277987242864297923051520000000000000 : Int) false,decode_split denominator ibox55 3 (1912556405249696657136277987242864297923051520000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_56 h,accepted_63 h⟩
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
private noncomputable def tree53 : TapeTree := .centered (candidateRows ibox53) (candidateRows (FixedTape.midBox ibox53))
attribute [irreducible] tree53
private theorem sign_53 : 2*denominator*(computed denominator (FixedTape.midBox ibox53)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox53).gradient k).lo.natAbs ((computed denominator ibox53).gradient k).hi.natAbs : Int)*((ibox53 k).hi-(ibox53 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox53
    (computed denominator ibox53) (computed denominator (FixedTape.midBox ibox53))
    (by decide +kernel)
private theorem midpoint_even_53 : ∀ k, 2 ∣ (ibox53 k).lo+(ibox53 k).hi := by decide +kernel
private theorem accepted_53 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox53) tree53 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox53 midpoint_even_53
  simp only [tree53,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox53,candidate_valid h (FixedTape.midBox ibox53),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox53 212 (FixedTape.rowsAux denominator ibox53 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox53) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_53
private noncomputable def tree52 : TapeTree := .split 3 (((2868834607874544985704416980864296446884577280000000000000 : Int) : ℚ)/(denominator : ℚ)) tree53 tree54
attribute [irreducible] tree52
private theorem accepted_52 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox52) tree52 = true := by
  simp only [tree52,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox52 3 (2868834607874544985704416980864296446884577280000000000000 : Int) false,decode_split denominator ibox52 3 (2868834607874544985704416980864296446884577280000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_53 h,accepted_54 h⟩
private noncomputable def tree51 : TapeTree := .centered (candidateRows ibox51) (candidateRows (FixedTape.midBox ibox51))
attribute [irreducible] tree51
private theorem sign_51 : 2*denominator*(computed denominator (FixedTape.midBox ibox51)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox51).gradient k).lo.natAbs ((computed denominator ibox51).gradient k).hi.natAbs : Int)*((ibox51 k).hi-(ibox51 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox51
    (computed denominator ibox51) (computed denominator (FixedTape.midBox ibox51))
    (by decide +kernel)
private theorem midpoint_even_51 : ∀ k, 2 ∣ (ibox51 k).lo+(ibox51 k).hi := by decide +kernel
private theorem accepted_51 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox51) tree51 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox51 midpoint_even_51
  simp only [tree51,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox51,candidate_valid h (FixedTape.midBox ibox51),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox51 212 (FixedTape.rowsAux denominator ibox51 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox51) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_51
private noncomputable def tree50 : TapeTree := .centered (candidateRows ibox50) (candidateRows (FixedTape.midBox ibox50))
attribute [irreducible] tree50
private theorem sign_50 : 2*denominator*(computed denominator (FixedTape.midBox ibox50)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox50).gradient k).lo.natAbs ((computed denominator ibox50).gradient k).hi.natAbs : Int)*((ibox50 k).hi-(ibox50 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox50
    (computed denominator ibox50) (computed denominator (FixedTape.midBox ibox50))
    (by decide +kernel)
private theorem midpoint_even_50 : ∀ k, 2 ∣ (ibox50 k).lo+(ibox50 k).hi := by decide +kernel
private theorem accepted_50 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox50) tree50 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox50 midpoint_even_50
  simp only [tree50,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox50,candidate_valid h (FixedTape.midBox ibox50),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox50 212 (FixedTape.rowsAux denominator ibox50 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox50) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_50
private noncomputable def tree49 : TapeTree := .split 3 (((2868834607874544985704416980864296446884577280000000000000 : Int) : ℚ)/(denominator : ℚ)) tree50 tree51
attribute [irreducible] tree49
private theorem accepted_49 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox49) tree49 = true := by
  simp only [tree49,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox49 3 (2868834607874544985704416980864296446884577280000000000000 : Int) false,decode_split denominator ibox49 3 (2868834607874544985704416980864296446884577280000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_50 h,accepted_51 h⟩
private noncomputable def tree48 : TapeTree := .split 0 (((7413023801207076203294811847038016014117765120000000000 : Int) : ℚ)/(denominator : ℚ)) tree49 tree52
attribute [irreducible] tree48
private theorem accepted_48 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox48) tree48 = true := by
  simp only [tree48,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox48 0 (7413023801207076203294811847038016014117765120000000000 : Int) false,decode_split denominator ibox48 0 (7413023801207076203294811847038016014117765120000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_49 h,accepted_52 h⟩
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
private noncomputable def tree45 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree46 tree47
attribute [irreducible] tree45
private theorem accepted_45 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox45) tree45 = true := by
  simp only [tree45,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox45 3 (956278202624848328568138993621432148961525760000000000000 : Int) false,decode_split denominator ibox45 3 (956278202624848328568138993621432148961525760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_46 h,accepted_47 h⟩
private noncomputable def tree44 : TapeTree := .centered (candidateRows ibox44) (candidateRows (FixedTape.midBox ibox44))
attribute [irreducible] tree44
private theorem sign_44 : 2*denominator*(computed denominator (FixedTape.midBox ibox44)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox44).gradient k).lo.natAbs ((computed denominator ibox44).gradient k).hi.natAbs : Int)*((ibox44 k).hi-(ibox44 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox44
    (computed denominator ibox44) (computed denominator (FixedTape.midBox ibox44))
    (by decide +kernel)
private theorem midpoint_even_44 : ∀ k, 2 ∣ (ibox44 k).lo+(ibox44 k).hi := by decide +kernel
private theorem accepted_44 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox44) tree44 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox44 midpoint_even_44
  simp only [tree44,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox44,candidate_valid h (FixedTape.midBox ibox44),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox44 212 (FixedTape.rowsAux denominator ibox44 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox44) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_44
private noncomputable def tree43 : TapeTree := .centered (candidateRows ibox43) (candidateRows (FixedTape.midBox ibox43))
attribute [irreducible] tree43
private theorem sign_43 : 2*denominator*(computed denominator (FixedTape.midBox ibox43)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox43).gradient k).lo.natAbs ((computed denominator ibox43).gradient k).hi.natAbs : Int)*((ibox43 k).hi-(ibox43 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox43
    (computed denominator ibox43) (computed denominator (FixedTape.midBox ibox43))
    (by decide +kernel)
private theorem midpoint_even_43 : ∀ k, 2 ∣ (ibox43 k).lo+(ibox43 k).hi := by decide +kernel
private theorem accepted_43 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox43) tree43 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox43 midpoint_even_43
  simp only [tree43,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox43,candidate_valid h (FixedTape.midBox ibox43),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox43 212 (FixedTape.rowsAux denominator ibox43 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox43) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_43
private noncomputable def tree42 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree43 tree44
attribute [irreducible] tree42
private theorem accepted_42 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox42) tree42 = true := by
  simp only [tree42,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox42 3 (956278202624848328568138993621432148961525760000000000000 : Int) false,decode_split denominator ibox42 3 (956278202624848328568138993621432148961525760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_43 h,accepted_44 h⟩
private noncomputable def tree41 : TapeTree := .split 0 (((7413023801207076203294811847038016014117765120000000000 : Int) : ℚ)/(denominator : ℚ)) tree42 tree45
attribute [irreducible] tree41
private theorem accepted_41 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox41) tree41 = true := by
  simp only [tree41,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox41 0 (7413023801207076203294811847038016014117765120000000000 : Int) false,decode_split denominator ibox41 0 (7413023801207076203294811847038016014117765120000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_42 h,accepted_45 h⟩
private noncomputable def tree40 : TapeTree := .split 3 (((1912556405249696657136277987242864297923051520000000000000 : Int) : ℚ)/(denominator : ℚ)) tree41 tree48
attribute [irreducible] tree40
private theorem accepted_40 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox40) tree40 = true := by
  simp only [tree40,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox40 3 (1912556405249696657136277987242864297923051520000000000000 : Int) false,decode_split denominator ibox40 3 (1912556405249696657136277987242864297923051520000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_41 h,accepted_48 h⟩
private noncomputable def tree39 : TapeTree := .split 0 (((7504542613567657390989809524161942137748848640000000000 : Int) : ℚ)/(denominator : ℚ)) tree40 tree55
attribute [irreducible] tree39
private theorem accepted_39 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox39) tree39 = true := by
  simp only [tree39,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox39 0 (7504542613567657390989809524161942137748848640000000000 : Int) false,decode_split denominator ibox39 0 (7504542613567657390989809524161942137748848640000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_40 h,accepted_55 h⟩
private noncomputable def tree38 : TapeTree := .split 0 (((7687580238288819766379804878409794385011015680000000000 : Int) : ℚ)/(denominator : ℚ)) tree39 tree70
attribute [irreducible] tree38
private theorem accepted_38 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox38) tree38 = true := by
  simp only [tree38,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox38 0 (7687580238288819766379804878409794385011015680000000000 : Int) false,decode_split denominator ibox38 0 (7687580238288819766379804878409794385011015680000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_39 h,accepted_70 h⟩
private noncomputable def tree37 : TapeTree := .split 3 (((3825112810499393314272555974485728595846103040000000000000 : Int) : ℚ)/(denominator : ℚ)) tree38 tree101
attribute [irreducible] tree37
private theorem accepted_37 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox37) tree37 = true := by
  simp only [tree37,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox37 3 (3825112810499393314272555974485728595846103040000000000000 : Int) false,decode_split denominator ibox37 3 (3825112810499393314272555974485728595846103040000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_38 h,accepted_101 h⟩
private noncomputable def tree36 : TapeTree := .split 3 (((7650225620998786628545111948971457191692206080000000000000 : Int) : ℚ)/(denominator : ℚ)) tree37 tree164
attribute [irreducible] tree36
private theorem accepted_36 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox36) tree36 = true := by
  simp only [tree36,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox36 3 (7650225620998786628545111948971457191692206080000000000000 : Int) false,decode_split denominator ibox36 3 (7650225620998786628545111948971457191692206080000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_37 h,accepted_164 h⟩
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
private noncomputable def tree34 : TapeTree := .split 0 (((8053655487731144517159795586905498879535349760000000000 : Int) : ℚ)/(denominator : ℚ)) tree35 tree277
attribute [irreducible] tree34
private theorem accepted_34 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox34) tree34 = true := by
  simp only [tree34,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox34 0 (8053655487731144517159795586905498879535349760000000000 : Int) false,decode_split denominator ibox34 0 (8053655487731144517159795586905498879535349760000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_35 h,accepted_277 h⟩
private noncomputable def tree33 : TapeTree := .split 1 (((1912556405249696657136277987242864297923051520000000000000 : Int) : ℚ)/(denominator : ℚ)) tree34 tree421
attribute [irreducible] tree33
private theorem accepted_33 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox33) tree33 = true := by
  simp only [tree33,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox33 1 (1912556405249696657136277987242864297923051520000000000000 : Int) false,decode_split denominator ibox33 1 (1912556405249696657136277987242864297923051520000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_34 h,accepted_421 h⟩
private noncomputable def tree32 : TapeTree := .split 1 (((3825112810499393314272555974485728595846103040000000000000 : Int) : ℚ)/(denominator : ℚ)) tree33 tree430
attribute [irreducible] tree32
private theorem accepted_32 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox32) tree32 = true := by
  simp only [tree32,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox32 1 (3825112810499393314272555974485728595846103040000000000000 : Int) false,decode_split denominator ibox32 1 (3825112810499393314272555974485728595846103040000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_33 h,accepted_430 h⟩
private noncomputable def tree31 : TapeTree := .face 2 true (candidateRows ibox31) tree32
attribute [irreducible] tree31
private theorem sign_31 : 0 ≤ ((computed denominator ibox31).gradient 2).lo := by decide +kernel
private theorem accepted_31 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox31) tree31 = true := by
  simp only [tree31,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox31,?_,accepted_32 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox31)).gradient 2).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox31).gradient 2).lo) denominator_positive).2 sign_31
private noncomputable def tree30 : TapeTree := .split 1 (((7650225620998786628545111948971457191692206080000000000000 : Int) : ℚ)/(denominator : ℚ)) tree31 tree435
attribute [irreducible] tree30
private theorem accepted_30 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox30) tree30 = true := by
  simp only [tree30,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox30 1 (7650225620998786628545111948971457191692206080000000000000 : Int) false,decode_split denominator ibox30 1 (7650225620998786628545111948971457191692206080000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_31 h,accepted_435 h⟩
private noncomputable def tree29 : TapeTree := .centered (candidateRows ibox29) (candidateRows (FixedTape.midBox ibox29))
attribute [irreducible] tree29
private theorem sign_29 : 2*denominator*(computed denominator (FixedTape.midBox ibox29)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox29).gradient k).lo.natAbs ((computed denominator ibox29).gradient k).hi.natAbs : Int)*((ibox29 k).hi-(ibox29 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox29
    (computed denominator ibox29) (computed denominator (FixedTape.midBox ibox29))
    (by decide +kernel)
private theorem midpoint_even_29 : ∀ k, 2 ∣ (ibox29 k).lo+(ibox29 k).hi := by decide +kernel
private theorem accepted_29 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox29) tree29 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox29 midpoint_even_29
  simp only [tree29,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox29,candidate_valid h (FixedTape.midBox ibox29),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox29 212 (FixedTape.rowsAux denominator ibox29 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox29) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_29
private noncomputable def tree28 : TapeTree := .centered (candidateRows ibox28) (candidateRows (FixedTape.midBox ibox28))
attribute [irreducible] tree28
private theorem sign_28 : 2*denominator*(computed denominator (FixedTape.midBox ibox28)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox28).gradient k).lo.natAbs ((computed denominator ibox28).gradient k).hi.natAbs : Int)*((ibox28 k).hi-(ibox28 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox28
    (computed denominator ibox28) (computed denominator (FixedTape.midBox ibox28))
    (by decide +kernel)
private theorem midpoint_even_28 : ∀ k, 2 ∣ (ibox28 k).lo+(ibox28 k).hi := by decide +kernel
private theorem accepted_28 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox28) tree28 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox28 midpoint_even_28
  simp only [tree28,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox28,candidate_valid h (FixedTape.midBox ibox28),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox28 212 (FixedTape.rowsAux denominator ibox28 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox28) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_28
private noncomputable def tree27 : TapeTree := .split 1 (((7650225620998786628545111948971457191692206080000000000000 : Int) : ℚ)/(denominator : ℚ)) tree28 tree29
attribute [irreducible] tree27
private theorem accepted_27 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox27) tree27 = true := by
  simp only [tree27,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox27 1 (7650225620998786628545111948971457191692206080000000000000 : Int) false,decode_split denominator ibox27 1 (7650225620998786628545111948971457191692206080000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_28 h,accepted_29 h⟩
private noncomputable def tree26 : TapeTree := .face 3 false (candidateRows ibox26) tree27
attribute [irreducible] tree26
private theorem sign_26 : ((computed denominator ibox26).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_26 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox26) tree26 = true := by
  simp only [tree26,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox26,?_,accepted_27 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox26)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox26).gradient 3).hi) denominator_positive).1 sign_26
private noncomputable def tree25 : TapeTree := .centered (candidateRows ibox25) (candidateRows (FixedTape.midBox ibox25))
attribute [irreducible] tree25
private theorem sign_25 : 2*denominator*(computed denominator (FixedTape.midBox ibox25)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox25).gradient k).lo.natAbs ((computed denominator ibox25).gradient k).hi.natAbs : Int)*((ibox25 k).hi-(ibox25 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox25
    (computed denominator ibox25) (computed denominator (FixedTape.midBox ibox25))
    (by decide +kernel)
private theorem midpoint_even_25 : ∀ k, 2 ∣ (ibox25 k).lo+(ibox25 k).hi := by decide +kernel
private theorem accepted_25 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox25) tree25 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox25 midpoint_even_25
  simp only [tree25,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox25,candidate_valid h (FixedTape.midBox ibox25),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox25 212 (FixedTape.rowsAux denominator ibox25 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox25) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_25
private noncomputable def tree24 : TapeTree := .centered (candidateRows ibox24) (candidateRows (FixedTape.midBox ibox24))
attribute [irreducible] tree24
private theorem sign_24 : 2*denominator*(computed denominator (FixedTape.midBox ibox24)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox24).gradient k).lo.natAbs ((computed denominator ibox24).gradient k).hi.natAbs : Int)*((ibox24 k).hi-(ibox24 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox24
    (computed denominator ibox24) (computed denominator (FixedTape.midBox ibox24))
    (by decide +kernel)
private theorem midpoint_even_24 : ∀ k, 2 ∣ (ibox24 k).lo+(ibox24 k).hi := by decide +kernel
private theorem accepted_24 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox24) tree24 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox24 midpoint_even_24
  simp only [tree24,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox24,candidate_valid h (FixedTape.midBox ibox24),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox24 212 (FixedTape.rowsAux denominator ibox24 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox24) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_24
private noncomputable def tree23 : TapeTree := .split 1 (((7650225620998786628545111948971457191692206080000000000000 : Int) : ℚ)/(denominator : ℚ)) tree24 tree25
attribute [irreducible] tree23
private theorem accepted_23 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox23) tree23 = true := by
  simp only [tree23,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox23 1 (7650225620998786628545111948971457191692206080000000000000 : Int) false,decode_split denominator ibox23 1 (7650225620998786628545111948971457191692206080000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_24 h,accepted_25 h⟩
private noncomputable def tree22 : TapeTree := .face 3 false (candidateRows ibox22) tree23
attribute [irreducible] tree22
private theorem sign_22 : ((computed denominator ibox22).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_22 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox22) tree22 = true := by
  simp only [tree22,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox22,?_,accepted_23 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox22)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox22).gradient 3).hi) denominator_positive).1 sign_22
private noncomputable def tree21 : TapeTree := .split 0 (((8053655487731144517159795586905498879535349760000000000 : Int) : ℚ)/(denominator : ℚ)) tree22 tree26
attribute [irreducible] tree21
private theorem accepted_21 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox21) tree21 = true := by
  simp only [tree21,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox21 0 (8053655487731144517159795586905498879535349760000000000 : Int) false,decode_split denominator ibox21 0 (8053655487731144517159795586905498879535349760000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_22 h,accepted_26 h⟩
private noncomputable def tree20 : TapeTree := .split 2 (((11475338431498179942817667923457185787538309120000000000000 : Int) : ℚ)/(denominator : ℚ)) tree21 tree30
attribute [irreducible] tree20
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox20 2 (11475338431498179942817667923457185787538309120000000000000 : Int) false,decode_split denominator ibox20 2 (11475338431498179942817667923457185787538309120000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_21 h,accepted_30 h⟩
private noncomputable def tree19 : TapeTree := .split 0 (((8785805986615794018719777003896907868584017920000000000 : Int) : ℚ)/(denominator : ℚ)) tree20 tree443
attribute [irreducible] tree19
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox19 0 (8785805986615794018719777003896907868584017920000000000 : Int) false,decode_split denominator ibox19 0 (8785805986615794018719777003896907868584017920000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_20 h,accepted_443 h⟩
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
private noncomputable def tree17 : TapeTree := .centered (candidateRows ibox17) (candidateRows (FixedTape.midBox ibox17))
attribute [irreducible] tree17
private theorem sign_17 : 2*denominator*(computed denominator (FixedTape.midBox ibox17)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox17).gradient k).lo.natAbs ((computed denominator ibox17).gradient k).hi.natAbs : Int)*((ibox17 k).hi-(ibox17 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox17
    (computed denominator ibox17) (computed denominator (FixedTape.midBox ibox17))
    (by decide +kernel)
private theorem midpoint_even_17 : ∀ k, 2 ∣ (ibox17 k).lo+(ibox17 k).hi := by decide +kernel
private theorem accepted_17 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox17) tree17 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox17 midpoint_even_17
  simp only [tree17,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox17,candidate_valid h (FixedTape.midBox ibox17),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox17 212 (FixedTape.rowsAux denominator ibox17 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox17) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_17
private noncomputable def tree16 : TapeTree := .split 0 (((9517956485500443520279758420888316857632686080000000000 : Int) : ℚ)/(denominator : ℚ)) tree17 tree18
attribute [irreducible] tree16
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox16 0 (9517956485500443520279758420888316857632686080000000000 : Int) false,decode_split denominator ibox16 0 (9517956485500443520279758420888316857632686080000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_17 h,accepted_18 h⟩
private noncomputable def tree15 : TapeTree := .centered (candidateRows ibox15) (candidateRows (FixedTape.midBox ibox15))
attribute [irreducible] tree15
private theorem sign_15 : 2*denominator*(computed denominator (FixedTape.midBox ibox15)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox15).gradient k).lo.natAbs ((computed denominator ibox15).gradient k).hi.natAbs : Int)*((ibox15 k).hi-(ibox15 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox15
    (computed denominator ibox15) (computed denominator (FixedTape.midBox ibox15))
    (by decide +kernel)
private theorem midpoint_even_15 : ∀ k, 2 ∣ (ibox15 k).lo+(ibox15 k).hi := by decide +kernel
private theorem accepted_15 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox15) tree15 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox15 midpoint_even_15
  simp only [tree15,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox15,candidate_valid h (FixedTape.midBox ibox15),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox15 212 (FixedTape.rowsAux denominator ibox15 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox15) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_15
private noncomputable def tree14 : TapeTree := .split 1 (((11475338431498179942817667923457185787538309120000000000000 : Int) : ℚ)/(denominator : ℚ)) tree15 tree16
attribute [irreducible] tree14
private theorem accepted_14 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox14) tree14 = true := by
  simp only [tree14,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox14 1 (11475338431498179942817667923457185787538309120000000000000 : Int) false,decode_split denominator ibox14 1 (11475338431498179942817667923457185787538309120000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_15 h,accepted_16 h⟩
private noncomputable def tree13 : TapeTree := .centered (candidateRows ibox13) (candidateRows (FixedTape.midBox ibox13))
attribute [irreducible] tree13
private theorem sign_13 : 2*denominator*(computed denominator (FixedTape.midBox ibox13)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox13).gradient k).lo.natAbs ((computed denominator ibox13).gradient k).hi.natAbs : Int)*((ibox13 k).hi-(ibox13 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox13
    (computed denominator ibox13) (computed denominator (FixedTape.midBox ibox13))
    (by decide +kernel)
private theorem midpoint_even_13 : ∀ k, 2 ∣ (ibox13 k).lo+(ibox13 k).hi := by decide +kernel
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox13 midpoint_even_13
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox13,candidate_valid h (FixedTape.midBox ibox13),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox13 212 (FixedTape.rowsAux denominator ibox13 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox13) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_13
private noncomputable def tree12 : TapeTree := .face 2 true (candidateRows ibox12) tree13
attribute [irreducible] tree12
private theorem sign_12 : 0 ≤ ((computed denominator ibox12).gradient 2).lo := by decide +kernel
private theorem accepted_12 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox12) tree12 = true := by
  simp only [tree12,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox12,?_,accepted_13 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox12)).gradient 2).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox12).gradient 2).lo) denominator_positive).2 sign_12
private noncomputable def tree11 : TapeTree := .split 1 (((7650225620998786628545111948971457191692206080000000000000 : Int) : ℚ)/(denominator : ℚ)) tree12 tree14
attribute [irreducible] tree11
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox11 1 (7650225620998786628545111948971457191692206080000000000000 : Int) false,decode_split denominator ibox11 1 (7650225620998786628545111948971457191692206080000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_12 h,accepted_14 h⟩
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
private noncomputable def tree9 : TapeTree := .face 1 true (candidateRows ibox9) tree10
attribute [irreducible] tree9
private theorem sign_9 : 0 ≤ ((computed denominator ibox9).gradient 1).lo := by decide +kernel
private theorem accepted_9 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox9) tree9 = true := by
  simp only [tree9,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox9,?_,accepted_10 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox9)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox9).gradient 1).lo) denominator_positive).2 sign_9
private noncomputable def tree8 : TapeTree := .centered (candidateRows ibox8) (candidateRows (FixedTape.midBox ibox8))
attribute [irreducible] tree8
private theorem sign_8 : 2*denominator*(computed denominator (FixedTape.midBox ibox8)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox8).gradient k).lo.natAbs ((computed denominator ibox8).gradient k).hi.natAbs : Int)*((ibox8 k).hi-(ibox8 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox8
    (computed denominator ibox8) (computed denominator (FixedTape.midBox ibox8))
    (by decide +kernel)
private theorem midpoint_even_8 : ∀ k, 2 ∣ (ibox8 k).lo+(ibox8 k).hi := by decide +kernel
private theorem accepted_8 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox8) tree8 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox8 midpoint_even_8
  simp only [tree8,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox8,candidate_valid h (FixedTape.midBox ibox8),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox8 212 (FixedTape.rowsAux denominator ibox8 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox8) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_8
private noncomputable def tree7 : TapeTree := .face 1 true (candidateRows ibox7) tree8
attribute [irreducible] tree7
private theorem sign_7 : 0 ≤ ((computed denominator ibox7).gradient 1).lo := by decide +kernel
private theorem accepted_7 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox7) tree7 = true := by
  simp only [tree7,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox7,?_,accepted_8 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox7)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox7).gradient 1).lo) denominator_positive).2 sign_7
private noncomputable def tree6 : TapeTree := .split 0 (((8053655487731144517159795586905498879535349760000000000 : Int) : ℚ)/(denominator : ℚ)) tree7 tree9
attribute [irreducible] tree6
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox6 0 (8053655487731144517159795586905498879535349760000000000 : Int) false,decode_split denominator ibox6 0 (8053655487731144517159795586905498879535349760000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_7 h,accepted_9 h⟩
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
private noncomputable def tree3 : TapeTree := .split 1 (((7650225620998786628545111948971457191692206080000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree6
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 1 (7650225620998786628545111948971457191692206080000000000000 : Int) false,decode_split denominator ibox3 1 (7650225620998786628545111948971457191692206080000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_6 h⟩
private noncomputable def tree2 : TapeTree := .split 0 (((8785805986615794018719777003896907868584017920000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree11
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 0 (8785805986615794018719777003896907868584017920000000000 : Int) false,decode_split denominator ibox2 0 (8785805986615794018719777003896907868584017920000000000 : Int) true]
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
private noncomputable def tree0 : TapeTree := .split 2 (((7650225620998786628545111948971457191692206080000000000000 : Int) : ℚ)/(denominator : ℚ)) tree1 tree19
attribute [irreducible] tree0
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox0 2 (7650225620998786628545111948971457191692206080000000000000 : Int) false,decode_split denominator ibox0 2 (7650225620998786628545111948971457191692206080000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_1 h,accepted_19 h⟩
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (49/102400 : ℚ) (343/512000 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 212 = e219 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (49/102400 : ℚ) (343/512000 : ℚ)) x → eval e219 x ≤ 0 := by
  have hb := h.child_4 tape 212 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell3_low_internal

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell3_low_internal
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((49/102400 : ℚ) : ℝ) < p ∧ p ≤ ((343/512000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 3 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 3 p)
    (hk0 : ((343/512000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((49/102400 : ℚ) : ℝ))
    (hk1 : ((343/512000 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((49/102400 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r), internalResidual (0 : Fin 9) a p A r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell3_low_internal.cell_bound h.child_8 h.child_9 (Cell3_low_internal.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell3_low_internal
