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
namespace Cell4_low_internal
private noncomputable def qValues : Fin 2 → ℚ := ![(119836212559/32768000000000000 : ℚ),(92978587123/16000000000 : ℚ)]
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
    priceLambda 4 p = ((119836212559/32768000000000000 : ℝ)+(92978587123/16000000000 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell4,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 4 p = (((145513/100000 : ℝ)+(145513/25000 : ℝ)*p)-(145513/100000 : ℝ)*(1/1 : ℝ))/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell4,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e219 x = (x 0*(1-x 0))*(aPoint x+priceLambda 4 (x 0)*(HStar (yPoint x)-HStar (aPoint x)-HStar (capPoint x))+priceTau 4 (x 0)*psiStar (rPoint x)+(0)-(0)) := by
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
    (hL : lambdaStar (x 0) = priceLambda 4 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 4 (x 0)) :
    (1)*eval e219 x = (x 0*(1-x 0))*(internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,if_pos hA,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (343/512000 : ℚ) (2401/2560000 : ℚ)) x → eval e219 x ≤ 0)
    (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((343/512000 : ℚ) : ℝ) < p ∧ p ≤ ((2401/2560000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 4 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 4 p)
    (hk0 : ((2401/2560000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((343/512000 : ℚ) : ℝ))
    (hk1 : ((2401/2560000 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((343/512000 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r) :
    internalResidual (0 : Fin 9) a p A r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxA,hxr⟩ := h3 (343/512000 : ℚ) (2401/2560000 : ℚ) ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ) p a A r hpcell hk0 hk1 hr ha hap hpA hAr
  have hcut : ((2401/2560000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) := by norm_num [bStar]
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxa
  have hAx : capPoint x = A := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxA
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 4 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 4 (x 0) := by simpa only [hxp] using hT
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
.const (119836212559/32768000000000000 : ℚ),
.const (92978587123/16000000000 : ℚ),
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
private noncomputable def ssaQVals : Fin 16 → ℚ := ![(1/1 : ℚ),(49/100 : ℚ),(390189/5000000 : ℚ),(1085/4818 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(4818/3733 : ℚ),(119836212559/32768000000000000 : ℚ),(92978587123/16000000000 : ℚ),(145513/100000 : ℚ),(145513/25000 : ℚ),(-145513/100000 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ)]
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
private noncomputable def denominator : Int := 1912556405249696657136277987242864297923051520000000000000000
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
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨1281263373048136627729967479734965730835169280000000000000,1793768722267391278821954471628952023169236992000000000000⟩,⟨0,1912556405249696657136277987242864297923051520000000000000000⟩,⟨0,1912556405249696657136277987242864297923051520000000000000000⟩,⟨0,1912556405249696657136277987242864297923051520000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := splitI ibox0 2 956278202624848328568138993621432148961525760000000000000000 false
private noncomputable def ibox2 : Fin 4 → FixedTape.I := faceI ibox1 3 false
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 0 1537516047657763953275960975681958877002203136000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 1 956278202624848328568138993621432148961525760000000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := faceI ibox4 2 true
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox3 1 956278202624848328568138993621432148961525760000000000000000 true
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox6 0 1409389710352950290502964227708462303918686208000000000000 false
private noncomputable def ibox8 : Fin 4 → FixedTape.I := faceI ibox7 1 true
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox6 0 1409389710352950290502964227708462303918686208000000000000 true
private noncomputable def ibox10 : Fin 4 → FixedTape.I := faceI ibox9 1 true
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox2 0 1537516047657763953275960975681958877002203136000000000000 true
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox11 1 956278202624848328568138993621432148961525760000000000000000 false
private noncomputable def ibox13 : Fin 4 → FixedTape.I := faceI ibox12 2 true
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox11 1 956278202624848328568138993621432148961525760000000000000000 true
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox14 1 1434417303937272492852208490432148223442288640000000000000000 false
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox14 1 1434417303937272492852208490432148223442288640000000000000000 true
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox16 0 1665642384962577616048957723655455450085720064000000000000 false
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox16 0 1665642384962577616048957723655455450085720064000000000000 true
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox0 2 956278202624848328568138993621432148961525760000000000000000 true
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox19 0 1537516047657763953275960975681958877002203136000000000000 false
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox20 2 1434417303937272492852208490432148223442288640000000000000000 false
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox21 0 1409389710352950290502964227708462303918686208000000000000 false
private noncomputable def ibox23 : Fin 4 → FixedTape.I := faceI ibox22 3 false
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox23 1 956278202624848328568138993621432148961525760000000000000000 false
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox23 1 956278202624848328568138993621432148961525760000000000000000 true
private noncomputable def ibox26 : Fin 4 → FixedTape.I := splitI ibox21 0 1409389710352950290502964227708462303918686208000000000000 true
private noncomputable def ibox27 : Fin 4 → FixedTape.I := faceI ibox26 3 false
private noncomputable def ibox28 : Fin 4 → FixedTape.I := splitI ibox27 1 956278202624848328568138993621432148961525760000000000000000 false
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox27 1 956278202624848328568138993621432148961525760000000000000000 true
private noncomputable def ibox30 : Fin 4 → FixedTape.I := splitI ibox20 2 1434417303937272492852208490432148223442288640000000000000000 true
private noncomputable def ibox31 : Fin 4 → FixedTape.I := splitI ibox30 1 956278202624848328568138993621432148961525760000000000000000 false
private noncomputable def ibox32 : Fin 4 → FixedTape.I := faceI ibox31 2 true
private noncomputable def ibox33 : Fin 4 → FixedTape.I := splitI ibox32 1 478139101312424164284069496810716074480762880000000000000000 false
private noncomputable def ibox34 : Fin 4 → FixedTape.I := splitI ibox33 1 239069550656212082142034748405358037240381440000000000000000 false
private noncomputable def ibox35 : Fin 4 → FixedTape.I := splitI ibox34 0 1409389710352950290502964227708462303918686208000000000000 false
private noncomputable def ibox36 : Fin 4 → FixedTape.I := faceI ibox35 1 false
private noncomputable def ibox37 : Fin 4 → FixedTape.I := splitI ibox36 3 956278202624848328568138993621432148961525760000000000000000 false
private noncomputable def ibox38 : Fin 4 → FixedTape.I := splitI ibox37 3 478139101312424164284069496810716074480762880000000000000000 false
private noncomputable def ibox39 : Fin 4 → FixedTape.I := splitI ibox38 0 1345326541700543459116465853721714017376927744000000000000 false
private noncomputable def ibox40 : Fin 4 → FixedTape.I := splitI ibox39 0 1313294957374340043423216666728339874106048512000000000000 false
private noncomputable def ibox41 : Fin 4 → FixedTape.I := splitI ibox40 3 239069550656212082142034748405358037240381440000000000000000 false
private noncomputable def ibox42 : Fin 4 → FixedTape.I := splitI ibox41 0 1297279165211238335576592073231652802470608896000000000000 false
private noncomputable def ibox43 : Fin 4 → FixedTape.I := splitI ibox41 0 1297279165211238335576592073231652802470608896000000000000 true
private noncomputable def ibox44 : Fin 4 → FixedTape.I := splitI ibox40 3 239069550656212082142034748405358037240381440000000000000000 true
private noncomputable def ibox45 : Fin 4 → FixedTape.I := splitI ibox44 0 1297279165211238335576592073231652802470608896000000000000 false
private noncomputable def ibox46 : Fin 4 → FixedTape.I := splitI ibox44 0 1297279165211238335576592073231652802470608896000000000000 true
private noncomputable def ibox47 : Fin 4 → FixedTape.I := splitI ibox39 0 1313294957374340043423216666728339874106048512000000000000 true
private noncomputable def ibox48 : Fin 4 → FixedTape.I := splitI ibox47 3 239069550656212082142034748405358037240381440000000000000000 false
private noncomputable def ibox49 : Fin 4 → FixedTape.I := splitI ibox48 0 1329310749537441751269841260225026945741488128000000000000 false
private noncomputable def ibox50 : Fin 4 → FixedTape.I := splitI ibox48 0 1329310749537441751269841260225026945741488128000000000000 true
private noncomputable def ibox51 : Fin 4 → FixedTape.I := splitI ibox47 3 239069550656212082142034748405358037240381440000000000000000 true
private noncomputable def ibox52 : Fin 4 → FixedTape.I := splitI ibox51 0 1329310749537441751269841260225026945741488128000000000000 false
private noncomputable def ibox53 : Fin 4 → FixedTape.I := splitI ibox51 0 1329310749537441751269841260225026945741488128000000000000 true
private noncomputable def ibox54 : Fin 4 → FixedTape.I := splitI ibox38 0 1345326541700543459116465853721714017376927744000000000000 true
private noncomputable def ibox55 : Fin 4 → FixedTape.I := splitI ibox54 3 239069550656212082142034748405358037240381440000000000000000 false
private noncomputable def ibox56 : Fin 4 → FixedTape.I := splitI ibox55 0 1377358126026746874809715040715088160647806976000000000000 false
private noncomputable def ibox57 : Fin 4 → FixedTape.I := splitI ibox56 0 1361342333863645166963090447218401089012367360000000000000 false
private noncomputable def ibox58 : Fin 4 → FixedTape.I := splitI ibox56 0 1361342333863645166963090447218401089012367360000000000000 true
private noncomputable def ibox59 : Fin 4 → FixedTape.I := splitI ibox55 0 1377358126026746874809715040715088160647806976000000000000 true
private noncomputable def ibox60 : Fin 4 → FixedTape.I := splitI ibox59 0 1393373918189848582656339634211775232283246592000000000000 false
private noncomputable def ibox61 : Fin 4 → FixedTape.I := splitI ibox59 0 1393373918189848582656339634211775232283246592000000000000 true
private noncomputable def ibox62 : Fin 4 → FixedTape.I := splitI ibox54 3 239069550656212082142034748405358037240381440000000000000000 true
private noncomputable def ibox63 : Fin 4 → FixedTape.I := splitI ibox62 0 1377358126026746874809715040715088160647806976000000000000 false
private noncomputable def ibox64 : Fin 4 → FixedTape.I := splitI ibox63 0 1361342333863645166963090447218401089012367360000000000000 false
private noncomputable def ibox65 : Fin 4 → FixedTape.I := splitI ibox63 0 1361342333863645166963090447218401089012367360000000000000 true
private noncomputable def ibox66 : Fin 4 → FixedTape.I := splitI ibox62 0 1377358126026746874809715040715088160647806976000000000000 true
private noncomputable def ibox67 : Fin 4 → FixedTape.I := splitI ibox66 0 1393373918189848582656339634211775232283246592000000000000 false
private noncomputable def ibox68 : Fin 4 → FixedTape.I := splitI ibox66 0 1393373918189848582656339634211775232283246592000000000000 true
private noncomputable def ibox69 : Fin 4 → FixedTape.I := splitI ibox37 3 478139101312424164284069496810716074480762880000000000000000 true
private noncomputable def ibox70 : Fin 4 → FixedTape.I := splitI ibox69 0 1345326541700543459116465853721714017376927744000000000000 false
private noncomputable def ibox71 : Fin 4 → FixedTape.I := splitI ibox70 3 717208651968636246426104245216074111721144320000000000000000 false
private noncomputable def ibox72 : Fin 4 → FixedTape.I := splitI ibox71 0 1313294957374340043423216666728339874106048512000000000000 false
private noncomputable def ibox73 : Fin 4 → FixedTape.I := splitI ibox72 3 597673876640530205355086871013395093100953600000000000000000 false
private noncomputable def ibox74 : Fin 4 → FixedTape.I := splitI ibox72 3 597673876640530205355086871013395093100953600000000000000000 true
private noncomputable def ibox75 : Fin 4 → FixedTape.I := splitI ibox71 0 1313294957374340043423216666728339874106048512000000000000 true
private noncomputable def ibox76 : Fin 4 → FixedTape.I := splitI ibox75 3 597673876640530205355086871013395093100953600000000000000000 false
private noncomputable def ibox77 : Fin 4 → FixedTape.I := splitI ibox75 3 597673876640530205355086871013395093100953600000000000000000 true
private noncomputable def ibox78 : Fin 4 → FixedTape.I := splitI ibox70 3 717208651968636246426104245216074111721144320000000000000000 true
private noncomputable def ibox79 : Fin 4 → FixedTape.I := splitI ibox78 0 1313294957374340043423216666728339874106048512000000000000 false
private noncomputable def ibox80 : Fin 4 → FixedTape.I := splitI ibox79 3 836743427296742287497121619418753130341335040000000000000000 false
private noncomputable def ibox81 : Fin 4 → FixedTape.I := splitI ibox79 3 836743427296742287497121619418753130341335040000000000000000 true
private noncomputable def ibox82 : Fin 4 → FixedTape.I := splitI ibox78 0 1313294957374340043423216666728339874106048512000000000000 true
private noncomputable def ibox83 : Fin 4 → FixedTape.I := splitI ibox82 3 836743427296742287497121619418753130341335040000000000000000 false
private noncomputable def ibox84 : Fin 4 → FixedTape.I := splitI ibox82 3 836743427296742287497121619418753130341335040000000000000000 true
private noncomputable def ibox85 : Fin 4 → FixedTape.I := splitI ibox69 0 1345326541700543459116465853721714017376927744000000000000 true
private noncomputable def ibox86 : Fin 4 → FixedTape.I := splitI ibox85 3 717208651968636246426104245216074111721144320000000000000000 false
private noncomputable def ibox87 : Fin 4 → FixedTape.I := splitI ibox86 0 1377358126026746874809715040715088160647806976000000000000 false
private noncomputable def ibox88 : Fin 4 → FixedTape.I := splitI ibox87 3 597673876640530205355086871013395093100953600000000000000000 false
private noncomputable def ibox89 : Fin 4 → FixedTape.I := splitI ibox87 3 597673876640530205355086871013395093100953600000000000000000 true
private noncomputable def ibox90 : Fin 4 → FixedTape.I := splitI ibox86 0 1377358126026746874809715040715088160647806976000000000000 true
private noncomputable def ibox91 : Fin 4 → FixedTape.I := splitI ibox90 3 597673876640530205355086871013395093100953600000000000000000 false
private noncomputable def ibox92 : Fin 4 → FixedTape.I := splitI ibox90 3 597673876640530205355086871013395093100953600000000000000000 true
private noncomputable def ibox93 : Fin 4 → FixedTape.I := splitI ibox85 3 717208651968636246426104245216074111721144320000000000000000 true
private noncomputable def ibox94 : Fin 4 → FixedTape.I := splitI ibox93 0 1377358126026746874809715040715088160647806976000000000000 false
private noncomputable def ibox95 : Fin 4 → FixedTape.I := splitI ibox94 3 836743427296742287497121619418753130341335040000000000000000 false
private noncomputable def ibox96 : Fin 4 → FixedTape.I := splitI ibox94 3 836743427296742287497121619418753130341335040000000000000000 true
private noncomputable def ibox97 : Fin 4 → FixedTape.I := splitI ibox93 0 1377358126026746874809715040715088160647806976000000000000 true
private noncomputable def ibox98 : Fin 4 → FixedTape.I := splitI ibox97 3 836743427296742287497121619418753130341335040000000000000000 false
private noncomputable def ibox99 : Fin 4 → FixedTape.I := splitI ibox97 3 836743427296742287497121619418753130341335040000000000000000 true
private noncomputable def ibox100 : Fin 4 → FixedTape.I := splitI ibox36 3 956278202624848328568138993621432148961525760000000000000000 true
private noncomputable def ibox101 : Fin 4 → FixedTape.I := splitI ibox100 3 1434417303937272492852208490432148223442288640000000000000000 false
private noncomputable def ibox102 : Fin 4 → FixedTape.I := splitI ibox101 0 1345326541700543459116465853721714017376927744000000000000 false
private noncomputable def ibox103 : Fin 4 → FixedTape.I := splitI ibox102 3 1195347753281060410710173742026790186201907200000000000000000 false
private noncomputable def ibox104 : Fin 4 → FixedTape.I := splitI ibox103 0 1313294957374340043423216666728339874106048512000000000000 false
private noncomputable def ibox105 : Fin 4 → FixedTape.I := splitI ibox104 3 1075812977952954369639156367824111167581716480000000000000000 false
private noncomputable def ibox106 : Fin 4 → FixedTape.I := splitI ibox104 3 1075812977952954369639156367824111167581716480000000000000000 true
private noncomputable def ibox107 : Fin 4 → FixedTape.I := splitI ibox103 0 1313294957374340043423216666728339874106048512000000000000 true
private noncomputable def ibox108 : Fin 4 → FixedTape.I := splitI ibox107 3 1075812977952954369639156367824111167581716480000000000000000 false
private noncomputable def ibox109 : Fin 4 → FixedTape.I := splitI ibox107 3 1075812977952954369639156367824111167581716480000000000000000 true
private noncomputable def ibox110 : Fin 4 → FixedTape.I := splitI ibox102 3 1195347753281060410710173742026790186201907200000000000000000 true
private noncomputable def ibox111 : Fin 4 → FixedTape.I := splitI ibox110 0 1313294957374340043423216666728339874106048512000000000000 false
private noncomputable def ibox112 : Fin 4 → FixedTape.I := splitI ibox111 3 1314882528609166451781191116229469204822097920000000000000000 false
private noncomputable def ibox113 : Fin 4 → FixedTape.I := splitI ibox111 3 1314882528609166451781191116229469204822097920000000000000000 true
private noncomputable def ibox114 : Fin 4 → FixedTape.I := splitI ibox110 0 1313294957374340043423216666728339874106048512000000000000 true
private noncomputable def ibox115 : Fin 4 → FixedTape.I := splitI ibox114 3 1314882528609166451781191116229469204822097920000000000000000 false
private noncomputable def ibox116 : Fin 4 → FixedTape.I := splitI ibox114 3 1314882528609166451781191116229469204822097920000000000000000 true
private noncomputable def ibox117 : Fin 4 → FixedTape.I := splitI ibox101 0 1345326541700543459116465853721714017376927744000000000000 true
private noncomputable def ibox118 : Fin 4 → FixedTape.I := splitI ibox117 3 1195347753281060410710173742026790186201907200000000000000000 false
private noncomputable def ibox119 : Fin 4 → FixedTape.I := splitI ibox118 0 1377358126026746874809715040715088160647806976000000000000 false
private noncomputable def ibox120 : Fin 4 → FixedTape.I := splitI ibox119 3 1075812977952954369639156367824111167581716480000000000000000 false
private noncomputable def ibox121 : Fin 4 → FixedTape.I := splitI ibox119 3 1075812977952954369639156367824111167581716480000000000000000 true
private noncomputable def ibox122 : Fin 4 → FixedTape.I := splitI ibox118 0 1377358126026746874809715040715088160647806976000000000000 true
private noncomputable def ibox123 : Fin 4 → FixedTape.I := splitI ibox122 3 1075812977952954369639156367824111167581716480000000000000000 false
private noncomputable def ibox124 : Fin 4 → FixedTape.I := splitI ibox122 3 1075812977952954369639156367824111167581716480000000000000000 true
private noncomputable def ibox125 : Fin 4 → FixedTape.I := splitI ibox117 3 1195347753281060410710173742026790186201907200000000000000000 true
private noncomputable def ibox126 : Fin 4 → FixedTape.I := splitI ibox125 0 1377358126026746874809715040715088160647806976000000000000 false
private noncomputable def ibox127 : Fin 4 → FixedTape.I := splitI ibox126 3 1314882528609166451781191116229469204822097920000000000000000 false
private noncomputable def ibox128 : Fin 4 → FixedTape.I := splitI ibox126 3 1314882528609166451781191116229469204822097920000000000000000 true
private noncomputable def ibox129 : Fin 4 → FixedTape.I := splitI ibox125 0 1377358126026746874809715040715088160647806976000000000000 true
private noncomputable def ibox130 : Fin 4 → FixedTape.I := splitI ibox129 3 1314882528609166451781191116229469204822097920000000000000000 false
private noncomputable def ibox131 : Fin 4 → FixedTape.I := splitI ibox129 3 1314882528609166451781191116229469204822097920000000000000000 true
private noncomputable def ibox132 : Fin 4 → FixedTape.I := splitI ibox100 3 1434417303937272492852208490432148223442288640000000000000000 true
private noncomputable def ibox133 : Fin 4 → FixedTape.I := splitI ibox132 3 1673486854593484574994243238837506260682670080000000000000000 false
private noncomputable def ibox134 : Fin 4 → FixedTape.I := splitI ibox133 0 1345326541700543459116465853721714017376927744000000000000 false
private noncomputable def ibox135 : Fin 4 → FixedTape.I := splitI ibox134 0 1313294957374340043423216666728339874106048512000000000000 false
private noncomputable def ibox136 : Fin 4 → FixedTape.I := splitI ibox135 3 1553952079265378533923225864634827242062479360000000000000000 false
private noncomputable def ibox137 : Fin 4 → FixedTape.I := splitI ibox135 3 1553952079265378533923225864634827242062479360000000000000000 true
private noncomputable def ibox138 : Fin 4 → FixedTape.I := splitI ibox134 0 1313294957374340043423216666728339874106048512000000000000 true
private noncomputable def ibox139 : Fin 4 → FixedTape.I := splitI ibox138 3 1553952079265378533923225864634827242062479360000000000000000 false
private noncomputable def ibox140 : Fin 4 → FixedTape.I := splitI ibox138 3 1553952079265378533923225864634827242062479360000000000000000 true
private noncomputable def ibox141 : Fin 4 → FixedTape.I := splitI ibox133 0 1345326541700543459116465853721714017376927744000000000000 true
private noncomputable def ibox142 : Fin 4 → FixedTape.I := splitI ibox141 0 1377358126026746874809715040715088160647806976000000000000 false
private noncomputable def ibox143 : Fin 4 → FixedTape.I := splitI ibox142 3 1553952079265378533923225864634827242062479360000000000000000 false
private noncomputable def ibox144 : Fin 4 → FixedTape.I := splitI ibox142 3 1553952079265378533923225864634827242062479360000000000000000 true
private noncomputable def ibox145 : Fin 4 → FixedTape.I := splitI ibox141 0 1377358126026746874809715040715088160647806976000000000000 true
private noncomputable def ibox146 : Fin 4 → FixedTape.I := splitI ibox145 3 1553952079265378533923225864634827242062479360000000000000000 false
private noncomputable def ibox147 : Fin 4 → FixedTape.I := splitI ibox145 3 1553952079265378533923225864634827242062479360000000000000000 true
private noncomputable def ibox148 : Fin 4 → FixedTape.I := splitI ibox132 3 1673486854593484574994243238837506260682670080000000000000000 true
private noncomputable def ibox149 : Fin 4 → FixedTape.I := splitI ibox148 0 1345326541700543459116465853721714017376927744000000000000 false
private noncomputable def ibox150 : Fin 4 → FixedTape.I := splitI ibox149 3 1793021629921590616065260613040185279302860800000000000000000 false
private noncomputable def ibox151 : Fin 4 → FixedTape.I := splitI ibox150 0 1313294957374340043423216666728339874106048512000000000000 false
private noncomputable def ibox152 : Fin 4 → FixedTape.I := splitI ibox150 0 1313294957374340043423216666728339874106048512000000000000 true
private noncomputable def ibox153 : Fin 4 → FixedTape.I := splitI ibox149 3 1793021629921590616065260613040185279302860800000000000000000 true
private noncomputable def ibox154 : Fin 4 → FixedTape.I := splitI ibox153 0 1313294957374340043423216666728339874106048512000000000000 false
private noncomputable def ibox155 : Fin 4 → FixedTape.I := splitI ibox153 0 1313294957374340043423216666728339874106048512000000000000 true
private noncomputable def ibox156 : Fin 4 → FixedTape.I := splitI ibox148 0 1345326541700543459116465853721714017376927744000000000000 true
private noncomputable def ibox157 : Fin 4 → FixedTape.I := splitI ibox156 3 1793021629921590616065260613040185279302860800000000000000000 false
private noncomputable def ibox158 : Fin 4 → FixedTape.I := splitI ibox157 0 1377358126026746874809715040715088160647806976000000000000 false
private noncomputable def ibox159 : Fin 4 → FixedTape.I := splitI ibox157 0 1377358126026746874809715040715088160647806976000000000000 true
private noncomputable def ibox160 : Fin 4 → FixedTape.I := splitI ibox156 3 1793021629921590616065260613040185279302860800000000000000000 true
private noncomputable def ibox161 : Fin 4 → FixedTape.I := splitI ibox160 0 1377358126026746874809715040715088160647806976000000000000 false
private noncomputable def ibox162 : Fin 4 → FixedTape.I := splitI ibox160 0 1377358126026746874809715040715088160647806976000000000000 true
private noncomputable def ibox163 : Fin 4 → FixedTape.I := splitI ibox34 0 1409389710352950290502964227708462303918686208000000000000 true
private noncomputable def ibox164 : Fin 4 → FixedTape.I := faceI ibox163 1 false
private noncomputable def ibox165 : Fin 4 → FixedTape.I := splitI ibox164 3 956278202624848328568138993621432148961525760000000000000000 false
private noncomputable def ibox166 : Fin 4 → FixedTape.I := splitI ibox165 3 478139101312424164284069496810716074480762880000000000000000 false
private noncomputable def ibox167 : Fin 4 → FixedTape.I := splitI ibox166 0 1473452879005357121889462601695210590460444672000000000000 false
private noncomputable def ibox168 : Fin 4 → FixedTape.I := splitI ibox167 3 239069550656212082142034748405358037240381440000000000000000 false
private noncomputable def ibox169 : Fin 4 → FixedTape.I := splitI ibox168 0 1441421294679153706196213414701836447189565440000000000000 false
private noncomputable def ibox170 : Fin 4 → FixedTape.I := splitI ibox169 0 1425405502516051998349588821205149375554125824000000000000 false
private noncomputable def ibox171 : Fin 4 → FixedTape.I := splitI ibox169 0 1425405502516051998349588821205149375554125824000000000000 true
private noncomputable def ibox172 : Fin 4 → FixedTape.I := splitI ibox168 0 1441421294679153706196213414701836447189565440000000000000 true
private noncomputable def ibox173 : Fin 4 → FixedTape.I := splitI ibox172 0 1457437086842255414042838008198523518825005056000000000000 false
private noncomputable def ibox174 : Fin 4 → FixedTape.I := splitI ibox172 0 1457437086842255414042838008198523518825005056000000000000 true
private noncomputable def ibox175 : Fin 4 → FixedTape.I := splitI ibox167 3 239069550656212082142034748405358037240381440000000000000000 true
private noncomputable def ibox176 : Fin 4 → FixedTape.I := splitI ibox175 0 1441421294679153706196213414701836447189565440000000000000 false
private noncomputable def ibox177 : Fin 4 → FixedTape.I := splitI ibox176 3 358604325984318123213052122608037055860572160000000000000000 false
private noncomputable def ibox178 : Fin 4 → FixedTape.I := splitI ibox176 3 358604325984318123213052122608037055860572160000000000000000 true
private noncomputable def ibox179 : Fin 4 → FixedTape.I := splitI ibox175 0 1441421294679153706196213414701836447189565440000000000000 true
private noncomputable def ibox180 : Fin 4 → FixedTape.I := splitI ibox179 3 358604325984318123213052122608037055860572160000000000000000 false
private noncomputable def ibox181 : Fin 4 → FixedTape.I := splitI ibox179 3 358604325984318123213052122608037055860572160000000000000000 true
private noncomputable def ibox182 : Fin 4 → FixedTape.I := splitI ibox166 0 1473452879005357121889462601695210590460444672000000000000 true
private noncomputable def ibox183 : Fin 4 → FixedTape.I := splitI ibox182 3 239069550656212082142034748405358037240381440000000000000000 false
private noncomputable def ibox184 : Fin 4 → FixedTape.I := splitI ibox183 0 1505484463331560537582711788688584733731323904000000000000 false
private noncomputable def ibox185 : Fin 4 → FixedTape.I := splitI ibox184 0 1489468671168458829736087195191897662095884288000000000000 false
private noncomputable def ibox186 : Fin 4 → FixedTape.I := splitI ibox184 0 1489468671168458829736087195191897662095884288000000000000 true
private noncomputable def ibox187 : Fin 4 → FixedTape.I := splitI ibox183 0 1505484463331560537582711788688584733731323904000000000000 true
private noncomputable def ibox188 : Fin 4 → FixedTape.I := splitI ibox187 3 119534775328106041071017374202679018620190720000000000000000 false
private noncomputable def ibox189 : Fin 4 → FixedTape.I := splitI ibox187 3 119534775328106041071017374202679018620190720000000000000000 true
private noncomputable def ibox190 : Fin 4 → FixedTape.I := splitI ibox182 3 239069550656212082142034748405358037240381440000000000000000 true
private noncomputable def ibox191 : Fin 4 → FixedTape.I := splitI ibox190 0 1505484463331560537582711788688584733731323904000000000000 false
private noncomputable def ibox192 : Fin 4 → FixedTape.I := splitI ibox191 3 358604325984318123213052122608037055860572160000000000000000 false
private noncomputable def ibox193 : Fin 4 → FixedTape.I := splitI ibox191 3 358604325984318123213052122608037055860572160000000000000000 true
private noncomputable def ibox194 : Fin 4 → FixedTape.I := splitI ibox190 0 1505484463331560537582711788688584733731323904000000000000 true
private noncomputable def ibox195 : Fin 4 → FixedTape.I := splitI ibox194 3 358604325984318123213052122608037055860572160000000000000000 false
private noncomputable def ibox196 : Fin 4 → FixedTape.I := splitI ibox194 3 358604325984318123213052122608037055860572160000000000000000 true
private noncomputable def ibox197 : Fin 4 → FixedTape.I := splitI ibox165 3 478139101312424164284069496810716074480762880000000000000000 true
private noncomputable def ibox198 : Fin 4 → FixedTape.I := splitI ibox197 0 1473452879005357121889462601695210590460444672000000000000 false
private noncomputable def ibox199 : Fin 4 → FixedTape.I := splitI ibox198 3 717208651968636246426104245216074111721144320000000000000000 false
private noncomputable def ibox200 : Fin 4 → FixedTape.I := splitI ibox199 0 1441421294679153706196213414701836447189565440000000000000 false
private noncomputable def ibox201 : Fin 4 → FixedTape.I := splitI ibox200 3 597673876640530205355086871013395093100953600000000000000000 false
private noncomputable def ibox202 : Fin 4 → FixedTape.I := splitI ibox200 3 597673876640530205355086871013395093100953600000000000000000 true
private noncomputable def ibox203 : Fin 4 → FixedTape.I := splitI ibox199 0 1441421294679153706196213414701836447189565440000000000000 true
private noncomputable def ibox204 : Fin 4 → FixedTape.I := splitI ibox203 3 597673876640530205355086871013395093100953600000000000000000 false
private noncomputable def ibox205 : Fin 4 → FixedTape.I := splitI ibox203 3 597673876640530205355086871013395093100953600000000000000000 true
private noncomputable def ibox206 : Fin 4 → FixedTape.I := splitI ibox198 3 717208651968636246426104245216074111721144320000000000000000 true
private noncomputable def ibox207 : Fin 4 → FixedTape.I := splitI ibox206 0 1441421294679153706196213414701836447189565440000000000000 false
private noncomputable def ibox208 : Fin 4 → FixedTape.I := splitI ibox207 3 836743427296742287497121619418753130341335040000000000000000 false
private noncomputable def ibox209 : Fin 4 → FixedTape.I := splitI ibox207 3 836743427296742287497121619418753130341335040000000000000000 true
private noncomputable def ibox210 : Fin 4 → FixedTape.I := splitI ibox206 0 1441421294679153706196213414701836447189565440000000000000 true
private noncomputable def ibox211 : Fin 4 → FixedTape.I := splitI ibox210 3 836743427296742287497121619418753130341335040000000000000000 false
private noncomputable def ibox212 : Fin 4 → FixedTape.I := splitI ibox210 3 836743427296742287497121619418753130341335040000000000000000 true
private noncomputable def ibox213 : Fin 4 → FixedTape.I := splitI ibox197 0 1473452879005357121889462601695210590460444672000000000000 true
private noncomputable def ibox214 : Fin 4 → FixedTape.I := splitI ibox213 3 717208651968636246426104245216074111721144320000000000000000 false
private noncomputable def ibox215 : Fin 4 → FixedTape.I := splitI ibox214 0 1505484463331560537582711788688584733731323904000000000000 false
private noncomputable def ibox216 : Fin 4 → FixedTape.I := splitI ibox215 3 597673876640530205355086871013395093100953600000000000000000 false
private noncomputable def ibox217 : Fin 4 → FixedTape.I := splitI ibox215 3 597673876640530205355086871013395093100953600000000000000000 true
private noncomputable def ibox218 : Fin 4 → FixedTape.I := splitI ibox214 0 1505484463331560537582711788688584733731323904000000000000 true
private noncomputable def ibox219 : Fin 4 → FixedTape.I := splitI ibox218 3 597673876640530205355086871013395093100953600000000000000000 false
private noncomputable def ibox220 : Fin 4 → FixedTape.I := splitI ibox218 3 597673876640530205355086871013395093100953600000000000000000 true
private noncomputable def ibox221 : Fin 4 → FixedTape.I := splitI ibox213 3 717208651968636246426104245216074111721144320000000000000000 true
private noncomputable def ibox222 : Fin 4 → FixedTape.I := splitI ibox221 0 1505484463331560537582711788688584733731323904000000000000 false
private noncomputable def ibox223 : Fin 4 → FixedTape.I := splitI ibox222 3 836743427296742287497121619418753130341335040000000000000000 false
private noncomputable def ibox224 : Fin 4 → FixedTape.I := splitI ibox222 3 836743427296742287497121619418753130341335040000000000000000 true
private noncomputable def ibox225 : Fin 4 → FixedTape.I := splitI ibox221 0 1505484463331560537582711788688584733731323904000000000000 true
private noncomputable def ibox226 : Fin 4 → FixedTape.I := splitI ibox225 3 836743427296742287497121619418753130341335040000000000000000 false
private noncomputable def ibox227 : Fin 4 → FixedTape.I := splitI ibox225 3 836743427296742287497121619418753130341335040000000000000000 true
private noncomputable def ibox228 : Fin 4 → FixedTape.I := splitI ibox164 3 956278202624848328568138993621432148961525760000000000000000 true
private noncomputable def ibox229 : Fin 4 → FixedTape.I := splitI ibox228 3 1434417303937272492852208490432148223442288640000000000000000 false
private noncomputable def ibox230 : Fin 4 → FixedTape.I := splitI ibox229 0 1473452879005357121889462601695210590460444672000000000000 false
private noncomputable def ibox231 : Fin 4 → FixedTape.I := splitI ibox230 3 1195347753281060410710173742026790186201907200000000000000000 false
private noncomputable def ibox232 : Fin 4 → FixedTape.I := splitI ibox231 0 1441421294679153706196213414701836447189565440000000000000 false
private noncomputable def ibox233 : Fin 4 → FixedTape.I := splitI ibox232 3 1075812977952954369639156367824111167581716480000000000000000 false
private noncomputable def ibox234 : Fin 4 → FixedTape.I := splitI ibox232 3 1075812977952954369639156367824111167581716480000000000000000 true
private noncomputable def ibox235 : Fin 4 → FixedTape.I := splitI ibox231 0 1441421294679153706196213414701836447189565440000000000000 true
private noncomputable def ibox236 : Fin 4 → FixedTape.I := splitI ibox235 3 1075812977952954369639156367824111167581716480000000000000000 false
private noncomputable def ibox237 : Fin 4 → FixedTape.I := splitI ibox235 3 1075812977952954369639156367824111167581716480000000000000000 true
private noncomputable def ibox238 : Fin 4 → FixedTape.I := splitI ibox230 3 1195347753281060410710173742026790186201907200000000000000000 true
private noncomputable def ibox239 : Fin 4 → FixedTape.I := splitI ibox238 0 1441421294679153706196213414701836447189565440000000000000 false
private noncomputable def ibox240 : Fin 4 → FixedTape.I := splitI ibox239 3 1314882528609166451781191116229469204822097920000000000000000 false
private noncomputable def ibox241 : Fin 4 → FixedTape.I := splitI ibox239 3 1314882528609166451781191116229469204822097920000000000000000 true
private noncomputable def ibox242 : Fin 4 → FixedTape.I := splitI ibox238 0 1441421294679153706196213414701836447189565440000000000000 true
private noncomputable def ibox243 : Fin 4 → FixedTape.I := splitI ibox242 3 1314882528609166451781191116229469204822097920000000000000000 false
private noncomputable def ibox244 : Fin 4 → FixedTape.I := splitI ibox242 3 1314882528609166451781191116229469204822097920000000000000000 true
private noncomputable def ibox245 : Fin 4 → FixedTape.I := splitI ibox229 0 1473452879005357121889462601695210590460444672000000000000 true
private noncomputable def ibox246 : Fin 4 → FixedTape.I := splitI ibox245 3 1195347753281060410710173742026790186201907200000000000000000 false
private noncomputable def ibox247 : Fin 4 → FixedTape.I := splitI ibox246 0 1505484463331560537582711788688584733731323904000000000000 false
private noncomputable def ibox248 : Fin 4 → FixedTape.I := splitI ibox247 3 1075812977952954369639156367824111167581716480000000000000000 false
private noncomputable def ibox249 : Fin 4 → FixedTape.I := splitI ibox247 3 1075812977952954369639156367824111167581716480000000000000000 true
private noncomputable def ibox250 : Fin 4 → FixedTape.I := splitI ibox246 0 1505484463331560537582711788688584733731323904000000000000 true
private noncomputable def ibox251 : Fin 4 → FixedTape.I := splitI ibox250 3 1075812977952954369639156367824111167581716480000000000000000 false
private noncomputable def ibox252 : Fin 4 → FixedTape.I := splitI ibox250 3 1075812977952954369639156367824111167581716480000000000000000 true
private noncomputable def ibox253 : Fin 4 → FixedTape.I := splitI ibox245 3 1195347753281060410710173742026790186201907200000000000000000 true
private noncomputable def ibox254 : Fin 4 → FixedTape.I := splitI ibox253 0 1505484463331560537582711788688584733731323904000000000000 false
private noncomputable def ibox255 : Fin 4 → FixedTape.I := splitI ibox254 3 1314882528609166451781191116229469204822097920000000000000000 false
private noncomputable def ibox256 : Fin 4 → FixedTape.I := splitI ibox254 3 1314882528609166451781191116229469204822097920000000000000000 true
private noncomputable def ibox257 : Fin 4 → FixedTape.I := splitI ibox253 0 1505484463331560537582711788688584733731323904000000000000 true
private noncomputable def ibox258 : Fin 4 → FixedTape.I := splitI ibox257 3 1314882528609166451781191116229469204822097920000000000000000 false
private noncomputable def ibox259 : Fin 4 → FixedTape.I := splitI ibox257 3 1314882528609166451781191116229469204822097920000000000000000 true
private noncomputable def ibox260 : Fin 4 → FixedTape.I := splitI ibox228 3 1434417303937272492852208490432148223442288640000000000000000 true
private noncomputable def ibox261 : Fin 4 → FixedTape.I := splitI ibox260 3 1673486854593484574994243238837506260682670080000000000000000 false
private noncomputable def ibox262 : Fin 4 → FixedTape.I := splitI ibox261 0 1473452879005357121889462601695210590460444672000000000000 false
private noncomputable def ibox263 : Fin 4 → FixedTape.I := splitI ibox262 0 1441421294679153706196213414701836447189565440000000000000 false
private noncomputable def ibox264 : Fin 4 → FixedTape.I := splitI ibox263 3 1553952079265378533923225864634827242062479360000000000000000 false
private noncomputable def ibox265 : Fin 4 → FixedTape.I := splitI ibox263 3 1553952079265378533923225864634827242062479360000000000000000 true
private noncomputable def ibox266 : Fin 4 → FixedTape.I := splitI ibox262 0 1441421294679153706196213414701836447189565440000000000000 true
private noncomputable def ibox267 : Fin 4 → FixedTape.I := splitI ibox266 3 1553952079265378533923225864634827242062479360000000000000000 false
private noncomputable def ibox268 : Fin 4 → FixedTape.I := splitI ibox266 3 1553952079265378533923225864634827242062479360000000000000000 true
private noncomputable def ibox269 : Fin 4 → FixedTape.I := splitI ibox261 0 1473452879005357121889462601695210590460444672000000000000 true
private noncomputable def ibox270 : Fin 4 → FixedTape.I := splitI ibox269 0 1505484463331560537582711788688584733731323904000000000000 false
private noncomputable def ibox271 : Fin 4 → FixedTape.I := splitI ibox270 3 1553952079265378533923225864634827242062479360000000000000000 false
private noncomputable def ibox272 : Fin 4 → FixedTape.I := splitI ibox270 3 1553952079265378533923225864634827242062479360000000000000000 true
private noncomputable def ibox273 : Fin 4 → FixedTape.I := splitI ibox269 0 1505484463331560537582711788688584733731323904000000000000 true
private noncomputable def ibox274 : Fin 4 → FixedTape.I := splitI ibox273 3 1553952079265378533923225864634827242062479360000000000000000 false
private noncomputable def ibox275 : Fin 4 → FixedTape.I := splitI ibox273 3 1553952079265378533923225864634827242062479360000000000000000 true
private noncomputable def ibox276 : Fin 4 → FixedTape.I := splitI ibox260 3 1673486854593484574994243238837506260682670080000000000000000 true
private noncomputable def ibox277 : Fin 4 → FixedTape.I := splitI ibox276 0 1473452879005357121889462601695210590460444672000000000000 false
private noncomputable def ibox278 : Fin 4 → FixedTape.I := splitI ibox277 3 1793021629921590616065260613040185279302860800000000000000000 false
private noncomputable def ibox279 : Fin 4 → FixedTape.I := splitI ibox278 0 1441421294679153706196213414701836447189565440000000000000 false
private noncomputable def ibox280 : Fin 4 → FixedTape.I := splitI ibox278 0 1441421294679153706196213414701836447189565440000000000000 true
private noncomputable def ibox281 : Fin 4 → FixedTape.I := splitI ibox277 3 1793021629921590616065260613040185279302860800000000000000000 true
private noncomputable def ibox282 : Fin 4 → FixedTape.I := splitI ibox281 0 1441421294679153706196213414701836447189565440000000000000 false
private noncomputable def ibox283 : Fin 4 → FixedTape.I := splitI ibox281 0 1441421294679153706196213414701836447189565440000000000000 true
private noncomputable def ibox284 : Fin 4 → FixedTape.I := splitI ibox276 0 1473452879005357121889462601695210590460444672000000000000 true
private noncomputable def ibox285 : Fin 4 → FixedTape.I := splitI ibox284 3 1793021629921590616065260613040185279302860800000000000000000 false
private noncomputable def ibox286 : Fin 4 → FixedTape.I := splitI ibox285 0 1505484463331560537582711788688584733731323904000000000000 false
private noncomputable def ibox287 : Fin 4 → FixedTape.I := splitI ibox285 0 1505484463331560537582711788688584733731323904000000000000 true
private noncomputable def ibox288 : Fin 4 → FixedTape.I := splitI ibox284 3 1793021629921590616065260613040185279302860800000000000000000 true
private noncomputable def ibox289 : Fin 4 → FixedTape.I := splitI ibox288 0 1505484463331560537582711788688584733731323904000000000000 false
private noncomputable def ibox290 : Fin 4 → FixedTape.I := splitI ibox288 0 1505484463331560537582711788688584733731323904000000000000 true
private noncomputable def ibox291 : Fin 4 → FixedTape.I := splitI ibox33 1 239069550656212082142034748405358037240381440000000000000000 true
private noncomputable def ibox292 : Fin 4 → FixedTape.I := splitI ibox291 0 1409389710352950290502964227708462303918686208000000000000 false
private noncomputable def ibox293 : Fin 4 → FixedTape.I := faceI ibox292 1 false
private noncomputable def ibox294 : Fin 4 → FixedTape.I := splitI ibox293 3 956278202624848328568138993621432148961525760000000000000000 false
private noncomputable def ibox295 : Fin 4 → FixedTape.I := splitI ibox293 3 956278202624848328568138993621432148961525760000000000000000 true
private noncomputable def ibox296 : Fin 4 → FixedTape.I := splitI ibox291 0 1409389710352950290502964227708462303918686208000000000000 true
private noncomputable def ibox297 : Fin 4 → FixedTape.I := faceI ibox296 1 false
private noncomputable def ibox298 : Fin 4 → FixedTape.I := splitI ibox297 3 956278202624848328568138993621432148961525760000000000000000 false
private noncomputable def ibox299 : Fin 4 → FixedTape.I := splitI ibox297 3 956278202624848328568138993621432148961525760000000000000000 true
private noncomputable def ibox300 : Fin 4 → FixedTape.I := splitI ibox32 1 478139101312424164284069496810716074480762880000000000000000 true
private noncomputable def ibox301 : Fin 4 → FixedTape.I := splitI ibox300 0 1409389710352950290502964227708462303918686208000000000000 false
private noncomputable def ibox302 : Fin 4 → FixedTape.I := faceI ibox301 1 false
private noncomputable def ibox303 : Fin 4 → FixedTape.I := splitI ibox300 0 1409389710352950290502964227708462303918686208000000000000 true
private noncomputable def ibox304 : Fin 4 → FixedTape.I := faceI ibox303 1 false
private noncomputable def ibox305 : Fin 4 → FixedTape.I := splitI ibox30 1 956278202624848328568138993621432148961525760000000000000000 true
private noncomputable def ibox306 : Fin 4 → FixedTape.I := faceI ibox305 3 false
private noncomputable def ibox307 : Fin 4 → FixedTape.I := splitI ibox306 0 1409389710352950290502964227708462303918686208000000000000 false
private noncomputable def ibox308 : Fin 4 → FixedTape.I := splitI ibox307 1 1434417303937272492852208490432148223442288640000000000000000 false
private noncomputable def ibox309 : Fin 4 → FixedTape.I := splitI ibox307 1 1434417303937272492852208490432148223442288640000000000000000 true
private noncomputable def ibox310 : Fin 4 → FixedTape.I := splitI ibox306 0 1409389710352950290502964227708462303918686208000000000000 true
private noncomputable def ibox311 : Fin 4 → FixedTape.I := splitI ibox310 1 1434417303937272492852208490432148223442288640000000000000000 false
private noncomputable def ibox312 : Fin 4 → FixedTape.I := splitI ibox310 1 1434417303937272492852208490432148223442288640000000000000000 true
private noncomputable def ibox313 : Fin 4 → FixedTape.I := splitI ibox19 0 1537516047657763953275960975681958877002203136000000000000 true
private noncomputable def ibox314 : Fin 4 → FixedTape.I := splitI ibox313 2 1434417303937272492852208490432148223442288640000000000000000 false
private noncomputable def ibox315 : Fin 4 → FixedTape.I := faceI ibox314 3 false
private noncomputable def ibox316 : Fin 4 → FixedTape.I := splitI ibox315 0 1665642384962577616048957723655455450085720064000000000000 false
private noncomputable def ibox317 : Fin 4 → FixedTape.I := splitI ibox316 1 956278202624848328568138993621432148961525760000000000000000 false
private noncomputable def ibox318 : Fin 4 → FixedTape.I := splitI ibox316 1 956278202624848328568138993621432148961525760000000000000000 true
private noncomputable def ibox319 : Fin 4 → FixedTape.I := splitI ibox315 0 1665642384962577616048957723655455450085720064000000000000 true
private noncomputable def ibox320 : Fin 4 → FixedTape.I := splitI ibox319 1 956278202624848328568138993621432148961525760000000000000000 false
private noncomputable def ibox321 : Fin 4 → FixedTape.I := splitI ibox319 1 956278202624848328568138993621432148961525760000000000000000 true
private noncomputable def ibox322 : Fin 4 → FixedTape.I := splitI ibox313 2 1434417303937272492852208490432148223442288640000000000000000 true
private noncomputable def ibox323 : Fin 4 → FixedTape.I := splitI ibox322 1 956278202624848328568138993621432148961525760000000000000000 false
private noncomputable def ibox324 : Fin 4 → FixedTape.I := faceI ibox323 2 true
private noncomputable def ibox325 : Fin 4 → FixedTape.I := splitI ibox324 1 478139101312424164284069496810716074480762880000000000000000 false
private noncomputable def ibox326 : Fin 4 → FixedTape.I := splitI ibox325 1 239069550656212082142034748405358037240381440000000000000000 false
private noncomputable def ibox327 : Fin 4 → FixedTape.I := splitI ibox326 0 1665642384962577616048957723655455450085720064000000000000 false
private noncomputable def ibox328 : Fin 4 → FixedTape.I := faceI ibox327 1 false
private noncomputable def ibox329 : Fin 4 → FixedTape.I := splitI ibox328 3 956278202624848328568138993621432148961525760000000000000000 false
private noncomputable def ibox330 : Fin 4 → FixedTape.I := splitI ibox329 3 478139101312424164284069496810716074480762880000000000000000 false
private noncomputable def ibox331 : Fin 4 → FixedTape.I := splitI ibox330 0 1601579216310170784662459349668707163543961600000000000000 false
private noncomputable def ibox332 : Fin 4 → FixedTape.I := splitI ibox331 3 239069550656212082142034748405358037240381440000000000000000 false
private noncomputable def ibox333 : Fin 4 → FixedTape.I := splitI ibox332 0 1569547631983967368969210162675333020273082368000000000000 false
private noncomputable def ibox334 : Fin 4 → FixedTape.I := splitI ibox333 3 119534775328106041071017374202679018620190720000000000000000 false
private noncomputable def ibox335 : Fin 4 → FixedTape.I := splitI ibox333 3 119534775328106041071017374202679018620190720000000000000000 true
private noncomputable def ibox336 : Fin 4 → FixedTape.I := splitI ibox332 0 1569547631983967368969210162675333020273082368000000000000 true
private noncomputable def ibox337 : Fin 4 → FixedTape.I := splitI ibox336 3 119534775328106041071017374202679018620190720000000000000000 false
private noncomputable def ibox338 : Fin 4 → FixedTape.I := splitI ibox336 3 119534775328106041071017374202679018620190720000000000000000 true
private noncomputable def ibox339 : Fin 4 → FixedTape.I := splitI ibox331 3 239069550656212082142034748405358037240381440000000000000000 true
private noncomputable def ibox340 : Fin 4 → FixedTape.I := splitI ibox339 0 1569547631983967368969210162675333020273082368000000000000 false
private noncomputable def ibox341 : Fin 4 → FixedTape.I := splitI ibox340 3 358604325984318123213052122608037055860572160000000000000000 false
private noncomputable def ibox342 : Fin 4 → FixedTape.I := splitI ibox340 3 358604325984318123213052122608037055860572160000000000000000 true
private noncomputable def ibox343 : Fin 4 → FixedTape.I := splitI ibox339 0 1569547631983967368969210162675333020273082368000000000000 true
private noncomputable def ibox344 : Fin 4 → FixedTape.I := splitI ibox343 3 358604325984318123213052122608037055860572160000000000000000 false
private noncomputable def ibox345 : Fin 4 → FixedTape.I := splitI ibox343 3 358604325984318123213052122608037055860572160000000000000000 true
private noncomputable def ibox346 : Fin 4 → FixedTape.I := splitI ibox330 0 1601579216310170784662459349668707163543961600000000000000 true
private noncomputable def ibox347 : Fin 4 → FixedTape.I := splitI ibox346 3 239069550656212082142034748405358037240381440000000000000000 false
private noncomputable def ibox348 : Fin 4 → FixedTape.I := splitI ibox347 0 1633610800636374200355708536662081306814840832000000000000 false
private noncomputable def ibox349 : Fin 4 → FixedTape.I := splitI ibox348 3 119534775328106041071017374202679018620190720000000000000000 false
private noncomputable def ibox350 : Fin 4 → FixedTape.I := splitI ibox348 3 119534775328106041071017374202679018620190720000000000000000 true
private noncomputable def ibox351 : Fin 4 → FixedTape.I := splitI ibox347 0 1633610800636374200355708536662081306814840832000000000000 true
private noncomputable def ibox352 : Fin 4 → FixedTape.I := splitI ibox351 3 119534775328106041071017374202679018620190720000000000000000 false
private noncomputable def ibox353 : Fin 4 → FixedTape.I := splitI ibox351 3 119534775328106041071017374202679018620190720000000000000000 true
private noncomputable def ibox354 : Fin 4 → FixedTape.I := splitI ibox346 3 239069550656212082142034748405358037240381440000000000000000 true
private noncomputable def ibox355 : Fin 4 → FixedTape.I := splitI ibox354 0 1633610800636374200355708536662081306814840832000000000000 false
private noncomputable def ibox356 : Fin 4 → FixedTape.I := splitI ibox355 3 358604325984318123213052122608037055860572160000000000000000 false
private noncomputable def ibox357 : Fin 4 → FixedTape.I := splitI ibox355 3 358604325984318123213052122608037055860572160000000000000000 true
private noncomputable def ibox358 : Fin 4 → FixedTape.I := splitI ibox354 0 1633610800636374200355708536662081306814840832000000000000 true
private noncomputable def ibox359 : Fin 4 → FixedTape.I := splitI ibox358 3 358604325984318123213052122608037055860572160000000000000000 false
private noncomputable def ibox360 : Fin 4 → FixedTape.I := splitI ibox358 3 358604325984318123213052122608037055860572160000000000000000 true
private noncomputable def ibox361 : Fin 4 → FixedTape.I := splitI ibox329 3 478139101312424164284069496810716074480762880000000000000000 true
private noncomputable def ibox362 : Fin 4 → FixedTape.I := splitI ibox361 0 1601579216310170784662459349668707163543961600000000000000 false
private noncomputable def ibox363 : Fin 4 → FixedTape.I := splitI ibox362 3 717208651968636246426104245216074111721144320000000000000000 false
private noncomputable def ibox364 : Fin 4 → FixedTape.I := splitI ibox363 0 1569547631983967368969210162675333020273082368000000000000 false
private noncomputable def ibox365 : Fin 4 → FixedTape.I := splitI ibox364 3 597673876640530205355086871013395093100953600000000000000000 false
private noncomputable def ibox366 : Fin 4 → FixedTape.I := splitI ibox364 3 597673876640530205355086871013395093100953600000000000000000 true
private noncomputable def ibox367 : Fin 4 → FixedTape.I := splitI ibox363 0 1569547631983967368969210162675333020273082368000000000000 true
private noncomputable def ibox368 : Fin 4 → FixedTape.I := splitI ibox367 3 597673876640530205355086871013395093100953600000000000000000 false
private noncomputable def ibox369 : Fin 4 → FixedTape.I := splitI ibox367 3 597673876640530205355086871013395093100953600000000000000000 true
private noncomputable def ibox370 : Fin 4 → FixedTape.I := splitI ibox362 3 717208651968636246426104245216074111721144320000000000000000 true
private noncomputable def ibox371 : Fin 4 → FixedTape.I := splitI ibox370 0 1569547631983967368969210162675333020273082368000000000000 false
private noncomputable def ibox372 : Fin 4 → FixedTape.I := splitI ibox371 3 836743427296742287497121619418753130341335040000000000000000 false
private noncomputable def ibox373 : Fin 4 → FixedTape.I := splitI ibox371 3 836743427296742287497121619418753130341335040000000000000000 true
private noncomputable def ibox374 : Fin 4 → FixedTape.I := splitI ibox370 0 1569547631983967368969210162675333020273082368000000000000 true
private noncomputable def ibox375 : Fin 4 → FixedTape.I := splitI ibox374 3 836743427296742287497121619418753130341335040000000000000000 false
private noncomputable def ibox376 : Fin 4 → FixedTape.I := splitI ibox374 3 836743427296742287497121619418753130341335040000000000000000 true
private noncomputable def ibox377 : Fin 4 → FixedTape.I := splitI ibox361 0 1601579216310170784662459349668707163543961600000000000000 true
private noncomputable def ibox378 : Fin 4 → FixedTape.I := splitI ibox377 3 717208651968636246426104245216074111721144320000000000000000 false
private noncomputable def ibox379 : Fin 4 → FixedTape.I := splitI ibox378 0 1633610800636374200355708536662081306814840832000000000000 false
private noncomputable def ibox380 : Fin 4 → FixedTape.I := splitI ibox379 3 597673876640530205355086871013395093100953600000000000000000 false
private noncomputable def ibox381 : Fin 4 → FixedTape.I := splitI ibox379 3 597673876640530205355086871013395093100953600000000000000000 true
private noncomputable def ibox382 : Fin 4 → FixedTape.I := splitI ibox378 0 1633610800636374200355708536662081306814840832000000000000 true
private noncomputable def ibox383 : Fin 4 → FixedTape.I := splitI ibox382 3 597673876640530205355086871013395093100953600000000000000000 false
private noncomputable def ibox384 : Fin 4 → FixedTape.I := splitI ibox382 3 597673876640530205355086871013395093100953600000000000000000 true
private noncomputable def ibox385 : Fin 4 → FixedTape.I := splitI ibox377 3 717208651968636246426104245216074111721144320000000000000000 true
private noncomputable def ibox386 : Fin 4 → FixedTape.I := splitI ibox385 0 1633610800636374200355708536662081306814840832000000000000 false
private noncomputable def ibox387 : Fin 4 → FixedTape.I := splitI ibox386 3 836743427296742287497121619418753130341335040000000000000000 false
private noncomputable def ibox388 : Fin 4 → FixedTape.I := splitI ibox386 3 836743427296742287497121619418753130341335040000000000000000 true
private noncomputable def ibox389 : Fin 4 → FixedTape.I := splitI ibox385 0 1633610800636374200355708536662081306814840832000000000000 true
private noncomputable def ibox390 : Fin 4 → FixedTape.I := splitI ibox389 3 836743427296742287497121619418753130341335040000000000000000 false
private noncomputable def ibox391 : Fin 4 → FixedTape.I := splitI ibox389 3 836743427296742287497121619418753130341335040000000000000000 true
private noncomputable def ibox392 : Fin 4 → FixedTape.I := splitI ibox328 3 956278202624848328568138993621432148961525760000000000000000 true
private noncomputable def ibox393 : Fin 4 → FixedTape.I := splitI ibox392 3 1434417303937272492852208490432148223442288640000000000000000 false
private noncomputable def ibox394 : Fin 4 → FixedTape.I := splitI ibox393 0 1601579216310170784662459349668707163543961600000000000000 false
private noncomputable def ibox395 : Fin 4 → FixedTape.I := splitI ibox394 3 1195347753281060410710173742026790186201907200000000000000000 false
private noncomputable def ibox396 : Fin 4 → FixedTape.I := splitI ibox395 0 1569547631983967368969210162675333020273082368000000000000 false
private noncomputable def ibox397 : Fin 4 → FixedTape.I := splitI ibox396 3 1075812977952954369639156367824111167581716480000000000000000 false
private noncomputable def ibox398 : Fin 4 → FixedTape.I := splitI ibox396 3 1075812977952954369639156367824111167581716480000000000000000 true
private noncomputable def ibox399 : Fin 4 → FixedTape.I := splitI ibox395 0 1569547631983967368969210162675333020273082368000000000000 true
private noncomputable def ibox400 : Fin 4 → FixedTape.I := splitI ibox399 3 1075812977952954369639156367824111167581716480000000000000000 false
private noncomputable def ibox401 : Fin 4 → FixedTape.I := splitI ibox399 3 1075812977952954369639156367824111167581716480000000000000000 true
private noncomputable def ibox402 : Fin 4 → FixedTape.I := splitI ibox394 3 1195347753281060410710173742026790186201907200000000000000000 true
private noncomputable def ibox403 : Fin 4 → FixedTape.I := splitI ibox402 0 1569547631983967368969210162675333020273082368000000000000 false
private noncomputable def ibox404 : Fin 4 → FixedTape.I := splitI ibox403 3 1314882528609166451781191116229469204822097920000000000000000 false
private noncomputable def ibox405 : Fin 4 → FixedTape.I := splitI ibox403 3 1314882528609166451781191116229469204822097920000000000000000 true
private noncomputable def ibox406 : Fin 4 → FixedTape.I := splitI ibox402 0 1569547631983967368969210162675333020273082368000000000000 true
private noncomputable def ibox407 : Fin 4 → FixedTape.I := splitI ibox406 3 1314882528609166451781191116229469204822097920000000000000000 false
private noncomputable def ibox408 : Fin 4 → FixedTape.I := splitI ibox406 3 1314882528609166451781191116229469204822097920000000000000000 true
private noncomputable def ibox409 : Fin 4 → FixedTape.I := splitI ibox393 0 1601579216310170784662459349668707163543961600000000000000 true
private noncomputable def ibox410 : Fin 4 → FixedTape.I := splitI ibox409 3 1195347753281060410710173742026790186201907200000000000000000 false
private noncomputable def ibox411 : Fin 4 → FixedTape.I := splitI ibox410 0 1633610800636374200355708536662081306814840832000000000000 false
private noncomputable def ibox412 : Fin 4 → FixedTape.I := splitI ibox411 3 1075812977952954369639156367824111167581716480000000000000000 false
private noncomputable def ibox413 : Fin 4 → FixedTape.I := splitI ibox411 3 1075812977952954369639156367824111167581716480000000000000000 true
private noncomputable def ibox414 : Fin 4 → FixedTape.I := splitI ibox410 0 1633610800636374200355708536662081306814840832000000000000 true
private noncomputable def ibox415 : Fin 4 → FixedTape.I := splitI ibox414 3 1075812977952954369639156367824111167581716480000000000000000 false
private noncomputable def ibox416 : Fin 4 → FixedTape.I := splitI ibox414 3 1075812977952954369639156367824111167581716480000000000000000 true
private noncomputable def ibox417 : Fin 4 → FixedTape.I := splitI ibox409 3 1195347753281060410710173742026790186201907200000000000000000 true
private noncomputable def ibox418 : Fin 4 → FixedTape.I := splitI ibox417 0 1633610800636374200355708536662081306814840832000000000000 false
private noncomputable def ibox419 : Fin 4 → FixedTape.I := splitI ibox418 3 1314882528609166451781191116229469204822097920000000000000000 false
private noncomputable def ibox420 : Fin 4 → FixedTape.I := splitI ibox418 3 1314882528609166451781191116229469204822097920000000000000000 true
private noncomputable def ibox421 : Fin 4 → FixedTape.I := splitI ibox417 0 1633610800636374200355708536662081306814840832000000000000 true
private noncomputable def ibox422 : Fin 4 → FixedTape.I := splitI ibox421 3 1314882528609166451781191116229469204822097920000000000000000 false
private noncomputable def ibox423 : Fin 4 → FixedTape.I := splitI ibox421 3 1314882528609166451781191116229469204822097920000000000000000 true
private noncomputable def ibox424 : Fin 4 → FixedTape.I := splitI ibox392 3 1434417303937272492852208490432148223442288640000000000000000 true
private noncomputable def ibox425 : Fin 4 → FixedTape.I := splitI ibox424 3 1673486854593484574994243238837506260682670080000000000000000 false
private noncomputable def ibox426 : Fin 4 → FixedTape.I := splitI ibox425 0 1601579216310170784662459349668707163543961600000000000000 false
private noncomputable def ibox427 : Fin 4 → FixedTape.I := splitI ibox426 0 1569547631983967368969210162675333020273082368000000000000 false
private noncomputable def ibox428 : Fin 4 → FixedTape.I := splitI ibox427 3 1553952079265378533923225864634827242062479360000000000000000 false
private noncomputable def ibox429 : Fin 4 → FixedTape.I := splitI ibox427 3 1553952079265378533923225864634827242062479360000000000000000 true
private noncomputable def ibox430 : Fin 4 → FixedTape.I := splitI ibox426 0 1569547631983967368969210162675333020273082368000000000000 true
private noncomputable def ibox431 : Fin 4 → FixedTape.I := splitI ibox430 3 1553952079265378533923225864634827242062479360000000000000000 false
private noncomputable def ibox432 : Fin 4 → FixedTape.I := splitI ibox430 3 1553952079265378533923225864634827242062479360000000000000000 true
private noncomputable def ibox433 : Fin 4 → FixedTape.I := splitI ibox425 0 1601579216310170784662459349668707163543961600000000000000 true
private noncomputable def ibox434 : Fin 4 → FixedTape.I := splitI ibox433 0 1633610800636374200355708536662081306814840832000000000000 false
private noncomputable def ibox435 : Fin 4 → FixedTape.I := splitI ibox434 3 1553952079265378533923225864634827242062479360000000000000000 false
private noncomputable def ibox436 : Fin 4 → FixedTape.I := splitI ibox434 3 1553952079265378533923225864634827242062479360000000000000000 true
private noncomputable def ibox437 : Fin 4 → FixedTape.I := splitI ibox433 0 1633610800636374200355708536662081306814840832000000000000 true
private noncomputable def ibox438 : Fin 4 → FixedTape.I := splitI ibox437 3 1553952079265378533923225864634827242062479360000000000000000 false
private noncomputable def ibox439 : Fin 4 → FixedTape.I := splitI ibox437 3 1553952079265378533923225864634827242062479360000000000000000 true
private noncomputable def ibox440 : Fin 4 → FixedTape.I := splitI ibox424 3 1673486854593484574994243238837506260682670080000000000000000 true
private noncomputable def ibox441 : Fin 4 → FixedTape.I := splitI ibox440 0 1601579216310170784662459349668707163543961600000000000000 false
private noncomputable def ibox442 : Fin 4 → FixedTape.I := splitI ibox441 3 1793021629921590616065260613040185279302860800000000000000000 false
private noncomputable def ibox443 : Fin 4 → FixedTape.I := splitI ibox442 0 1569547631983967368969210162675333020273082368000000000000 false
private noncomputable def ibox444 : Fin 4 → FixedTape.I := splitI ibox442 0 1569547631983967368969210162675333020273082368000000000000 true
private noncomputable def ibox445 : Fin 4 → FixedTape.I := splitI ibox441 3 1793021629921590616065260613040185279302860800000000000000000 true
private noncomputable def ibox446 : Fin 4 → FixedTape.I := splitI ibox445 0 1569547631983967368969210162675333020273082368000000000000 false
private noncomputable def ibox447 : Fin 4 → FixedTape.I := splitI ibox445 0 1569547631983967368969210162675333020273082368000000000000 true
private noncomputable def ibox448 : Fin 4 → FixedTape.I := splitI ibox440 0 1601579216310170784662459349668707163543961600000000000000 true
private noncomputable def ibox449 : Fin 4 → FixedTape.I := splitI ibox448 3 1793021629921590616065260613040185279302860800000000000000000 false
private noncomputable def ibox450 : Fin 4 → FixedTape.I := splitI ibox449 0 1633610800636374200355708536662081306814840832000000000000 false
private noncomputable def ibox451 : Fin 4 → FixedTape.I := splitI ibox449 0 1633610800636374200355708536662081306814840832000000000000 true
private noncomputable def ibox452 : Fin 4 → FixedTape.I := splitI ibox448 3 1793021629921590616065260613040185279302860800000000000000000 true
private noncomputable def ibox453 : Fin 4 → FixedTape.I := splitI ibox326 0 1665642384962577616048957723655455450085720064000000000000 true
private noncomputable def ibox454 : Fin 4 → FixedTape.I := faceI ibox453 1 false
private noncomputable def ibox455 : Fin 4 → FixedTape.I := splitI ibox454 3 956278202624848328568138993621432148961525760000000000000000 false
private noncomputable def ibox456 : Fin 4 → FixedTape.I := splitI ibox455 3 478139101312424164284069496810716074480762880000000000000000 false
private noncomputable def ibox457 : Fin 4 → FixedTape.I := splitI ibox456 0 1729705553614984447435456097642203736627478528000000000000 false
private noncomputable def ibox458 : Fin 4 → FixedTape.I := splitI ibox457 3 239069550656212082142034748405358037240381440000000000000000 false
private noncomputable def ibox459 : Fin 4 → FixedTape.I := splitI ibox458 0 1697673969288781031742206910648829593356599296000000000000 false
private noncomputable def ibox460 : Fin 4 → FixedTape.I := splitI ibox459 3 119534775328106041071017374202679018620190720000000000000000 false
private noncomputable def ibox461 : Fin 4 → FixedTape.I := splitI ibox459 3 119534775328106041071017374202679018620190720000000000000000 true
private noncomputable def ibox462 : Fin 4 → FixedTape.I := splitI ibox458 0 1697673969288781031742206910648829593356599296000000000000 true
private noncomputable def ibox463 : Fin 4 → FixedTape.I := splitI ibox462 3 119534775328106041071017374202679018620190720000000000000000 false
private noncomputable def ibox464 : Fin 4 → FixedTape.I := splitI ibox462 3 119534775328106041071017374202679018620190720000000000000000 true
private noncomputable def ibox465 : Fin 4 → FixedTape.I := splitI ibox457 3 239069550656212082142034748405358037240381440000000000000000 true
private noncomputable def ibox466 : Fin 4 → FixedTape.I := splitI ibox465 0 1697673969288781031742206910648829593356599296000000000000 false
private noncomputable def ibox467 : Fin 4 → FixedTape.I := splitI ibox466 3 358604325984318123213052122608037055860572160000000000000000 false
private noncomputable def ibox468 : Fin 4 → FixedTape.I := splitI ibox466 3 358604325984318123213052122608037055860572160000000000000000 true
private noncomputable def ibox469 : Fin 4 → FixedTape.I := splitI ibox465 0 1697673969288781031742206910648829593356599296000000000000 true
private noncomputable def ibox470 : Fin 4 → FixedTape.I := splitI ibox469 3 358604325984318123213052122608037055860572160000000000000000 false
private noncomputable def ibox471 : Fin 4 → FixedTape.I := splitI ibox469 3 358604325984318123213052122608037055860572160000000000000000 true
private noncomputable def ibox472 : Fin 4 → FixedTape.I := splitI ibox456 0 1729705553614984447435456097642203736627478528000000000000 true
private noncomputable def ibox473 : Fin 4 → FixedTape.I := splitI ibox472 3 239069550656212082142034748405358037240381440000000000000000 false
private noncomputable def ibox474 : Fin 4 → FixedTape.I := splitI ibox473 0 1761737137941187863128705284635577879898357760000000000000 false
private noncomputable def ibox475 : Fin 4 → FixedTape.I := splitI ibox473 0 1761737137941187863128705284635577879898357760000000000000 true
private noncomputable def ibox476 : Fin 4 → FixedTape.I := splitI ibox472 3 239069550656212082142034748405358037240381440000000000000000 true
private noncomputable def ibox477 : Fin 4 → FixedTape.I := splitI ibox476 0 1761737137941187863128705284635577879898357760000000000000 false
private noncomputable def ibox478 : Fin 4 → FixedTape.I := splitI ibox476 0 1761737137941187863128705284635577879898357760000000000000 true
private noncomputable def ibox479 : Fin 4 → FixedTape.I := splitI ibox455 3 478139101312424164284069496810716074480762880000000000000000 true
private noncomputable def ibox480 : Fin 4 → FixedTape.I := splitI ibox479 0 1729705553614984447435456097642203736627478528000000000000 false
private noncomputable def ibox481 : Fin 4 → FixedTape.I := splitI ibox480 3 717208651968636246426104245216074111721144320000000000000000 false
private noncomputable def ibox482 : Fin 4 → FixedTape.I := splitI ibox481 0 1697673969288781031742206910648829593356599296000000000000 false
private noncomputable def ibox483 : Fin 4 → FixedTape.I := splitI ibox482 3 597673876640530205355086871013395093100953600000000000000000 false
private noncomputable def ibox484 : Fin 4 → FixedTape.I := splitI ibox482 3 597673876640530205355086871013395093100953600000000000000000 true
private noncomputable def ibox485 : Fin 4 → FixedTape.I := splitI ibox481 0 1697673969288781031742206910648829593356599296000000000000 true
private noncomputable def ibox486 : Fin 4 → FixedTape.I := splitI ibox480 3 717208651968636246426104245216074111721144320000000000000000 true
private noncomputable def ibox487 : Fin 4 → FixedTape.I := splitI ibox486 0 1697673969288781031742206910648829593356599296000000000000 false
private noncomputable def ibox488 : Fin 4 → FixedTape.I := splitI ibox487 3 836743427296742287497121619418753130341335040000000000000000 false
private noncomputable def ibox489 : Fin 4 → FixedTape.I := splitI ibox487 3 836743427296742287497121619418753130341335040000000000000000 true
private noncomputable def ibox490 : Fin 4 → FixedTape.I := splitI ibox486 0 1697673969288781031742206910648829593356599296000000000000 true
private noncomputable def ibox491 : Fin 4 → FixedTape.I := splitI ibox479 0 1729705553614984447435456097642203736627478528000000000000 true
private noncomputable def ibox492 : Fin 4 → FixedTape.I := splitI ibox491 3 717208651968636246426104245216074111721144320000000000000000 false
private noncomputable def ibox493 : Fin 4 → FixedTape.I := splitI ibox492 0 1761737137941187863128705284635577879898357760000000000000 false
private noncomputable def ibox494 : Fin 4 → FixedTape.I := splitI ibox492 0 1761737137941187863128705284635577879898357760000000000000 true
private noncomputable def ibox495 : Fin 4 → FixedTape.I := splitI ibox491 3 717208651968636246426104245216074111721144320000000000000000 true
private noncomputable def ibox496 : Fin 4 → FixedTape.I := splitI ibox495 0 1761737137941187863128705284635577879898357760000000000000 false
private noncomputable def ibox497 : Fin 4 → FixedTape.I := splitI ibox495 0 1761737137941187863128705284635577879898357760000000000000 true
private noncomputable def ibox498 : Fin 4 → FixedTape.I := splitI ibox454 3 956278202624848328568138993621432148961525760000000000000000 true
private noncomputable def ibox499 : Fin 4 → FixedTape.I := splitI ibox498 3 1434417303937272492852208490432148223442288640000000000000000 false
private noncomputable def ibox500 : Fin 4 → FixedTape.I := splitI ibox499 0 1729705553614984447435456097642203736627478528000000000000 false
private noncomputable def ibox501 : Fin 4 → FixedTape.I := splitI ibox500 3 1195347753281060410710173742026790186201907200000000000000000 false
private noncomputable def ibox502 : Fin 4 → FixedTape.I := splitI ibox501 0 1697673969288781031742206910648829593356599296000000000000 false
private noncomputable def ibox503 : Fin 4 → FixedTape.I := splitI ibox502 3 1075812977952954369639156367824111167581716480000000000000000 false
private noncomputable def ibox504 : Fin 4 → FixedTape.I := splitI ibox502 3 1075812977952954369639156367824111167581716480000000000000000 true
private noncomputable def ibox505 : Fin 4 → FixedTape.I := splitI ibox501 0 1697673969288781031742206910648829593356599296000000000000 true
private noncomputable def ibox506 : Fin 4 → FixedTape.I := splitI ibox500 3 1195347753281060410710173742026790186201907200000000000000000 true
private noncomputable def ibox507 : Fin 4 → FixedTape.I := splitI ibox506 0 1697673969288781031742206910648829593356599296000000000000 false
private noncomputable def ibox508 : Fin 4 → FixedTape.I := splitI ibox507 3 1314882528609166451781191116229469204822097920000000000000000 false
private noncomputable def ibox509 : Fin 4 → FixedTape.I := splitI ibox507 3 1314882528609166451781191116229469204822097920000000000000000 true
private noncomputable def ibox510 : Fin 4 → FixedTape.I := splitI ibox506 0 1697673969288781031742206910648829593356599296000000000000 true
private noncomputable def ibox511 : Fin 4 → FixedTape.I := splitI ibox499 0 1729705553614984447435456097642203736627478528000000000000 true
private noncomputable def ibox512 : Fin 4 → FixedTape.I := splitI ibox511 3 1195347753281060410710173742026790186201907200000000000000000 false
private noncomputable def ibox513 : Fin 4 → FixedTape.I := splitI ibox512 0 1761737137941187863128705284635577879898357760000000000000 false
private noncomputable def ibox514 : Fin 4 → FixedTape.I := splitI ibox512 0 1761737137941187863128705284635577879898357760000000000000 true
private noncomputable def ibox515 : Fin 4 → FixedTape.I := splitI ibox511 3 1195347753281060410710173742026790186201907200000000000000000 true
private noncomputable def ibox516 : Fin 4 → FixedTape.I := splitI ibox515 0 1761737137941187863128705284635577879898357760000000000000 false
private noncomputable def ibox517 : Fin 4 → FixedTape.I := splitI ibox515 0 1761737137941187863128705284635577879898357760000000000000 true
private noncomputable def ibox518 : Fin 4 → FixedTape.I := splitI ibox498 3 1434417303937272492852208490432148223442288640000000000000000 true
private noncomputable def ibox519 : Fin 4 → FixedTape.I := splitI ibox518 3 1673486854593484574994243238837506260682670080000000000000000 false
private noncomputable def ibox520 : Fin 4 → FixedTape.I := splitI ibox519 0 1729705553614984447435456097642203736627478528000000000000 false
private noncomputable def ibox521 : Fin 4 → FixedTape.I := splitI ibox520 0 1697673969288781031742206910648829593356599296000000000000 false
private noncomputable def ibox522 : Fin 4 → FixedTape.I := splitI ibox520 0 1697673969288781031742206910648829593356599296000000000000 true
private noncomputable def ibox523 : Fin 4 → FixedTape.I := splitI ibox519 0 1729705553614984447435456097642203736627478528000000000000 true
private noncomputable def ibox524 : Fin 4 → FixedTape.I := splitI ibox523 0 1761737137941187863128705284635577879898357760000000000000 false
private noncomputable def ibox525 : Fin 4 → FixedTape.I := splitI ibox523 0 1761737137941187863128705284635577879898357760000000000000 true
private noncomputable def ibox526 : Fin 4 → FixedTape.I := splitI ibox518 3 1673486854593484574994243238837506260682670080000000000000000 true
private noncomputable def ibox527 : Fin 4 → FixedTape.I := splitI ibox526 0 1729705553614984447435456097642203736627478528000000000000 false
private noncomputable def ibox528 : Fin 4 → FixedTape.I := splitI ibox527 3 1793021629921590616065260613040185279302860800000000000000000 false
private noncomputable def ibox529 : Fin 4 → FixedTape.I := splitI ibox527 3 1793021629921590616065260613040185279302860800000000000000000 true
private noncomputable def ibox530 : Fin 4 → FixedTape.I := splitI ibox526 0 1729705553614984447435456097642203736627478528000000000000 true
private noncomputable def ibox531 : Fin 4 → FixedTape.I := splitI ibox530 3 1793021629921590616065260613040185279302860800000000000000000 false
private noncomputable def ibox532 : Fin 4 → FixedTape.I := splitI ibox530 3 1793021629921590616065260613040185279302860800000000000000000 true
private noncomputable def ibox533 : Fin 4 → FixedTape.I := splitI ibox325 1 239069550656212082142034748405358037240381440000000000000000 true
private noncomputable def ibox534 : Fin 4 → FixedTape.I := splitI ibox533 0 1665642384962577616048957723655455450085720064000000000000 false
private noncomputable def ibox535 : Fin 4 → FixedTape.I := faceI ibox534 1 false
private noncomputable def ibox536 : Fin 4 → FixedTape.I := splitI ibox535 3 956278202624848328568138993621432148961525760000000000000000 false
private noncomputable def ibox537 : Fin 4 → FixedTape.I := splitI ibox535 3 956278202624848328568138993621432148961525760000000000000000 true
private noncomputable def ibox538 : Fin 4 → FixedTape.I := splitI ibox533 0 1665642384962577616048957723655455450085720064000000000000 true
private noncomputable def ibox539 : Fin 4 → FixedTape.I := faceI ibox538 1 false
private noncomputable def ibox540 : Fin 4 → FixedTape.I := splitI ibox539 3 956278202624848328568138993621432148961525760000000000000000 false
private noncomputable def ibox541 : Fin 4 → FixedTape.I := splitI ibox539 3 956278202624848328568138993621432148961525760000000000000000 true
private noncomputable def ibox542 : Fin 4 → FixedTape.I := splitI ibox324 1 478139101312424164284069496810716074480762880000000000000000 true
private noncomputable def ibox543 : Fin 4 → FixedTape.I := splitI ibox542 0 1665642384962577616048957723655455450085720064000000000000 false
private noncomputable def ibox544 : Fin 4 → FixedTape.I := faceI ibox543 1 false
private noncomputable def ibox545 : Fin 4 → FixedTape.I := splitI ibox542 0 1665642384962577616048957723655455450085720064000000000000 true
private noncomputable def ibox546 : Fin 4 → FixedTape.I := faceI ibox545 1 false
private noncomputable def ibox547 : Fin 4 → FixedTape.I := splitI ibox322 1 956278202624848328568138993621432148961525760000000000000000 true
private noncomputable def ibox548 : Fin 4 → FixedTape.I := faceI ibox547 3 false
private noncomputable def ibox549 : Fin 4 → FixedTape.I := splitI ibox548 0 1665642384962577616048957723655455450085720064000000000000 false
private noncomputable def ibox550 : Fin 4 → FixedTape.I := splitI ibox549 1 1434417303937272492852208490432148223442288640000000000000000 false
private noncomputable def ibox551 : Fin 4 → FixedTape.I := splitI ibox549 1 1434417303937272492852208490432148223442288640000000000000000 true
private noncomputable def ibox552 : Fin 4 → FixedTape.I := splitI ibox548 0 1665642384962577616048957723655455450085720064000000000000 true
private noncomputable def ibox553 : Fin 4 → FixedTape.I := splitI ibox552 1 1434417303937272492852208490432148223442288640000000000000000 false
private noncomputable def ibox554 : Fin 4 → FixedTape.I := splitI ibox552 1 1434417303937272492852208490432148223442288640000000000000000 true
private noncomputable def tree554 : TapeTree := .centered (candidateRows ibox554) (candidateRows (FixedTape.midBox ibox554))
attribute [irreducible] tree554
private theorem sign_554 : 2*denominator*(computed denominator (FixedTape.midBox ibox554)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox554).gradient k).lo.natAbs ((computed denominator ibox554).gradient k).hi.natAbs : Int)*((ibox554 k).hi-(ibox554 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox554
    (computed denominator ibox554) (computed denominator (FixedTape.midBox ibox554))
    (by decide +kernel)
private theorem midpoint_even_554 : ∀ k, 2 ∣ (ibox554 k).lo+(ibox554 k).hi := by decide +kernel
private theorem accepted_554 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox554) tree554 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox554 midpoint_even_554
  simp only [tree554,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox554,candidate_valid h (FixedTape.midBox ibox554),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox554 212 (FixedTape.rowsAux denominator ibox554 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox554) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_554
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
private noncomputable def tree552 : TapeTree := .split 1 (((1434417303937272492852208490432148223442288640000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree553 tree554
attribute [irreducible] tree552
private theorem accepted_552 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox552) tree552 = true := by
  simp only [tree552,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox552 1 (1434417303937272492852208490432148223442288640000000000000000 : Int) false,decode_split denominator ibox552 1 (1434417303937272492852208490432148223442288640000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_553 h,accepted_554 h⟩
private noncomputable def tree551 : TapeTree := .centered (candidateRows ibox551) (candidateRows (FixedTape.midBox ibox551))
attribute [irreducible] tree551
private theorem sign_551 : 2*denominator*(computed denominator (FixedTape.midBox ibox551)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox551).gradient k).lo.natAbs ((computed denominator ibox551).gradient k).hi.natAbs : Int)*((ibox551 k).hi-(ibox551 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox551
    (computed denominator ibox551) (computed denominator (FixedTape.midBox ibox551))
    (by decide +kernel)
private theorem midpoint_even_551 : ∀ k, 2 ∣ (ibox551 k).lo+(ibox551 k).hi := by decide +kernel
private theorem accepted_551 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox551) tree551 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox551 midpoint_even_551
  simp only [tree551,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox551,candidate_valid h (FixedTape.midBox ibox551),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox551 212 (FixedTape.rowsAux denominator ibox551 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox551) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_551
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
private noncomputable def tree549 : TapeTree := .split 1 (((1434417303937272492852208490432148223442288640000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree550 tree551
attribute [irreducible] tree549
private theorem accepted_549 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox549) tree549 = true := by
  simp only [tree549,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox549 1 (1434417303937272492852208490432148223442288640000000000000000 : Int) false,decode_split denominator ibox549 1 (1434417303937272492852208490432148223442288640000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_550 h,accepted_551 h⟩
private noncomputable def tree548 : TapeTree := .split 0 (((1665642384962577616048957723655455450085720064000000000000 : Int) : ℚ)/(denominator : ℚ)) tree549 tree552
attribute [irreducible] tree548
private theorem accepted_548 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox548) tree548 = true := by
  simp only [tree548,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox548 0 (1665642384962577616048957723655455450085720064000000000000 : Int) false,decode_split denominator ibox548 0 (1665642384962577616048957723655455450085720064000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_549 h,accepted_552 h⟩
private noncomputable def tree547 : TapeTree := .face 3 false (candidateRows ibox547) tree548
attribute [irreducible] tree547
private theorem sign_547 : ((computed denominator ibox547).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_547 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox547) tree547 = true := by
  simp only [tree547,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox547,?_,accepted_548 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox547)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox547).gradient 3).hi) denominator_positive).1 sign_547
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
private noncomputable def tree545 : TapeTree := .face 1 false (candidateRows ibox545) tree546
attribute [irreducible] tree545
private theorem sign_545 : ((computed denominator ibox545).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_545 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox545) tree545 = true := by
  simp only [tree545,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox545,?_,accepted_546 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox545)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox545).gradient 1).hi) denominator_positive).1 sign_545
private noncomputable def tree544 : TapeTree := .centered (candidateRows ibox544) (candidateRows (FixedTape.midBox ibox544))
attribute [irreducible] tree544
private theorem sign_544 : 2*denominator*(computed denominator (FixedTape.midBox ibox544)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox544).gradient k).lo.natAbs ((computed denominator ibox544).gradient k).hi.natAbs : Int)*((ibox544 k).hi-(ibox544 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox544
    (computed denominator ibox544) (computed denominator (FixedTape.midBox ibox544))
    (by decide +kernel)
private theorem midpoint_even_544 : ∀ k, 2 ∣ (ibox544 k).lo+(ibox544 k).hi := by decide +kernel
private theorem accepted_544 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox544) tree544 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox544 midpoint_even_544
  simp only [tree544,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox544,candidate_valid h (FixedTape.midBox ibox544),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox544 212 (FixedTape.rowsAux denominator ibox544 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox544) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_544
private noncomputable def tree543 : TapeTree := .face 1 false (candidateRows ibox543) tree544
attribute [irreducible] tree543
private theorem sign_543 : ((computed denominator ibox543).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_543 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox543) tree543 = true := by
  simp only [tree543,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox543,?_,accepted_544 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox543)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox543).gradient 1).hi) denominator_positive).1 sign_543
private noncomputable def tree542 : TapeTree := .split 0 (((1665642384962577616048957723655455450085720064000000000000 : Int) : ℚ)/(denominator : ℚ)) tree543 tree545
attribute [irreducible] tree542
private theorem accepted_542 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox542) tree542 = true := by
  simp only [tree542,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox542 0 (1665642384962577616048957723655455450085720064000000000000 : Int) false,decode_split denominator ibox542 0 (1665642384962577616048957723655455450085720064000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_543 h,accepted_545 h⟩
private noncomputable def tree541 : TapeTree := .centered (candidateRows ibox541) (candidateRows (FixedTape.midBox ibox541))
attribute [irreducible] tree541
private theorem sign_541 : 2*denominator*(computed denominator (FixedTape.midBox ibox541)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox541).gradient k).lo.natAbs ((computed denominator ibox541).gradient k).hi.natAbs : Int)*((ibox541 k).hi-(ibox541 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox541
    (computed denominator ibox541) (computed denominator (FixedTape.midBox ibox541))
    (by decide +kernel)
private theorem midpoint_even_541 : ∀ k, 2 ∣ (ibox541 k).lo+(ibox541 k).hi := by decide +kernel
private theorem accepted_541 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox541) tree541 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox541 midpoint_even_541
  simp only [tree541,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox541,candidate_valid h (FixedTape.midBox ibox541),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox541 212 (FixedTape.rowsAux denominator ibox541 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox541) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_541
private noncomputable def tree540 : TapeTree := .centered (candidateRows ibox540) (candidateRows (FixedTape.midBox ibox540))
attribute [irreducible] tree540
private theorem sign_540 : 2*denominator*(computed denominator (FixedTape.midBox ibox540)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox540).gradient k).lo.natAbs ((computed denominator ibox540).gradient k).hi.natAbs : Int)*((ibox540 k).hi-(ibox540 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox540
    (computed denominator ibox540) (computed denominator (FixedTape.midBox ibox540))
    (by decide +kernel)
private theorem midpoint_even_540 : ∀ k, 2 ∣ (ibox540 k).lo+(ibox540 k).hi := by decide +kernel
private theorem accepted_540 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox540) tree540 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox540 midpoint_even_540
  simp only [tree540,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox540,candidate_valid h (FixedTape.midBox ibox540),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox540 212 (FixedTape.rowsAux denominator ibox540 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox540) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_540
private noncomputable def tree539 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree540 tree541
attribute [irreducible] tree539
private theorem accepted_539 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox539) tree539 = true := by
  simp only [tree539,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox539 3 (956278202624848328568138993621432148961525760000000000000000 : Int) false,decode_split denominator ibox539 3 (956278202624848328568138993621432148961525760000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_540 h,accepted_541 h⟩
private noncomputable def tree538 : TapeTree := .face 1 false (candidateRows ibox538) tree539
attribute [irreducible] tree538
private theorem sign_538 : ((computed denominator ibox538).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_538 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox538) tree538 = true := by
  simp only [tree538,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox538,?_,accepted_539 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox538)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox538).gradient 1).hi) denominator_positive).1 sign_538
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
private noncomputable def tree536 : TapeTree := .centered (candidateRows ibox536) (candidateRows (FixedTape.midBox ibox536))
attribute [irreducible] tree536
private theorem sign_536 : 2*denominator*(computed denominator (FixedTape.midBox ibox536)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox536).gradient k).lo.natAbs ((computed denominator ibox536).gradient k).hi.natAbs : Int)*((ibox536 k).hi-(ibox536 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox536
    (computed denominator ibox536) (computed denominator (FixedTape.midBox ibox536))
    (by decide +kernel)
private theorem midpoint_even_536 : ∀ k, 2 ∣ (ibox536 k).lo+(ibox536 k).hi := by decide +kernel
private theorem accepted_536 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox536) tree536 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox536 midpoint_even_536
  simp only [tree536,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox536,candidate_valid h (FixedTape.midBox ibox536),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox536 212 (FixedTape.rowsAux denominator ibox536 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox536) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_536
private noncomputable def tree535 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree536 tree537
attribute [irreducible] tree535
private theorem accepted_535 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox535) tree535 = true := by
  simp only [tree535,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox535 3 (956278202624848328568138993621432148961525760000000000000000 : Int) false,decode_split denominator ibox535 3 (956278202624848328568138993621432148961525760000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_536 h,accepted_537 h⟩
private noncomputable def tree534 : TapeTree := .face 1 false (candidateRows ibox534) tree535
attribute [irreducible] tree534
private theorem sign_534 : ((computed denominator ibox534).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_534 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox534) tree534 = true := by
  simp only [tree534,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox534,?_,accepted_535 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox534)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox534).gradient 1).hi) denominator_positive).1 sign_534
private noncomputable def tree533 : TapeTree := .split 0 (((1665642384962577616048957723655455450085720064000000000000 : Int) : ℚ)/(denominator : ℚ)) tree534 tree538
attribute [irreducible] tree533
private theorem accepted_533 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox533) tree533 = true := by
  simp only [tree533,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox533 0 (1665642384962577616048957723655455450085720064000000000000 : Int) false,decode_split denominator ibox533 0 (1665642384962577616048957723655455450085720064000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_534 h,accepted_538 h⟩
private noncomputable def tree532 : TapeTree := .centered (candidateRows ibox532) (candidateRows (FixedTape.midBox ibox532))
attribute [irreducible] tree532
private theorem sign_532 : 2*denominator*(computed denominator (FixedTape.midBox ibox532)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox532).gradient k).lo.natAbs ((computed denominator ibox532).gradient k).hi.natAbs : Int)*((ibox532 k).hi-(ibox532 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox532
    (computed denominator ibox532) (computed denominator (FixedTape.midBox ibox532))
    (by decide +kernel)
private theorem midpoint_even_532 : ∀ k, 2 ∣ (ibox532 k).lo+(ibox532 k).hi := by decide +kernel
private theorem accepted_532 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox532) tree532 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox532 midpoint_even_532
  simp only [tree532,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox532,candidate_valid h (FixedTape.midBox ibox532),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox532 212 (FixedTape.rowsAux denominator ibox532 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox532) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_532
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
private noncomputable def tree530 : TapeTree := .split 3 (((1793021629921590616065260613040185279302860800000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree531 tree532
attribute [irreducible] tree530
private theorem accepted_530 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox530) tree530 = true := by
  simp only [tree530,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox530 3 (1793021629921590616065260613040185279302860800000000000000000 : Int) false,decode_split denominator ibox530 3 (1793021629921590616065260613040185279302860800000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_531 h,accepted_532 h⟩
private noncomputable def tree529 : TapeTree := .centered (candidateRows ibox529) (candidateRows (FixedTape.midBox ibox529))
attribute [irreducible] tree529
private theorem sign_529 : 2*denominator*(computed denominator (FixedTape.midBox ibox529)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox529).gradient k).lo.natAbs ((computed denominator ibox529).gradient k).hi.natAbs : Int)*((ibox529 k).hi-(ibox529 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox529
    (computed denominator ibox529) (computed denominator (FixedTape.midBox ibox529))
    (by decide +kernel)
private theorem midpoint_even_529 : ∀ k, 2 ∣ (ibox529 k).lo+(ibox529 k).hi := by decide +kernel
private theorem accepted_529 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox529) tree529 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox529 midpoint_even_529
  simp only [tree529,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox529,candidate_valid h (FixedTape.midBox ibox529),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox529 212 (FixedTape.rowsAux denominator ibox529 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox529) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_529
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
private noncomputable def tree527 : TapeTree := .split 3 (((1793021629921590616065260613040185279302860800000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree528 tree529
attribute [irreducible] tree527
private theorem accepted_527 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox527) tree527 = true := by
  simp only [tree527,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox527 3 (1793021629921590616065260613040185279302860800000000000000000 : Int) false,decode_split denominator ibox527 3 (1793021629921590616065260613040185279302860800000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_528 h,accepted_529 h⟩
private noncomputable def tree526 : TapeTree := .split 0 (((1729705553614984447435456097642203736627478528000000000000 : Int) : ℚ)/(denominator : ℚ)) tree527 tree530
attribute [irreducible] tree526
private theorem accepted_526 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox526) tree526 = true := by
  simp only [tree526,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox526 0 (1729705553614984447435456097642203736627478528000000000000 : Int) false,decode_split denominator ibox526 0 (1729705553614984447435456097642203736627478528000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_527 h,accepted_530 h⟩
private noncomputable def tree525 : TapeTree := .centered (candidateRows ibox525) (candidateRows (FixedTape.midBox ibox525))
attribute [irreducible] tree525
private theorem sign_525 : 2*denominator*(computed denominator (FixedTape.midBox ibox525)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox525).gradient k).lo.natAbs ((computed denominator ibox525).gradient k).hi.natAbs : Int)*((ibox525 k).hi-(ibox525 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox525
    (computed denominator ibox525) (computed denominator (FixedTape.midBox ibox525))
    (by decide +kernel)
private theorem midpoint_even_525 : ∀ k, 2 ∣ (ibox525 k).lo+(ibox525 k).hi := by decide +kernel
private theorem accepted_525 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox525) tree525 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox525 midpoint_even_525
  simp only [tree525,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox525,candidate_valid h (FixedTape.midBox ibox525),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox525 212 (FixedTape.rowsAux denominator ibox525 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox525) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_525
private noncomputable def tree524 : TapeTree := .centered (candidateRows ibox524) (candidateRows (FixedTape.midBox ibox524))
attribute [irreducible] tree524
private theorem sign_524 : 2*denominator*(computed denominator (FixedTape.midBox ibox524)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox524).gradient k).lo.natAbs ((computed denominator ibox524).gradient k).hi.natAbs : Int)*((ibox524 k).hi-(ibox524 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox524
    (computed denominator ibox524) (computed denominator (FixedTape.midBox ibox524))
    (by decide +kernel)
private theorem midpoint_even_524 : ∀ k, 2 ∣ (ibox524 k).lo+(ibox524 k).hi := by decide +kernel
private theorem accepted_524 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox524) tree524 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox524 midpoint_even_524
  simp only [tree524,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox524,candidate_valid h (FixedTape.midBox ibox524),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox524 212 (FixedTape.rowsAux denominator ibox524 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox524) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_524
private noncomputable def tree523 : TapeTree := .split 0 (((1761737137941187863128705284635577879898357760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree524 tree525
attribute [irreducible] tree523
private theorem accepted_523 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox523) tree523 = true := by
  simp only [tree523,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox523 0 (1761737137941187863128705284635577879898357760000000000000 : Int) false,decode_split denominator ibox523 0 (1761737137941187863128705284635577879898357760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_524 h,accepted_525 h⟩
private noncomputable def tree522 : TapeTree := .centered (candidateRows ibox522) (candidateRows (FixedTape.midBox ibox522))
attribute [irreducible] tree522
private theorem sign_522 : 2*denominator*(computed denominator (FixedTape.midBox ibox522)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox522).gradient k).lo.natAbs ((computed denominator ibox522).gradient k).hi.natAbs : Int)*((ibox522 k).hi-(ibox522 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox522
    (computed denominator ibox522) (computed denominator (FixedTape.midBox ibox522))
    (by decide +kernel)
private theorem midpoint_even_522 : ∀ k, 2 ∣ (ibox522 k).lo+(ibox522 k).hi := by decide +kernel
private theorem accepted_522 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox522) tree522 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox522 midpoint_even_522
  simp only [tree522,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox522,candidate_valid h (FixedTape.midBox ibox522),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox522 212 (FixedTape.rowsAux denominator ibox522 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox522) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_522
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
private noncomputable def tree520 : TapeTree := .split 0 (((1697673969288781031742206910648829593356599296000000000000 : Int) : ℚ)/(denominator : ℚ)) tree521 tree522
attribute [irreducible] tree520
private theorem accepted_520 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox520) tree520 = true := by
  simp only [tree520,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox520 0 (1697673969288781031742206910648829593356599296000000000000 : Int) false,decode_split denominator ibox520 0 (1697673969288781031742206910648829593356599296000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_521 h,accepted_522 h⟩
private noncomputable def tree519 : TapeTree := .split 0 (((1729705553614984447435456097642203736627478528000000000000 : Int) : ℚ)/(denominator : ℚ)) tree520 tree523
attribute [irreducible] tree519
private theorem accepted_519 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox519) tree519 = true := by
  simp only [tree519,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox519 0 (1729705553614984447435456097642203736627478528000000000000 : Int) false,decode_split denominator ibox519 0 (1729705553614984447435456097642203736627478528000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_520 h,accepted_523 h⟩
private noncomputable def tree518 : TapeTree := .split 3 (((1673486854593484574994243238837506260682670080000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree519 tree526
attribute [irreducible] tree518
private theorem accepted_518 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox518) tree518 = true := by
  simp only [tree518,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox518 3 (1673486854593484574994243238837506260682670080000000000000000 : Int) false,decode_split denominator ibox518 3 (1673486854593484574994243238837506260682670080000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_519 h,accepted_526 h⟩
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
private noncomputable def tree516 : TapeTree := .centered (candidateRows ibox516) (candidateRows (FixedTape.midBox ibox516))
attribute [irreducible] tree516
private theorem sign_516 : 2*denominator*(computed denominator (FixedTape.midBox ibox516)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox516).gradient k).lo.natAbs ((computed denominator ibox516).gradient k).hi.natAbs : Int)*((ibox516 k).hi-(ibox516 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox516
    (computed denominator ibox516) (computed denominator (FixedTape.midBox ibox516))
    (by decide +kernel)
private theorem midpoint_even_516 : ∀ k, 2 ∣ (ibox516 k).lo+(ibox516 k).hi := by decide +kernel
private theorem accepted_516 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox516) tree516 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox516 midpoint_even_516
  simp only [tree516,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox516,candidate_valid h (FixedTape.midBox ibox516),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox516 212 (FixedTape.rowsAux denominator ibox516 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox516) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_516
private noncomputable def tree515 : TapeTree := .split 0 (((1761737137941187863128705284635577879898357760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree516 tree517
attribute [irreducible] tree515
private theorem accepted_515 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox515) tree515 = true := by
  simp only [tree515,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox515 0 (1761737137941187863128705284635577879898357760000000000000 : Int) false,decode_split denominator ibox515 0 (1761737137941187863128705284635577879898357760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_516 h,accepted_517 h⟩
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
private noncomputable def tree512 : TapeTree := .split 0 (((1761737137941187863128705284635577879898357760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree513 tree514
attribute [irreducible] tree512
private theorem accepted_512 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox512) tree512 = true := by
  simp only [tree512,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox512 0 (1761737137941187863128705284635577879898357760000000000000 : Int) false,decode_split denominator ibox512 0 (1761737137941187863128705284635577879898357760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_513 h,accepted_514 h⟩
private noncomputable def tree511 : TapeTree := .split 3 (((1195347753281060410710173742026790186201907200000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree512 tree515
attribute [irreducible] tree511
private theorem accepted_511 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox511) tree511 = true := by
  simp only [tree511,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox511 3 (1195347753281060410710173742026790186201907200000000000000000 : Int) false,decode_split denominator ibox511 3 (1195347753281060410710173742026790186201907200000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_512 h,accepted_515 h⟩
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
private noncomputable def tree509 : TapeTree := .centered (candidateRows ibox509) (candidateRows (FixedTape.midBox ibox509))
attribute [irreducible] tree509
private theorem sign_509 : 2*denominator*(computed denominator (FixedTape.midBox ibox509)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox509).gradient k).lo.natAbs ((computed denominator ibox509).gradient k).hi.natAbs : Int)*((ibox509 k).hi-(ibox509 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox509
    (computed denominator ibox509) (computed denominator (FixedTape.midBox ibox509))
    (by decide +kernel)
private theorem midpoint_even_509 : ∀ k, 2 ∣ (ibox509 k).lo+(ibox509 k).hi := by decide +kernel
private theorem accepted_509 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox509) tree509 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox509 midpoint_even_509
  simp only [tree509,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox509,candidate_valid h (FixedTape.midBox ibox509),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox509 212 (FixedTape.rowsAux denominator ibox509 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox509) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_509
private noncomputable def tree508 : TapeTree := .centered (candidateRows ibox508) (candidateRows (FixedTape.midBox ibox508))
attribute [irreducible] tree508
private theorem sign_508 : 2*denominator*(computed denominator (FixedTape.midBox ibox508)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox508).gradient k).lo.natAbs ((computed denominator ibox508).gradient k).hi.natAbs : Int)*((ibox508 k).hi-(ibox508 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox508
    (computed denominator ibox508) (computed denominator (FixedTape.midBox ibox508))
    (by decide +kernel)
private theorem midpoint_even_508 : ∀ k, 2 ∣ (ibox508 k).lo+(ibox508 k).hi := by decide +kernel
private theorem accepted_508 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox508) tree508 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox508 midpoint_even_508
  simp only [tree508,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox508,candidate_valid h (FixedTape.midBox ibox508),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox508 212 (FixedTape.rowsAux denominator ibox508 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox508) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_508
private noncomputable def tree507 : TapeTree := .split 3 (((1314882528609166451781191116229469204822097920000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree508 tree509
attribute [irreducible] tree507
private theorem accepted_507 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox507) tree507 = true := by
  simp only [tree507,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox507 3 (1314882528609166451781191116229469204822097920000000000000000 : Int) false,decode_split denominator ibox507 3 (1314882528609166451781191116229469204822097920000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_508 h,accepted_509 h⟩
private noncomputable def tree506 : TapeTree := .split 0 (((1697673969288781031742206910648829593356599296000000000000 : Int) : ℚ)/(denominator : ℚ)) tree507 tree510
attribute [irreducible] tree506
private theorem accepted_506 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox506) tree506 = true := by
  simp only [tree506,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox506 0 (1697673969288781031742206910648829593356599296000000000000 : Int) false,decode_split denominator ibox506 0 (1697673969288781031742206910648829593356599296000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_507 h,accepted_510 h⟩
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
private noncomputable def tree504 : TapeTree := .centered (candidateRows ibox504) (candidateRows (FixedTape.midBox ibox504))
attribute [irreducible] tree504
private theorem sign_504 : 2*denominator*(computed denominator (FixedTape.midBox ibox504)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox504).gradient k).lo.natAbs ((computed denominator ibox504).gradient k).hi.natAbs : Int)*((ibox504 k).hi-(ibox504 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox504
    (computed denominator ibox504) (computed denominator (FixedTape.midBox ibox504))
    (by decide +kernel)
private theorem midpoint_even_504 : ∀ k, 2 ∣ (ibox504 k).lo+(ibox504 k).hi := by decide +kernel
private theorem accepted_504 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox504) tree504 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox504 midpoint_even_504
  simp only [tree504,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox504,candidate_valid h (FixedTape.midBox ibox504),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox504 212 (FixedTape.rowsAux denominator ibox504 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox504) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_504
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
private noncomputable def tree502 : TapeTree := .split 3 (((1075812977952954369639156367824111167581716480000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree503 tree504
attribute [irreducible] tree502
private theorem accepted_502 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox502) tree502 = true := by
  simp only [tree502,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox502 3 (1075812977952954369639156367824111167581716480000000000000000 : Int) false,decode_split denominator ibox502 3 (1075812977952954369639156367824111167581716480000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_503 h,accepted_504 h⟩
private noncomputable def tree501 : TapeTree := .split 0 (((1697673969288781031742206910648829593356599296000000000000 : Int) : ℚ)/(denominator : ℚ)) tree502 tree505
attribute [irreducible] tree501
private theorem accepted_501 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox501) tree501 = true := by
  simp only [tree501,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox501 0 (1697673969288781031742206910648829593356599296000000000000 : Int) false,decode_split denominator ibox501 0 (1697673969288781031742206910648829593356599296000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_502 h,accepted_505 h⟩
private noncomputable def tree500 : TapeTree := .split 3 (((1195347753281060410710173742026790186201907200000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree501 tree506
attribute [irreducible] tree500
private theorem accepted_500 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox500) tree500 = true := by
  simp only [tree500,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox500 3 (1195347753281060410710173742026790186201907200000000000000000 : Int) false,decode_split denominator ibox500 3 (1195347753281060410710173742026790186201907200000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_501 h,accepted_506 h⟩
private noncomputable def tree499 : TapeTree := .split 0 (((1729705553614984447435456097642203736627478528000000000000 : Int) : ℚ)/(denominator : ℚ)) tree500 tree511
attribute [irreducible] tree499
private theorem accepted_499 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox499) tree499 = true := by
  simp only [tree499,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox499 0 (1729705553614984447435456097642203736627478528000000000000 : Int) false,decode_split denominator ibox499 0 (1729705553614984447435456097642203736627478528000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_500 h,accepted_511 h⟩
private noncomputable def tree498 : TapeTree := .split 3 (((1434417303937272492852208490432148223442288640000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree499 tree518
attribute [irreducible] tree498
private theorem accepted_498 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox498) tree498 = true := by
  simp only [tree498,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox498 3 (1434417303937272492852208490432148223442288640000000000000000 : Int) false,decode_split denominator ibox498 3 (1434417303937272492852208490432148223442288640000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_499 h,accepted_518 h⟩
private noncomputable def tree497 : TapeTree := .centered (candidateRows ibox497) (candidateRows (FixedTape.midBox ibox497))
attribute [irreducible] tree497
private theorem sign_497 : 2*denominator*(computed denominator (FixedTape.midBox ibox497)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox497).gradient k).lo.natAbs ((computed denominator ibox497).gradient k).hi.natAbs : Int)*((ibox497 k).hi-(ibox497 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox497
    (computed denominator ibox497) (computed denominator (FixedTape.midBox ibox497))
    (by decide +kernel)
private theorem midpoint_even_497 : ∀ k, 2 ∣ (ibox497 k).lo+(ibox497 k).hi := by decide +kernel
private theorem accepted_497 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox497) tree497 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox497 midpoint_even_497
  simp only [tree497,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox497,candidate_valid h (FixedTape.midBox ibox497),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox497 212 (FixedTape.rowsAux denominator ibox497 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox497) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_497
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
private noncomputable def tree495 : TapeTree := .split 0 (((1761737137941187863128705284635577879898357760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree496 tree497
attribute [irreducible] tree495
private theorem accepted_495 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox495) tree495 = true := by
  simp only [tree495,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox495 0 (1761737137941187863128705284635577879898357760000000000000 : Int) false,decode_split denominator ibox495 0 (1761737137941187863128705284635577879898357760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_496 h,accepted_497 h⟩
private noncomputable def tree494 : TapeTree := .centered (candidateRows ibox494) (candidateRows (FixedTape.midBox ibox494))
attribute [irreducible] tree494
private theorem sign_494 : 2*denominator*(computed denominator (FixedTape.midBox ibox494)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox494).gradient k).lo.natAbs ((computed denominator ibox494).gradient k).hi.natAbs : Int)*((ibox494 k).hi-(ibox494 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox494
    (computed denominator ibox494) (computed denominator (FixedTape.midBox ibox494))
    (by decide +kernel)
private theorem midpoint_even_494 : ∀ k, 2 ∣ (ibox494 k).lo+(ibox494 k).hi := by decide +kernel
private theorem accepted_494 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox494) tree494 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox494 midpoint_even_494
  simp only [tree494,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox494,candidate_valid h (FixedTape.midBox ibox494),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox494 212 (FixedTape.rowsAux denominator ibox494 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox494) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_494
private noncomputable def tree493 : TapeTree := .centered (candidateRows ibox493) (candidateRows (FixedTape.midBox ibox493))
attribute [irreducible] tree493
private theorem sign_493 : 2*denominator*(computed denominator (FixedTape.midBox ibox493)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox493).gradient k).lo.natAbs ((computed denominator ibox493).gradient k).hi.natAbs : Int)*((ibox493 k).hi-(ibox493 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox493
    (computed denominator ibox493) (computed denominator (FixedTape.midBox ibox493))
    (by decide +kernel)
private theorem midpoint_even_493 : ∀ k, 2 ∣ (ibox493 k).lo+(ibox493 k).hi := by decide +kernel
private theorem accepted_493 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox493) tree493 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox493 midpoint_even_493
  simp only [tree493,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox493,candidate_valid h (FixedTape.midBox ibox493),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox493 212 (FixedTape.rowsAux denominator ibox493 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox493) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_493
private noncomputable def tree492 : TapeTree := .split 0 (((1761737137941187863128705284635577879898357760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree493 tree494
attribute [irreducible] tree492
private theorem accepted_492 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox492) tree492 = true := by
  simp only [tree492,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox492 0 (1761737137941187863128705284635577879898357760000000000000 : Int) false,decode_split denominator ibox492 0 (1761737137941187863128705284635577879898357760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_493 h,accepted_494 h⟩
private noncomputable def tree491 : TapeTree := .split 3 (((717208651968636246426104245216074111721144320000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree492 tree495
attribute [irreducible] tree491
private theorem accepted_491 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox491) tree491 = true := by
  simp only [tree491,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox491 3 (717208651968636246426104245216074111721144320000000000000000 : Int) false,decode_split denominator ibox491 3 (717208651968636246426104245216074111721144320000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_492 h,accepted_495 h⟩
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
private noncomputable def tree488 : TapeTree := .centered (candidateRows ibox488) (candidateRows (FixedTape.midBox ibox488))
attribute [irreducible] tree488
private theorem sign_488 : 2*denominator*(computed denominator (FixedTape.midBox ibox488)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox488).gradient k).lo.natAbs ((computed denominator ibox488).gradient k).hi.natAbs : Int)*((ibox488 k).hi-(ibox488 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox488
    (computed denominator ibox488) (computed denominator (FixedTape.midBox ibox488))
    (by decide +kernel)
private theorem midpoint_even_488 : ∀ k, 2 ∣ (ibox488 k).lo+(ibox488 k).hi := by decide +kernel
private theorem accepted_488 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox488) tree488 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox488 midpoint_even_488
  simp only [tree488,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox488,candidate_valid h (FixedTape.midBox ibox488),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox488 212 (FixedTape.rowsAux denominator ibox488 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox488) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_488
private noncomputable def tree487 : TapeTree := .split 3 (((836743427296742287497121619418753130341335040000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree488 tree489
attribute [irreducible] tree487
private theorem accepted_487 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox487) tree487 = true := by
  simp only [tree487,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox487 3 (836743427296742287497121619418753130341335040000000000000000 : Int) false,decode_split denominator ibox487 3 (836743427296742287497121619418753130341335040000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_488 h,accepted_489 h⟩
private noncomputable def tree486 : TapeTree := .split 0 (((1697673969288781031742206910648829593356599296000000000000 : Int) : ℚ)/(denominator : ℚ)) tree487 tree490
attribute [irreducible] tree486
private theorem accepted_486 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox486) tree486 = true := by
  simp only [tree486,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox486 0 (1697673969288781031742206910648829593356599296000000000000 : Int) false,decode_split denominator ibox486 0 (1697673969288781031742206910648829593356599296000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_487 h,accepted_490 h⟩
private noncomputable def tree485 : TapeTree := .centered (candidateRows ibox485) (candidateRows (FixedTape.midBox ibox485))
attribute [irreducible] tree485
private theorem sign_485 : 2*denominator*(computed denominator (FixedTape.midBox ibox485)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox485).gradient k).lo.natAbs ((computed denominator ibox485).gradient k).hi.natAbs : Int)*((ibox485 k).hi-(ibox485 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox485
    (computed denominator ibox485) (computed denominator (FixedTape.midBox ibox485))
    (by decide +kernel)
private theorem midpoint_even_485 : ∀ k, 2 ∣ (ibox485 k).lo+(ibox485 k).hi := by decide +kernel
private theorem accepted_485 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox485) tree485 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox485 midpoint_even_485
  simp only [tree485,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox485,candidate_valid h (FixedTape.midBox ibox485),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox485 212 (FixedTape.rowsAux denominator ibox485 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox485) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_485
private noncomputable def tree484 : TapeTree := .centered (candidateRows ibox484) (candidateRows (FixedTape.midBox ibox484))
attribute [irreducible] tree484
private theorem sign_484 : 2*denominator*(computed denominator (FixedTape.midBox ibox484)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox484).gradient k).lo.natAbs ((computed denominator ibox484).gradient k).hi.natAbs : Int)*((ibox484 k).hi-(ibox484 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox484
    (computed denominator ibox484) (computed denominator (FixedTape.midBox ibox484))
    (by decide +kernel)
private theorem midpoint_even_484 : ∀ k, 2 ∣ (ibox484 k).lo+(ibox484 k).hi := by decide +kernel
private theorem accepted_484 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox484) tree484 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox484 midpoint_even_484
  simp only [tree484,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox484,candidate_valid h (FixedTape.midBox ibox484),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox484 212 (FixedTape.rowsAux denominator ibox484 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox484) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_484
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
private noncomputable def tree482 : TapeTree := .split 3 (((597673876640530205355086871013395093100953600000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree483 tree484
attribute [irreducible] tree482
private theorem accepted_482 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox482) tree482 = true := by
  simp only [tree482,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox482 3 (597673876640530205355086871013395093100953600000000000000000 : Int) false,decode_split denominator ibox482 3 (597673876640530205355086871013395093100953600000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_483 h,accepted_484 h⟩
private noncomputable def tree481 : TapeTree := .split 0 (((1697673969288781031742206910648829593356599296000000000000 : Int) : ℚ)/(denominator : ℚ)) tree482 tree485
attribute [irreducible] tree481
private theorem accepted_481 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox481) tree481 = true := by
  simp only [tree481,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox481 0 (1697673969288781031742206910648829593356599296000000000000 : Int) false,decode_split denominator ibox481 0 (1697673969288781031742206910648829593356599296000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_482 h,accepted_485 h⟩
private noncomputable def tree480 : TapeTree := .split 3 (((717208651968636246426104245216074111721144320000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree481 tree486
attribute [irreducible] tree480
private theorem accepted_480 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox480) tree480 = true := by
  simp only [tree480,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox480 3 (717208651968636246426104245216074111721144320000000000000000 : Int) false,decode_split denominator ibox480 3 (717208651968636246426104245216074111721144320000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_481 h,accepted_486 h⟩
private noncomputable def tree479 : TapeTree := .split 0 (((1729705553614984447435456097642203736627478528000000000000 : Int) : ℚ)/(denominator : ℚ)) tree480 tree491
attribute [irreducible] tree479
private theorem accepted_479 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox479) tree479 = true := by
  simp only [tree479,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox479 0 (1729705553614984447435456097642203736627478528000000000000 : Int) false,decode_split denominator ibox479 0 (1729705553614984447435456097642203736627478528000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_480 h,accepted_491 h⟩
private noncomputable def tree478 : TapeTree := .centered (candidateRows ibox478) (candidateRows (FixedTape.midBox ibox478))
attribute [irreducible] tree478
private theorem sign_478 : 2*denominator*(computed denominator (FixedTape.midBox ibox478)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox478).gradient k).lo.natAbs ((computed denominator ibox478).gradient k).hi.natAbs : Int)*((ibox478 k).hi-(ibox478 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox478
    (computed denominator ibox478) (computed denominator (FixedTape.midBox ibox478))
    (by decide +kernel)
private theorem midpoint_even_478 : ∀ k, 2 ∣ (ibox478 k).lo+(ibox478 k).hi := by decide +kernel
private theorem accepted_478 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox478) tree478 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox478 midpoint_even_478
  simp only [tree478,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox478,candidate_valid h (FixedTape.midBox ibox478),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox478 212 (FixedTape.rowsAux denominator ibox478 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox478) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_478
private noncomputable def tree477 : TapeTree := .centered (candidateRows ibox477) (candidateRows (FixedTape.midBox ibox477))
attribute [irreducible] tree477
private theorem sign_477 : 2*denominator*(computed denominator (FixedTape.midBox ibox477)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox477).gradient k).lo.natAbs ((computed denominator ibox477).gradient k).hi.natAbs : Int)*((ibox477 k).hi-(ibox477 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox477
    (computed denominator ibox477) (computed denominator (FixedTape.midBox ibox477))
    (by decide +kernel)
private theorem midpoint_even_477 : ∀ k, 2 ∣ (ibox477 k).lo+(ibox477 k).hi := by decide +kernel
private theorem accepted_477 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox477) tree477 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox477 midpoint_even_477
  simp only [tree477,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox477,candidate_valid h (FixedTape.midBox ibox477),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox477 212 (FixedTape.rowsAux denominator ibox477 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox477) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_477
private noncomputable def tree476 : TapeTree := .split 0 (((1761737137941187863128705284635577879898357760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree477 tree478
attribute [irreducible] tree476
private theorem accepted_476 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox476) tree476 = true := by
  simp only [tree476,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox476 0 (1761737137941187863128705284635577879898357760000000000000 : Int) false,decode_split denominator ibox476 0 (1761737137941187863128705284635577879898357760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_477 h,accepted_478 h⟩
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
private noncomputable def tree473 : TapeTree := .split 0 (((1761737137941187863128705284635577879898357760000000000000 : Int) : ℚ)/(denominator : ℚ)) tree474 tree475
attribute [irreducible] tree473
private theorem accepted_473 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox473) tree473 = true := by
  simp only [tree473,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox473 0 (1761737137941187863128705284635577879898357760000000000000 : Int) false,decode_split denominator ibox473 0 (1761737137941187863128705284635577879898357760000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_474 h,accepted_475 h⟩
private noncomputable def tree472 : TapeTree := .split 3 (((239069550656212082142034748405358037240381440000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree473 tree476
attribute [irreducible] tree472
private theorem accepted_472 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox472) tree472 = true := by
  simp only [tree472,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox472 3 (239069550656212082142034748405358037240381440000000000000000 : Int) false,decode_split denominator ibox472 3 (239069550656212082142034748405358037240381440000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_473 h,accepted_476 h⟩
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
private noncomputable def tree470 : TapeTree := .centered (candidateRows ibox470) (candidateRows (FixedTape.midBox ibox470))
attribute [irreducible] tree470
private theorem sign_470 : 2*denominator*(computed denominator (FixedTape.midBox ibox470)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox470).gradient k).lo.natAbs ((computed denominator ibox470).gradient k).hi.natAbs : Int)*((ibox470 k).hi-(ibox470 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox470
    (computed denominator ibox470) (computed denominator (FixedTape.midBox ibox470))
    (by decide +kernel)
private theorem midpoint_even_470 : ∀ k, 2 ∣ (ibox470 k).lo+(ibox470 k).hi := by decide +kernel
private theorem accepted_470 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox470) tree470 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox470 midpoint_even_470
  simp only [tree470,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox470,candidate_valid h (FixedTape.midBox ibox470),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox470 212 (FixedTape.rowsAux denominator ibox470 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox470) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_470
private noncomputable def tree469 : TapeTree := .split 3 (((358604325984318123213052122608037055860572160000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree470 tree471
attribute [irreducible] tree469
private theorem accepted_469 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox469) tree469 = true := by
  simp only [tree469,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox469 3 (358604325984318123213052122608037055860572160000000000000000 : Int) false,decode_split denominator ibox469 3 (358604325984318123213052122608037055860572160000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_470 h,accepted_471 h⟩
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
private noncomputable def tree466 : TapeTree := .split 3 (((358604325984318123213052122608037055860572160000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree467 tree468
attribute [irreducible] tree466
private theorem accepted_466 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox466) tree466 = true := by
  simp only [tree466,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox466 3 (358604325984318123213052122608037055860572160000000000000000 : Int) false,decode_split denominator ibox466 3 (358604325984318123213052122608037055860572160000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_467 h,accepted_468 h⟩
private noncomputable def tree465 : TapeTree := .split 0 (((1697673969288781031742206910648829593356599296000000000000 : Int) : ℚ)/(denominator : ℚ)) tree466 tree469
attribute [irreducible] tree465
private theorem accepted_465 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox465) tree465 = true := by
  simp only [tree465,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox465 0 (1697673969288781031742206910648829593356599296000000000000 : Int) false,decode_split denominator ibox465 0 (1697673969288781031742206910648829593356599296000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_466 h,accepted_469 h⟩
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
private noncomputable def tree463 : TapeTree := .centered (candidateRows ibox463) (candidateRows (FixedTape.midBox ibox463))
attribute [irreducible] tree463
private theorem sign_463 : 2*denominator*(computed denominator (FixedTape.midBox ibox463)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox463).gradient k).lo.natAbs ((computed denominator ibox463).gradient k).hi.natAbs : Int)*((ibox463 k).hi-(ibox463 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox463
    (computed denominator ibox463) (computed denominator (FixedTape.midBox ibox463))
    (by decide +kernel)
private theorem midpoint_even_463 : ∀ k, 2 ∣ (ibox463 k).lo+(ibox463 k).hi := by decide +kernel
private theorem accepted_463 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox463) tree463 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox463 midpoint_even_463
  simp only [tree463,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox463,candidate_valid h (FixedTape.midBox ibox463),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox463 212 (FixedTape.rowsAux denominator ibox463 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox463) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_463
private noncomputable def tree462 : TapeTree := .split 3 (((119534775328106041071017374202679018620190720000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree463 tree464
attribute [irreducible] tree462
private theorem accepted_462 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox462) tree462 = true := by
  simp only [tree462,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox462 3 (119534775328106041071017374202679018620190720000000000000000 : Int) false,decode_split denominator ibox462 3 (119534775328106041071017374202679018620190720000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_463 h,accepted_464 h⟩
private noncomputable def tree461 : TapeTree := .centered (candidateRows ibox461) (candidateRows (FixedTape.midBox ibox461))
attribute [irreducible] tree461
private theorem sign_461 : 2*denominator*(computed denominator (FixedTape.midBox ibox461)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox461).gradient k).lo.natAbs ((computed denominator ibox461).gradient k).hi.natAbs : Int)*((ibox461 k).hi-(ibox461 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox461
    (computed denominator ibox461) (computed denominator (FixedTape.midBox ibox461))
    (by decide +kernel)
private theorem midpoint_even_461 : ∀ k, 2 ∣ (ibox461 k).lo+(ibox461 k).hi := by decide +kernel
private theorem accepted_461 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox461) tree461 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox461 midpoint_even_461
  simp only [tree461,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox461,candidate_valid h (FixedTape.midBox ibox461),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox461 212 (FixedTape.rowsAux denominator ibox461 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox461) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_461
private noncomputable def tree460 : TapeTree := .centered (candidateRows ibox460) (candidateRows (FixedTape.midBox ibox460))
attribute [irreducible] tree460
private theorem sign_460 : 2*denominator*(computed denominator (FixedTape.midBox ibox460)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox460).gradient k).lo.natAbs ((computed denominator ibox460).gradient k).hi.natAbs : Int)*((ibox460 k).hi-(ibox460 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox460
    (computed denominator ibox460) (computed denominator (FixedTape.midBox ibox460))
    (by decide +kernel)
private theorem midpoint_even_460 : ∀ k, 2 ∣ (ibox460 k).lo+(ibox460 k).hi := by decide +kernel
private theorem accepted_460 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox460) tree460 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox460 midpoint_even_460
  simp only [tree460,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox460,candidate_valid h (FixedTape.midBox ibox460),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox460 212 (FixedTape.rowsAux denominator ibox460 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox460) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_460
private noncomputable def tree459 : TapeTree := .split 3 (((119534775328106041071017374202679018620190720000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree460 tree461
attribute [irreducible] tree459
private theorem accepted_459 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox459) tree459 = true := by
  simp only [tree459,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox459 3 (119534775328106041071017374202679018620190720000000000000000 : Int) false,decode_split denominator ibox459 3 (119534775328106041071017374202679018620190720000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_460 h,accepted_461 h⟩
private noncomputable def tree458 : TapeTree := .split 0 (((1697673969288781031742206910648829593356599296000000000000 : Int) : ℚ)/(denominator : ℚ)) tree459 tree462
attribute [irreducible] tree458
private theorem accepted_458 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox458) tree458 = true := by
  simp only [tree458,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox458 0 (1697673969288781031742206910648829593356599296000000000000 : Int) false,decode_split denominator ibox458 0 (1697673969288781031742206910648829593356599296000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_459 h,accepted_462 h⟩
private noncomputable def tree457 : TapeTree := .split 3 (((239069550656212082142034748405358037240381440000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree458 tree465
attribute [irreducible] tree457
private theorem accepted_457 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox457) tree457 = true := by
  simp only [tree457,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox457 3 (239069550656212082142034748405358037240381440000000000000000 : Int) false,decode_split denominator ibox457 3 (239069550656212082142034748405358037240381440000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_458 h,accepted_465 h⟩
private noncomputable def tree456 : TapeTree := .split 0 (((1729705553614984447435456097642203736627478528000000000000 : Int) : ℚ)/(denominator : ℚ)) tree457 tree472
attribute [irreducible] tree456
private theorem accepted_456 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox456) tree456 = true := by
  simp only [tree456,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox456 0 (1729705553614984447435456097642203736627478528000000000000 : Int) false,decode_split denominator ibox456 0 (1729705553614984447435456097642203736627478528000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_457 h,accepted_472 h⟩
private noncomputable def tree455 : TapeTree := .split 3 (((478139101312424164284069496810716074480762880000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree456 tree479
attribute [irreducible] tree455
private theorem accepted_455 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox455) tree455 = true := by
  simp only [tree455,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox455 3 (478139101312424164284069496810716074480762880000000000000000 : Int) false,decode_split denominator ibox455 3 (478139101312424164284069496810716074480762880000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_456 h,accepted_479 h⟩
private noncomputable def tree454 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree455 tree498
attribute [irreducible] tree454
private theorem accepted_454 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox454) tree454 = true := by
  simp only [tree454,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox454 3 (956278202624848328568138993621432148961525760000000000000000 : Int) false,decode_split denominator ibox454 3 (956278202624848328568138993621432148961525760000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_455 h,accepted_498 h⟩
private noncomputable def tree453 : TapeTree := .face 1 false (candidateRows ibox453) tree454
attribute [irreducible] tree453
private theorem sign_453 : ((computed denominator ibox453).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_453 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox453) tree453 = true := by
  simp only [tree453,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox453,?_,accepted_454 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox453)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox453).gradient 1).hi) denominator_positive).1 sign_453
private noncomputable def tree452 : TapeTree := .centered (candidateRows ibox452) (candidateRows (FixedTape.midBox ibox452))
attribute [irreducible] tree452
private theorem sign_452 : 2*denominator*(computed denominator (FixedTape.midBox ibox452)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox452).gradient k).lo.natAbs ((computed denominator ibox452).gradient k).hi.natAbs : Int)*((ibox452 k).hi-(ibox452 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox452
    (computed denominator ibox452) (computed denominator (FixedTape.midBox ibox452))
    (by decide +kernel)
private theorem midpoint_even_452 : ∀ k, 2 ∣ (ibox452 k).lo+(ibox452 k).hi := by decide +kernel
private theorem accepted_452 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox452) tree452 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox452 midpoint_even_452
  simp only [tree452,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox452,candidate_valid h (FixedTape.midBox ibox452),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox452 212 (FixedTape.rowsAux denominator ibox452 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox452) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_452
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
private noncomputable def tree449 : TapeTree := .split 0 (((1633610800636374200355708536662081306814840832000000000000 : Int) : ℚ)/(denominator : ℚ)) tree450 tree451
attribute [irreducible] tree449
private theorem accepted_449 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox449) tree449 = true := by
  simp only [tree449,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox449 0 (1633610800636374200355708536662081306814840832000000000000 : Int) false,decode_split denominator ibox449 0 (1633610800636374200355708536662081306814840832000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_450 h,accepted_451 h⟩
private noncomputable def tree448 : TapeTree := .split 3 (((1793021629921590616065260613040185279302860800000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree449 tree452
attribute [irreducible] tree448
private theorem accepted_448 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox448) tree448 = true := by
  simp only [tree448,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox448 3 (1793021629921590616065260613040185279302860800000000000000000 : Int) false,decode_split denominator ibox448 3 (1793021629921590616065260613040185279302860800000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_449 h,accepted_452 h⟩
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
private noncomputable def tree446 : TapeTree := .centered (candidateRows ibox446) (candidateRows (FixedTape.midBox ibox446))
attribute [irreducible] tree446
private theorem sign_446 : 2*denominator*(computed denominator (FixedTape.midBox ibox446)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox446).gradient k).lo.natAbs ((computed denominator ibox446).gradient k).hi.natAbs : Int)*((ibox446 k).hi-(ibox446 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox446
    (computed denominator ibox446) (computed denominator (FixedTape.midBox ibox446))
    (by decide +kernel)
private theorem midpoint_even_446 : ∀ k, 2 ∣ (ibox446 k).lo+(ibox446 k).hi := by decide +kernel
private theorem accepted_446 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox446) tree446 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox446 midpoint_even_446
  simp only [tree446,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox446,candidate_valid h (FixedTape.midBox ibox446),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox446 212 (FixedTape.rowsAux denominator ibox446 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox446) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_446
private noncomputable def tree445 : TapeTree := .split 0 (((1569547631983967368969210162675333020273082368000000000000 : Int) : ℚ)/(denominator : ℚ)) tree446 tree447
attribute [irreducible] tree445
private theorem accepted_445 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox445) tree445 = true := by
  simp only [tree445,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox445 0 (1569547631983967368969210162675333020273082368000000000000 : Int) false,decode_split denominator ibox445 0 (1569547631983967368969210162675333020273082368000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_446 h,accepted_447 h⟩
private noncomputable def tree444 : TapeTree := .centered (candidateRows ibox444) (candidateRows (FixedTape.midBox ibox444))
attribute [irreducible] tree444
private theorem sign_444 : 2*denominator*(computed denominator (FixedTape.midBox ibox444)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox444).gradient k).lo.natAbs ((computed denominator ibox444).gradient k).hi.natAbs : Int)*((ibox444 k).hi-(ibox444 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox444
    (computed denominator ibox444) (computed denominator (FixedTape.midBox ibox444))
    (by decide +kernel)
private theorem midpoint_even_444 : ∀ k, 2 ∣ (ibox444 k).lo+(ibox444 k).hi := by decide +kernel
private theorem accepted_444 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox444) tree444 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox444 midpoint_even_444
  simp only [tree444,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox444,candidate_valid h (FixedTape.midBox ibox444),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox444 212 (FixedTape.rowsAux denominator ibox444 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox444) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_444
private noncomputable def tree443 : TapeTree := .centered (candidateRows ibox443) (candidateRows (FixedTape.midBox ibox443))
attribute [irreducible] tree443
private theorem sign_443 : 2*denominator*(computed denominator (FixedTape.midBox ibox443)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox443).gradient k).lo.natAbs ((computed denominator ibox443).gradient k).hi.natAbs : Int)*((ibox443 k).hi-(ibox443 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox443
    (computed denominator ibox443) (computed denominator (FixedTape.midBox ibox443))
    (by decide +kernel)
private theorem midpoint_even_443 : ∀ k, 2 ∣ (ibox443 k).lo+(ibox443 k).hi := by decide +kernel
private theorem accepted_443 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox443) tree443 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox443 midpoint_even_443
  simp only [tree443,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox443,candidate_valid h (FixedTape.midBox ibox443),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox443 212 (FixedTape.rowsAux denominator ibox443 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox443) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_443
private noncomputable def tree442 : TapeTree := .split 0 (((1569547631983967368969210162675333020273082368000000000000 : Int) : ℚ)/(denominator : ℚ)) tree443 tree444
attribute [irreducible] tree442
private theorem accepted_442 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox442) tree442 = true := by
  simp only [tree442,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox442 0 (1569547631983967368969210162675333020273082368000000000000 : Int) false,decode_split denominator ibox442 0 (1569547631983967368969210162675333020273082368000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_443 h,accepted_444 h⟩
private noncomputable def tree441 : TapeTree := .split 3 (((1793021629921590616065260613040185279302860800000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree442 tree445
attribute [irreducible] tree441
private theorem accepted_441 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox441) tree441 = true := by
  simp only [tree441,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox441 3 (1793021629921590616065260613040185279302860800000000000000000 : Int) false,decode_split denominator ibox441 3 (1793021629921590616065260613040185279302860800000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_442 h,accepted_445 h⟩
private noncomputable def tree440 : TapeTree := .split 0 (((1601579216310170784662459349668707163543961600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree441 tree448
attribute [irreducible] tree440
private theorem accepted_440 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox440) tree440 = true := by
  simp only [tree440,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox440 0 (1601579216310170784662459349668707163543961600000000000000 : Int) false,decode_split denominator ibox440 0 (1601579216310170784662459349668707163543961600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_441 h,accepted_448 h⟩
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
private noncomputable def tree437 : TapeTree := .split 3 (((1553952079265378533923225864634827242062479360000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree438 tree439
attribute [irreducible] tree437
private theorem accepted_437 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox437) tree437 = true := by
  simp only [tree437,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox437 3 (1553952079265378533923225864634827242062479360000000000000000 : Int) false,decode_split denominator ibox437 3 (1553952079265378533923225864634827242062479360000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_438 h,accepted_439 h⟩
private noncomputable def tree436 : TapeTree := .centered (candidateRows ibox436) (candidateRows (FixedTape.midBox ibox436))
attribute [irreducible] tree436
private theorem sign_436 : 2*denominator*(computed denominator (FixedTape.midBox ibox436)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox436).gradient k).lo.natAbs ((computed denominator ibox436).gradient k).hi.natAbs : Int)*((ibox436 k).hi-(ibox436 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox436
    (computed denominator ibox436) (computed denominator (FixedTape.midBox ibox436))
    (by decide +kernel)
private theorem midpoint_even_436 : ∀ k, 2 ∣ (ibox436 k).lo+(ibox436 k).hi := by decide +kernel
private theorem accepted_436 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox436) tree436 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox436 midpoint_even_436
  simp only [tree436,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox436,candidate_valid h (FixedTape.midBox ibox436),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox436 212 (FixedTape.rowsAux denominator ibox436 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox436) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_436
private noncomputable def tree435 : TapeTree := .centered (candidateRows ibox435) (candidateRows (FixedTape.midBox ibox435))
attribute [irreducible] tree435
private theorem sign_435 : 2*denominator*(computed denominator (FixedTape.midBox ibox435)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox435).gradient k).lo.natAbs ((computed denominator ibox435).gradient k).hi.natAbs : Int)*((ibox435 k).hi-(ibox435 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox435
    (computed denominator ibox435) (computed denominator (FixedTape.midBox ibox435))
    (by decide +kernel)
private theorem midpoint_even_435 : ∀ k, 2 ∣ (ibox435 k).lo+(ibox435 k).hi := by decide +kernel
private theorem accepted_435 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox435) tree435 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox435 midpoint_even_435
  simp only [tree435,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox435,candidate_valid h (FixedTape.midBox ibox435),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox435 212 (FixedTape.rowsAux denominator ibox435 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox435) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_435
private noncomputable def tree434 : TapeTree := .split 3 (((1553952079265378533923225864634827242062479360000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree435 tree436
attribute [irreducible] tree434
private theorem accepted_434 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox434) tree434 = true := by
  simp only [tree434,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox434 3 (1553952079265378533923225864634827242062479360000000000000000 : Int) false,decode_split denominator ibox434 3 (1553952079265378533923225864634827242062479360000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_435 h,accepted_436 h⟩
private noncomputable def tree433 : TapeTree := .split 0 (((1633610800636374200355708536662081306814840832000000000000 : Int) : ℚ)/(denominator : ℚ)) tree434 tree437
attribute [irreducible] tree433
private theorem accepted_433 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox433) tree433 = true := by
  simp only [tree433,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox433 0 (1633610800636374200355708536662081306814840832000000000000 : Int) false,decode_split denominator ibox433 0 (1633610800636374200355708536662081306814840832000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_434 h,accepted_437 h⟩
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
private noncomputable def tree431 : TapeTree := .centered (candidateRows ibox431) (candidateRows (FixedTape.midBox ibox431))
attribute [irreducible] tree431
private theorem sign_431 : 2*denominator*(computed denominator (FixedTape.midBox ibox431)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox431).gradient k).lo.natAbs ((computed denominator ibox431).gradient k).hi.natAbs : Int)*((ibox431 k).hi-(ibox431 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox431
    (computed denominator ibox431) (computed denominator (FixedTape.midBox ibox431))
    (by decide +kernel)
private theorem midpoint_even_431 : ∀ k, 2 ∣ (ibox431 k).lo+(ibox431 k).hi := by decide +kernel
private theorem accepted_431 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox431) tree431 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox431 midpoint_even_431
  simp only [tree431,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox431,candidate_valid h (FixedTape.midBox ibox431),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox431 212 (FixedTape.rowsAux denominator ibox431 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox431) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_431
private noncomputable def tree430 : TapeTree := .split 3 (((1553952079265378533923225864634827242062479360000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree431 tree432
attribute [irreducible] tree430
private theorem accepted_430 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox430) tree430 = true := by
  simp only [tree430,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox430 3 (1553952079265378533923225864634827242062479360000000000000000 : Int) false,decode_split denominator ibox430 3 (1553952079265378533923225864634827242062479360000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_431 h,accepted_432 h⟩
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
private noncomputable def tree427 : TapeTree := .split 3 (((1553952079265378533923225864634827242062479360000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree428 tree429
attribute [irreducible] tree427
private theorem accepted_427 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox427) tree427 = true := by
  simp only [tree427,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox427 3 (1553952079265378533923225864634827242062479360000000000000000 : Int) false,decode_split denominator ibox427 3 (1553952079265378533923225864634827242062479360000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_428 h,accepted_429 h⟩
private noncomputable def tree426 : TapeTree := .split 0 (((1569547631983967368969210162675333020273082368000000000000 : Int) : ℚ)/(denominator : ℚ)) tree427 tree430
attribute [irreducible] tree426
private theorem accepted_426 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox426) tree426 = true := by
  simp only [tree426,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox426 0 (1569547631983967368969210162675333020273082368000000000000 : Int) false,decode_split denominator ibox426 0 (1569547631983967368969210162675333020273082368000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_427 h,accepted_430 h⟩
private noncomputable def tree425 : TapeTree := .split 0 (((1601579216310170784662459349668707163543961600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree426 tree433
attribute [irreducible] tree425
private theorem accepted_425 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox425) tree425 = true := by
  simp only [tree425,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox425 0 (1601579216310170784662459349668707163543961600000000000000 : Int) false,decode_split denominator ibox425 0 (1601579216310170784662459349668707163543961600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_426 h,accepted_433 h⟩
private noncomputable def tree424 : TapeTree := .split 3 (((1673486854593484574994243238837506260682670080000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree425 tree440
attribute [irreducible] tree424
private theorem accepted_424 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox424) tree424 = true := by
  simp only [tree424,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox424 3 (1673486854593484574994243238837506260682670080000000000000000 : Int) false,decode_split denominator ibox424 3 (1673486854593484574994243238837506260682670080000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_425 h,accepted_440 h⟩
private noncomputable def tree423 : TapeTree := .centered (candidateRows ibox423) (candidateRows (FixedTape.midBox ibox423))
attribute [irreducible] tree423
private theorem sign_423 : 2*denominator*(computed denominator (FixedTape.midBox ibox423)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox423).gradient k).lo.natAbs ((computed denominator ibox423).gradient k).hi.natAbs : Int)*((ibox423 k).hi-(ibox423 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox423
    (computed denominator ibox423) (computed denominator (FixedTape.midBox ibox423))
    (by decide +kernel)
private theorem midpoint_even_423 : ∀ k, 2 ∣ (ibox423 k).lo+(ibox423 k).hi := by decide +kernel
private theorem accepted_423 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox423) tree423 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox423 midpoint_even_423
  simp only [tree423,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox423,candidate_valid h (FixedTape.midBox ibox423),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox423 212 (FixedTape.rowsAux denominator ibox423 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox423) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_423
private noncomputable def tree422 : TapeTree := .centered (candidateRows ibox422) (candidateRows (FixedTape.midBox ibox422))
attribute [irreducible] tree422
private theorem sign_422 : 2*denominator*(computed denominator (FixedTape.midBox ibox422)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox422).gradient k).lo.natAbs ((computed denominator ibox422).gradient k).hi.natAbs : Int)*((ibox422 k).hi-(ibox422 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox422
    (computed denominator ibox422) (computed denominator (FixedTape.midBox ibox422))
    (by decide +kernel)
private theorem midpoint_even_422 : ∀ k, 2 ∣ (ibox422 k).lo+(ibox422 k).hi := by decide +kernel
private theorem accepted_422 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox422) tree422 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox422 midpoint_even_422
  simp only [tree422,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox422,candidate_valid h (FixedTape.midBox ibox422),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox422 212 (FixedTape.rowsAux denominator ibox422 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox422) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_422
private noncomputable def tree421 : TapeTree := .split 3 (((1314882528609166451781191116229469204822097920000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree422 tree423
attribute [irreducible] tree421
private theorem accepted_421 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox421) tree421 = true := by
  simp only [tree421,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox421 3 (1314882528609166451781191116229469204822097920000000000000000 : Int) false,decode_split denominator ibox421 3 (1314882528609166451781191116229469204822097920000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_422 h,accepted_423 h⟩
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
private noncomputable def tree418 : TapeTree := .split 3 (((1314882528609166451781191116229469204822097920000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree419 tree420
attribute [irreducible] tree418
private theorem accepted_418 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox418) tree418 = true := by
  simp only [tree418,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox418 3 (1314882528609166451781191116229469204822097920000000000000000 : Int) false,decode_split denominator ibox418 3 (1314882528609166451781191116229469204822097920000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_419 h,accepted_420 h⟩
private noncomputable def tree417 : TapeTree := .split 0 (((1633610800636374200355708536662081306814840832000000000000 : Int) : ℚ)/(denominator : ℚ)) tree418 tree421
attribute [irreducible] tree417
private theorem accepted_417 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox417) tree417 = true := by
  simp only [tree417,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox417 0 (1633610800636374200355708536662081306814840832000000000000 : Int) false,decode_split denominator ibox417 0 (1633610800636374200355708536662081306814840832000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_418 h,accepted_421 h⟩
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
private noncomputable def tree415 : TapeTree := .centered (candidateRows ibox415) (candidateRows (FixedTape.midBox ibox415))
attribute [irreducible] tree415
private theorem sign_415 : 2*denominator*(computed denominator (FixedTape.midBox ibox415)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox415).gradient k).lo.natAbs ((computed denominator ibox415).gradient k).hi.natAbs : Int)*((ibox415 k).hi-(ibox415 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox415
    (computed denominator ibox415) (computed denominator (FixedTape.midBox ibox415))
    (by decide +kernel)
private theorem midpoint_even_415 : ∀ k, 2 ∣ (ibox415 k).lo+(ibox415 k).hi := by decide +kernel
private theorem accepted_415 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox415) tree415 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox415 midpoint_even_415
  simp only [tree415,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox415,candidate_valid h (FixedTape.midBox ibox415),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox415 212 (FixedTape.rowsAux denominator ibox415 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox415) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_415
private noncomputable def tree414 : TapeTree := .split 3 (((1075812977952954369639156367824111167581716480000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree415 tree416
attribute [irreducible] tree414
private theorem accepted_414 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox414) tree414 = true := by
  simp only [tree414,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox414 3 (1075812977952954369639156367824111167581716480000000000000000 : Int) false,decode_split denominator ibox414 3 (1075812977952954369639156367824111167581716480000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_415 h,accepted_416 h⟩
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
private noncomputable def tree411 : TapeTree := .split 3 (((1075812977952954369639156367824111167581716480000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree412 tree413
attribute [irreducible] tree411
private theorem accepted_411 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox411) tree411 = true := by
  simp only [tree411,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox411 3 (1075812977952954369639156367824111167581716480000000000000000 : Int) false,decode_split denominator ibox411 3 (1075812977952954369639156367824111167581716480000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_412 h,accepted_413 h⟩
private noncomputable def tree410 : TapeTree := .split 0 (((1633610800636374200355708536662081306814840832000000000000 : Int) : ℚ)/(denominator : ℚ)) tree411 tree414
attribute [irreducible] tree410
private theorem accepted_410 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox410) tree410 = true := by
  simp only [tree410,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox410 0 (1633610800636374200355708536662081306814840832000000000000 : Int) false,decode_split denominator ibox410 0 (1633610800636374200355708536662081306814840832000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_411 h,accepted_414 h⟩
private noncomputable def tree409 : TapeTree := .split 3 (((1195347753281060410710173742026790186201907200000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree410 tree417
attribute [irreducible] tree409
private theorem accepted_409 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox409) tree409 = true := by
  simp only [tree409,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox409 3 (1195347753281060410710173742026790186201907200000000000000000 : Int) false,decode_split denominator ibox409 3 (1195347753281060410710173742026790186201907200000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_410 h,accepted_417 h⟩
private noncomputable def tree408 : TapeTree := .centered (candidateRows ibox408) (candidateRows (FixedTape.midBox ibox408))
attribute [irreducible] tree408
private theorem sign_408 : 2*denominator*(computed denominator (FixedTape.midBox ibox408)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox408).gradient k).lo.natAbs ((computed denominator ibox408).gradient k).hi.natAbs : Int)*((ibox408 k).hi-(ibox408 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox408
    (computed denominator ibox408) (computed denominator (FixedTape.midBox ibox408))
    (by decide +kernel)
private theorem midpoint_even_408 : ∀ k, 2 ∣ (ibox408 k).lo+(ibox408 k).hi := by decide +kernel
private theorem accepted_408 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox408) tree408 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox408 midpoint_even_408
  simp only [tree408,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox408,candidate_valid h (FixedTape.midBox ibox408),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox408 212 (FixedTape.rowsAux denominator ibox408 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox408) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_408
private noncomputable def tree407 : TapeTree := .centered (candidateRows ibox407) (candidateRows (FixedTape.midBox ibox407))
attribute [irreducible] tree407
private theorem sign_407 : 2*denominator*(computed denominator (FixedTape.midBox ibox407)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox407).gradient k).lo.natAbs ((computed denominator ibox407).gradient k).hi.natAbs : Int)*((ibox407 k).hi-(ibox407 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox407
    (computed denominator ibox407) (computed denominator (FixedTape.midBox ibox407))
    (by decide +kernel)
private theorem midpoint_even_407 : ∀ k, 2 ∣ (ibox407 k).lo+(ibox407 k).hi := by decide +kernel
private theorem accepted_407 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox407) tree407 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox407 midpoint_even_407
  simp only [tree407,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox407,candidate_valid h (FixedTape.midBox ibox407),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox407 212 (FixedTape.rowsAux denominator ibox407 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox407) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_407
private noncomputable def tree406 : TapeTree := .split 3 (((1314882528609166451781191116229469204822097920000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree407 tree408
attribute [irreducible] tree406
private theorem accepted_406 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox406) tree406 = true := by
  simp only [tree406,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox406 3 (1314882528609166451781191116229469204822097920000000000000000 : Int) false,decode_split denominator ibox406 3 (1314882528609166451781191116229469204822097920000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_407 h,accepted_408 h⟩
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
private noncomputable def tree403 : TapeTree := .split 3 (((1314882528609166451781191116229469204822097920000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree404 tree405
attribute [irreducible] tree403
private theorem accepted_403 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox403) tree403 = true := by
  simp only [tree403,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox403 3 (1314882528609166451781191116229469204822097920000000000000000 : Int) false,decode_split denominator ibox403 3 (1314882528609166451781191116229469204822097920000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_404 h,accepted_405 h⟩
private noncomputable def tree402 : TapeTree := .split 0 (((1569547631983967368969210162675333020273082368000000000000 : Int) : ℚ)/(denominator : ℚ)) tree403 tree406
attribute [irreducible] tree402
private theorem accepted_402 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox402) tree402 = true := by
  simp only [tree402,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox402 0 (1569547631983967368969210162675333020273082368000000000000 : Int) false,decode_split denominator ibox402 0 (1569547631983967368969210162675333020273082368000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_403 h,accepted_406 h⟩
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
private noncomputable def tree400 : TapeTree := .centered (candidateRows ibox400) (candidateRows (FixedTape.midBox ibox400))
attribute [irreducible] tree400
private theorem sign_400 : 2*denominator*(computed denominator (FixedTape.midBox ibox400)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox400).gradient k).lo.natAbs ((computed denominator ibox400).gradient k).hi.natAbs : Int)*((ibox400 k).hi-(ibox400 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox400
    (computed denominator ibox400) (computed denominator (FixedTape.midBox ibox400))
    (by decide +kernel)
private theorem midpoint_even_400 : ∀ k, 2 ∣ (ibox400 k).lo+(ibox400 k).hi := by decide +kernel
private theorem accepted_400 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox400) tree400 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox400 midpoint_even_400
  simp only [tree400,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox400,candidate_valid h (FixedTape.midBox ibox400),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox400 212 (FixedTape.rowsAux denominator ibox400 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox400) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_400
private noncomputable def tree399 : TapeTree := .split 3 (((1075812977952954369639156367824111167581716480000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree400 tree401
attribute [irreducible] tree399
private theorem accepted_399 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox399) tree399 = true := by
  simp only [tree399,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox399 3 (1075812977952954369639156367824111167581716480000000000000000 : Int) false,decode_split denominator ibox399 3 (1075812977952954369639156367824111167581716480000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_400 h,accepted_401 h⟩
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
private noncomputable def tree396 : TapeTree := .split 3 (((1075812977952954369639156367824111167581716480000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree397 tree398
attribute [irreducible] tree396
private theorem accepted_396 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox396) tree396 = true := by
  simp only [tree396,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox396 3 (1075812977952954369639156367824111167581716480000000000000000 : Int) false,decode_split denominator ibox396 3 (1075812977952954369639156367824111167581716480000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_397 h,accepted_398 h⟩
private noncomputable def tree395 : TapeTree := .split 0 (((1569547631983967368969210162675333020273082368000000000000 : Int) : ℚ)/(denominator : ℚ)) tree396 tree399
attribute [irreducible] tree395
private theorem accepted_395 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox395) tree395 = true := by
  simp only [tree395,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox395 0 (1569547631983967368969210162675333020273082368000000000000 : Int) false,decode_split denominator ibox395 0 (1569547631983967368969210162675333020273082368000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_396 h,accepted_399 h⟩
private noncomputable def tree394 : TapeTree := .split 3 (((1195347753281060410710173742026790186201907200000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree395 tree402
attribute [irreducible] tree394
private theorem accepted_394 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox394) tree394 = true := by
  simp only [tree394,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox394 3 (1195347753281060410710173742026790186201907200000000000000000 : Int) false,decode_split denominator ibox394 3 (1195347753281060410710173742026790186201907200000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_395 h,accepted_402 h⟩
private noncomputable def tree393 : TapeTree := .split 0 (((1601579216310170784662459349668707163543961600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree394 tree409
attribute [irreducible] tree393
private theorem accepted_393 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox393) tree393 = true := by
  simp only [tree393,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox393 0 (1601579216310170784662459349668707163543961600000000000000 : Int) false,decode_split denominator ibox393 0 (1601579216310170784662459349668707163543961600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_394 h,accepted_409 h⟩
private noncomputable def tree392 : TapeTree := .split 3 (((1434417303937272492852208490432148223442288640000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree393 tree424
attribute [irreducible] tree392
private theorem accepted_392 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox392) tree392 = true := by
  simp only [tree392,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox392 3 (1434417303937272492852208490432148223442288640000000000000000 : Int) false,decode_split denominator ibox392 3 (1434417303937272492852208490432148223442288640000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_393 h,accepted_424 h⟩
private noncomputable def tree391 : TapeTree := .centered (candidateRows ibox391) (candidateRows (FixedTape.midBox ibox391))
attribute [irreducible] tree391
private theorem sign_391 : 2*denominator*(computed denominator (FixedTape.midBox ibox391)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox391).gradient k).lo.natAbs ((computed denominator ibox391).gradient k).hi.natAbs : Int)*((ibox391 k).hi-(ibox391 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox391
    (computed denominator ibox391) (computed denominator (FixedTape.midBox ibox391))
    (by decide +kernel)
private theorem midpoint_even_391 : ∀ k, 2 ∣ (ibox391 k).lo+(ibox391 k).hi := by decide +kernel
private theorem accepted_391 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox391) tree391 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox391 midpoint_even_391
  simp only [tree391,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox391,candidate_valid h (FixedTape.midBox ibox391),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox391 212 (FixedTape.rowsAux denominator ibox391 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox391) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_391
private noncomputable def tree390 : TapeTree := .centered (candidateRows ibox390) (candidateRows (FixedTape.midBox ibox390))
attribute [irreducible] tree390
private theorem sign_390 : 2*denominator*(computed denominator (FixedTape.midBox ibox390)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox390).gradient k).lo.natAbs ((computed denominator ibox390).gradient k).hi.natAbs : Int)*((ibox390 k).hi-(ibox390 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox390
    (computed denominator ibox390) (computed denominator (FixedTape.midBox ibox390))
    (by decide +kernel)
private theorem midpoint_even_390 : ∀ k, 2 ∣ (ibox390 k).lo+(ibox390 k).hi := by decide +kernel
private theorem accepted_390 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox390) tree390 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox390 midpoint_even_390
  simp only [tree390,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox390,candidate_valid h (FixedTape.midBox ibox390),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox390 212 (FixedTape.rowsAux denominator ibox390 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox390) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_390
private noncomputable def tree389 : TapeTree := .split 3 (((836743427296742287497121619418753130341335040000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree390 tree391
attribute [irreducible] tree389
private theorem accepted_389 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox389) tree389 = true := by
  simp only [tree389,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox389 3 (836743427296742287497121619418753130341335040000000000000000 : Int) false,decode_split denominator ibox389 3 (836743427296742287497121619418753130341335040000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_390 h,accepted_391 h⟩
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
private noncomputable def tree387 : TapeTree := .centered (candidateRows ibox387) (candidateRows (FixedTape.midBox ibox387))
attribute [irreducible] tree387
private theorem sign_387 : 2*denominator*(computed denominator (FixedTape.midBox ibox387)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox387).gradient k).lo.natAbs ((computed denominator ibox387).gradient k).hi.natAbs : Int)*((ibox387 k).hi-(ibox387 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox387
    (computed denominator ibox387) (computed denominator (FixedTape.midBox ibox387))
    (by decide +kernel)
private theorem midpoint_even_387 : ∀ k, 2 ∣ (ibox387 k).lo+(ibox387 k).hi := by decide +kernel
private theorem accepted_387 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox387) tree387 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox387 midpoint_even_387
  simp only [tree387,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox387,candidate_valid h (FixedTape.midBox ibox387),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox387 212 (FixedTape.rowsAux denominator ibox387 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox387) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_387
private noncomputable def tree386 : TapeTree := .split 3 (((836743427296742287497121619418753130341335040000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree387 tree388
attribute [irreducible] tree386
private theorem accepted_386 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox386) tree386 = true := by
  simp only [tree386,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox386 3 (836743427296742287497121619418753130341335040000000000000000 : Int) false,decode_split denominator ibox386 3 (836743427296742287497121619418753130341335040000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_387 h,accepted_388 h⟩
private noncomputable def tree385 : TapeTree := .split 0 (((1633610800636374200355708536662081306814840832000000000000 : Int) : ℚ)/(denominator : ℚ)) tree386 tree389
attribute [irreducible] tree385
private theorem accepted_385 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox385) tree385 = true := by
  simp only [tree385,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox385 0 (1633610800636374200355708536662081306814840832000000000000 : Int) false,decode_split denominator ibox385 0 (1633610800636374200355708536662081306814840832000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_386 h,accepted_389 h⟩
private noncomputable def tree384 : TapeTree := .centered (candidateRows ibox384) (candidateRows (FixedTape.midBox ibox384))
attribute [irreducible] tree384
private theorem sign_384 : 2*denominator*(computed denominator (FixedTape.midBox ibox384)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox384).gradient k).lo.natAbs ((computed denominator ibox384).gradient k).hi.natAbs : Int)*((ibox384 k).hi-(ibox384 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox384
    (computed denominator ibox384) (computed denominator (FixedTape.midBox ibox384))
    (by decide +kernel)
private theorem midpoint_even_384 : ∀ k, 2 ∣ (ibox384 k).lo+(ibox384 k).hi := by decide +kernel
private theorem accepted_384 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox384) tree384 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox384 midpoint_even_384
  simp only [tree384,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox384,candidate_valid h (FixedTape.midBox ibox384),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox384 212 (FixedTape.rowsAux denominator ibox384 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox384) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_384
private noncomputable def tree383 : TapeTree := .centered (candidateRows ibox383) (candidateRows (FixedTape.midBox ibox383))
attribute [irreducible] tree383
private theorem sign_383 : 2*denominator*(computed denominator (FixedTape.midBox ibox383)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox383).gradient k).lo.natAbs ((computed denominator ibox383).gradient k).hi.natAbs : Int)*((ibox383 k).hi-(ibox383 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox383
    (computed denominator ibox383) (computed denominator (FixedTape.midBox ibox383))
    (by decide +kernel)
private theorem midpoint_even_383 : ∀ k, 2 ∣ (ibox383 k).lo+(ibox383 k).hi := by decide +kernel
private theorem accepted_383 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox383) tree383 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox383 midpoint_even_383
  simp only [tree383,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox383,candidate_valid h (FixedTape.midBox ibox383),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox383 212 (FixedTape.rowsAux denominator ibox383 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox383) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_383
private noncomputable def tree382 : TapeTree := .split 3 (((597673876640530205355086871013395093100953600000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree383 tree384
attribute [irreducible] tree382
private theorem accepted_382 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox382) tree382 = true := by
  simp only [tree382,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox382 3 (597673876640530205355086871013395093100953600000000000000000 : Int) false,decode_split denominator ibox382 3 (597673876640530205355086871013395093100953600000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_383 h,accepted_384 h⟩
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
private noncomputable def tree380 : TapeTree := .centered (candidateRows ibox380) (candidateRows (FixedTape.midBox ibox380))
attribute [irreducible] tree380
private theorem sign_380 : 2*denominator*(computed denominator (FixedTape.midBox ibox380)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox380).gradient k).lo.natAbs ((computed denominator ibox380).gradient k).hi.natAbs : Int)*((ibox380 k).hi-(ibox380 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox380
    (computed denominator ibox380) (computed denominator (FixedTape.midBox ibox380))
    (by decide +kernel)
private theorem midpoint_even_380 : ∀ k, 2 ∣ (ibox380 k).lo+(ibox380 k).hi := by decide +kernel
private theorem accepted_380 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox380) tree380 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox380 midpoint_even_380
  simp only [tree380,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox380,candidate_valid h (FixedTape.midBox ibox380),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox380 212 (FixedTape.rowsAux denominator ibox380 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox380) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_380
private noncomputable def tree379 : TapeTree := .split 3 (((597673876640530205355086871013395093100953600000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree380 tree381
attribute [irreducible] tree379
private theorem accepted_379 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox379) tree379 = true := by
  simp only [tree379,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox379 3 (597673876640530205355086871013395093100953600000000000000000 : Int) false,decode_split denominator ibox379 3 (597673876640530205355086871013395093100953600000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_380 h,accepted_381 h⟩
private noncomputable def tree378 : TapeTree := .split 0 (((1633610800636374200355708536662081306814840832000000000000 : Int) : ℚ)/(denominator : ℚ)) tree379 tree382
attribute [irreducible] tree378
private theorem accepted_378 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox378) tree378 = true := by
  simp only [tree378,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox378 0 (1633610800636374200355708536662081306814840832000000000000 : Int) false,decode_split denominator ibox378 0 (1633610800636374200355708536662081306814840832000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_379 h,accepted_382 h⟩
private noncomputable def tree377 : TapeTree := .split 3 (((717208651968636246426104245216074111721144320000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree378 tree385
attribute [irreducible] tree377
private theorem accepted_377 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox377) tree377 = true := by
  simp only [tree377,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox377 3 (717208651968636246426104245216074111721144320000000000000000 : Int) false,decode_split denominator ibox377 3 (717208651968636246426104245216074111721144320000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_378 h,accepted_385 h⟩
private noncomputable def tree376 : TapeTree := .centered (candidateRows ibox376) (candidateRows (FixedTape.midBox ibox376))
attribute [irreducible] tree376
private theorem sign_376 : 2*denominator*(computed denominator (FixedTape.midBox ibox376)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox376).gradient k).lo.natAbs ((computed denominator ibox376).gradient k).hi.natAbs : Int)*((ibox376 k).hi-(ibox376 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox376
    (computed denominator ibox376) (computed denominator (FixedTape.midBox ibox376))
    (by decide +kernel)
private theorem midpoint_even_376 : ∀ k, 2 ∣ (ibox376 k).lo+(ibox376 k).hi := by decide +kernel
private theorem accepted_376 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox376) tree376 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox376 midpoint_even_376
  simp only [tree376,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox376,candidate_valid h (FixedTape.midBox ibox376),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox376 212 (FixedTape.rowsAux denominator ibox376 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox376) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_376
private noncomputable def tree375 : TapeTree := .centered (candidateRows ibox375) (candidateRows (FixedTape.midBox ibox375))
attribute [irreducible] tree375
private theorem sign_375 : 2*denominator*(computed denominator (FixedTape.midBox ibox375)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox375).gradient k).lo.natAbs ((computed denominator ibox375).gradient k).hi.natAbs : Int)*((ibox375 k).hi-(ibox375 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox375
    (computed denominator ibox375) (computed denominator (FixedTape.midBox ibox375))
    (by decide +kernel)
private theorem midpoint_even_375 : ∀ k, 2 ∣ (ibox375 k).lo+(ibox375 k).hi := by decide +kernel
private theorem accepted_375 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox375) tree375 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox375 midpoint_even_375
  simp only [tree375,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox375,candidate_valid h (FixedTape.midBox ibox375),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox375 212 (FixedTape.rowsAux denominator ibox375 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox375) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_375
private noncomputable def tree374 : TapeTree := .split 3 (((836743427296742287497121619418753130341335040000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree375 tree376
attribute [irreducible] tree374
private theorem accepted_374 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox374) tree374 = true := by
  simp only [tree374,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox374 3 (836743427296742287497121619418753130341335040000000000000000 : Int) false,decode_split denominator ibox374 3 (836743427296742287497121619418753130341335040000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_375 h,accepted_376 h⟩
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
private noncomputable def tree372 : TapeTree := .centered (candidateRows ibox372) (candidateRows (FixedTape.midBox ibox372))
attribute [irreducible] tree372
private theorem sign_372 : 2*denominator*(computed denominator (FixedTape.midBox ibox372)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox372).gradient k).lo.natAbs ((computed denominator ibox372).gradient k).hi.natAbs : Int)*((ibox372 k).hi-(ibox372 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox372
    (computed denominator ibox372) (computed denominator (FixedTape.midBox ibox372))
    (by decide +kernel)
private theorem midpoint_even_372 : ∀ k, 2 ∣ (ibox372 k).lo+(ibox372 k).hi := by decide +kernel
private theorem accepted_372 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox372) tree372 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox372 midpoint_even_372
  simp only [tree372,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox372,candidate_valid h (FixedTape.midBox ibox372),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox372 212 (FixedTape.rowsAux denominator ibox372 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox372) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_372
private noncomputable def tree371 : TapeTree := .split 3 (((836743427296742287497121619418753130341335040000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree372 tree373
attribute [irreducible] tree371
private theorem accepted_371 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox371) tree371 = true := by
  simp only [tree371,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox371 3 (836743427296742287497121619418753130341335040000000000000000 : Int) false,decode_split denominator ibox371 3 (836743427296742287497121619418753130341335040000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_372 h,accepted_373 h⟩
private noncomputable def tree370 : TapeTree := .split 0 (((1569547631983967368969210162675333020273082368000000000000 : Int) : ℚ)/(denominator : ℚ)) tree371 tree374
attribute [irreducible] tree370
private theorem accepted_370 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox370) tree370 = true := by
  simp only [tree370,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox370 0 (1569547631983967368969210162675333020273082368000000000000 : Int) false,decode_split denominator ibox370 0 (1569547631983967368969210162675333020273082368000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_371 h,accepted_374 h⟩
private noncomputable def tree369 : TapeTree := .centered (candidateRows ibox369) (candidateRows (FixedTape.midBox ibox369))
attribute [irreducible] tree369
private theorem sign_369 : 2*denominator*(computed denominator (FixedTape.midBox ibox369)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox369).gradient k).lo.natAbs ((computed denominator ibox369).gradient k).hi.natAbs : Int)*((ibox369 k).hi-(ibox369 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox369
    (computed denominator ibox369) (computed denominator (FixedTape.midBox ibox369))
    (by decide +kernel)
private theorem midpoint_even_369 : ∀ k, 2 ∣ (ibox369 k).lo+(ibox369 k).hi := by decide +kernel
private theorem accepted_369 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox369) tree369 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox369 midpoint_even_369
  simp only [tree369,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox369,candidate_valid h (FixedTape.midBox ibox369),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox369 212 (FixedTape.rowsAux denominator ibox369 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox369) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_369
private noncomputable def tree368 : TapeTree := .centered (candidateRows ibox368) (candidateRows (FixedTape.midBox ibox368))
attribute [irreducible] tree368
private theorem sign_368 : 2*denominator*(computed denominator (FixedTape.midBox ibox368)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox368).gradient k).lo.natAbs ((computed denominator ibox368).gradient k).hi.natAbs : Int)*((ibox368 k).hi-(ibox368 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox368
    (computed denominator ibox368) (computed denominator (FixedTape.midBox ibox368))
    (by decide +kernel)
private theorem midpoint_even_368 : ∀ k, 2 ∣ (ibox368 k).lo+(ibox368 k).hi := by decide +kernel
private theorem accepted_368 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox368) tree368 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox368 midpoint_even_368
  simp only [tree368,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox368,candidate_valid h (FixedTape.midBox ibox368),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox368 212 (FixedTape.rowsAux denominator ibox368 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox368) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_368
private noncomputable def tree367 : TapeTree := .split 3 (((597673876640530205355086871013395093100953600000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree368 tree369
attribute [irreducible] tree367
private theorem accepted_367 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox367) tree367 = true := by
  simp only [tree367,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox367 3 (597673876640530205355086871013395093100953600000000000000000 : Int) false,decode_split denominator ibox367 3 (597673876640530205355086871013395093100953600000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_368 h,accepted_369 h⟩
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
private noncomputable def tree365 : TapeTree := .centered (candidateRows ibox365) (candidateRows (FixedTape.midBox ibox365))
attribute [irreducible] tree365
private theorem sign_365 : 2*denominator*(computed denominator (FixedTape.midBox ibox365)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox365).gradient k).lo.natAbs ((computed denominator ibox365).gradient k).hi.natAbs : Int)*((ibox365 k).hi-(ibox365 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox365
    (computed denominator ibox365) (computed denominator (FixedTape.midBox ibox365))
    (by decide +kernel)
private theorem midpoint_even_365 : ∀ k, 2 ∣ (ibox365 k).lo+(ibox365 k).hi := by decide +kernel
private theorem accepted_365 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox365) tree365 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox365 midpoint_even_365
  simp only [tree365,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox365,candidate_valid h (FixedTape.midBox ibox365),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox365 212 (FixedTape.rowsAux denominator ibox365 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox365) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_365
private noncomputable def tree364 : TapeTree := .split 3 (((597673876640530205355086871013395093100953600000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree365 tree366
attribute [irreducible] tree364
private theorem accepted_364 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox364) tree364 = true := by
  simp only [tree364,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox364 3 (597673876640530205355086871013395093100953600000000000000000 : Int) false,decode_split denominator ibox364 3 (597673876640530205355086871013395093100953600000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_365 h,accepted_366 h⟩
private noncomputable def tree363 : TapeTree := .split 0 (((1569547631983967368969210162675333020273082368000000000000 : Int) : ℚ)/(denominator : ℚ)) tree364 tree367
attribute [irreducible] tree363
private theorem accepted_363 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox363) tree363 = true := by
  simp only [tree363,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox363 0 (1569547631983967368969210162675333020273082368000000000000 : Int) false,decode_split denominator ibox363 0 (1569547631983967368969210162675333020273082368000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_364 h,accepted_367 h⟩
private noncomputable def tree362 : TapeTree := .split 3 (((717208651968636246426104245216074111721144320000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree363 tree370
attribute [irreducible] tree362
private theorem accepted_362 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox362) tree362 = true := by
  simp only [tree362,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox362 3 (717208651968636246426104245216074111721144320000000000000000 : Int) false,decode_split denominator ibox362 3 (717208651968636246426104245216074111721144320000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_363 h,accepted_370 h⟩
private noncomputable def tree361 : TapeTree := .split 0 (((1601579216310170784662459349668707163543961600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree362 tree377
attribute [irreducible] tree361
private theorem accepted_361 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox361) tree361 = true := by
  simp only [tree361,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox361 0 (1601579216310170784662459349668707163543961600000000000000 : Int) false,decode_split denominator ibox361 0 (1601579216310170784662459349668707163543961600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_362 h,accepted_377 h⟩
private noncomputable def tree360 : TapeTree := .centered (candidateRows ibox360) (candidateRows (FixedTape.midBox ibox360))
attribute [irreducible] tree360
private theorem sign_360 : 2*denominator*(computed denominator (FixedTape.midBox ibox360)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox360).gradient k).lo.natAbs ((computed denominator ibox360).gradient k).hi.natAbs : Int)*((ibox360 k).hi-(ibox360 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox360
    (computed denominator ibox360) (computed denominator (FixedTape.midBox ibox360))
    (by decide +kernel)
private theorem midpoint_even_360 : ∀ k, 2 ∣ (ibox360 k).lo+(ibox360 k).hi := by decide +kernel
private theorem accepted_360 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox360) tree360 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox360 midpoint_even_360
  simp only [tree360,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox360,candidate_valid h (FixedTape.midBox ibox360),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox360 212 (FixedTape.rowsAux denominator ibox360 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox360) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_360
private noncomputable def tree359 : TapeTree := .centered (candidateRows ibox359) (candidateRows (FixedTape.midBox ibox359))
attribute [irreducible] tree359
private theorem sign_359 : 2*denominator*(computed denominator (FixedTape.midBox ibox359)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox359).gradient k).lo.natAbs ((computed denominator ibox359).gradient k).hi.natAbs : Int)*((ibox359 k).hi-(ibox359 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox359
    (computed denominator ibox359) (computed denominator (FixedTape.midBox ibox359))
    (by decide +kernel)
private theorem midpoint_even_359 : ∀ k, 2 ∣ (ibox359 k).lo+(ibox359 k).hi := by decide +kernel
private theorem accepted_359 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox359) tree359 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox359 midpoint_even_359
  simp only [tree359,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox359,candidate_valid h (FixedTape.midBox ibox359),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox359 212 (FixedTape.rowsAux denominator ibox359 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox359) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_359
private noncomputable def tree358 : TapeTree := .split 3 (((358604325984318123213052122608037055860572160000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree359 tree360
attribute [irreducible] tree358
private theorem accepted_358 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox358) tree358 = true := by
  simp only [tree358,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox358 3 (358604325984318123213052122608037055860572160000000000000000 : Int) false,decode_split denominator ibox358 3 (358604325984318123213052122608037055860572160000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_359 h,accepted_360 h⟩
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
private noncomputable def tree355 : TapeTree := .split 3 (((358604325984318123213052122608037055860572160000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree356 tree357
attribute [irreducible] tree355
private theorem accepted_355 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox355) tree355 = true := by
  simp only [tree355,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox355 3 (358604325984318123213052122608037055860572160000000000000000 : Int) false,decode_split denominator ibox355 3 (358604325984318123213052122608037055860572160000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_356 h,accepted_357 h⟩
private noncomputable def tree354 : TapeTree := .split 0 (((1633610800636374200355708536662081306814840832000000000000 : Int) : ℚ)/(denominator : ℚ)) tree355 tree358
attribute [irreducible] tree354
private theorem accepted_354 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox354) tree354 = true := by
  simp only [tree354,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox354 0 (1633610800636374200355708536662081306814840832000000000000 : Int) false,decode_split denominator ibox354 0 (1633610800636374200355708536662081306814840832000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_355 h,accepted_358 h⟩
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
private noncomputable def tree352 : TapeTree := .centered (candidateRows ibox352) (candidateRows (FixedTape.midBox ibox352))
attribute [irreducible] tree352
private theorem sign_352 : 2*denominator*(computed denominator (FixedTape.midBox ibox352)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox352).gradient k).lo.natAbs ((computed denominator ibox352).gradient k).hi.natAbs : Int)*((ibox352 k).hi-(ibox352 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox352
    (computed denominator ibox352) (computed denominator (FixedTape.midBox ibox352))
    (by decide +kernel)
private theorem midpoint_even_352 : ∀ k, 2 ∣ (ibox352 k).lo+(ibox352 k).hi := by decide +kernel
private theorem accepted_352 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox352) tree352 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox352 midpoint_even_352
  simp only [tree352,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox352,candidate_valid h (FixedTape.midBox ibox352),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox352 212 (FixedTape.rowsAux denominator ibox352 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox352) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_352
private noncomputable def tree351 : TapeTree := .split 3 (((119534775328106041071017374202679018620190720000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree352 tree353
attribute [irreducible] tree351
private theorem accepted_351 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox351) tree351 = true := by
  simp only [tree351,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox351 3 (119534775328106041071017374202679018620190720000000000000000 : Int) false,decode_split denominator ibox351 3 (119534775328106041071017374202679018620190720000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_352 h,accepted_353 h⟩
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
private noncomputable def tree348 : TapeTree := .split 3 (((119534775328106041071017374202679018620190720000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree349 tree350
attribute [irreducible] tree348
private theorem accepted_348 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox348) tree348 = true := by
  simp only [tree348,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox348 3 (119534775328106041071017374202679018620190720000000000000000 : Int) false,decode_split denominator ibox348 3 (119534775328106041071017374202679018620190720000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_349 h,accepted_350 h⟩
private noncomputable def tree347 : TapeTree := .split 0 (((1633610800636374200355708536662081306814840832000000000000 : Int) : ℚ)/(denominator : ℚ)) tree348 tree351
attribute [irreducible] tree347
private theorem accepted_347 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox347) tree347 = true := by
  simp only [tree347,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox347 0 (1633610800636374200355708536662081306814840832000000000000 : Int) false,decode_split denominator ibox347 0 (1633610800636374200355708536662081306814840832000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_348 h,accepted_351 h⟩
private noncomputable def tree346 : TapeTree := .split 3 (((239069550656212082142034748405358037240381440000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree347 tree354
attribute [irreducible] tree346
private theorem accepted_346 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox346) tree346 = true := by
  simp only [tree346,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox346 3 (239069550656212082142034748405358037240381440000000000000000 : Int) false,decode_split denominator ibox346 3 (239069550656212082142034748405358037240381440000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_347 h,accepted_354 h⟩
private noncomputable def tree345 : TapeTree := .centered (candidateRows ibox345) (candidateRows (FixedTape.midBox ibox345))
attribute [irreducible] tree345
private theorem sign_345 : 2*denominator*(computed denominator (FixedTape.midBox ibox345)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox345).gradient k).lo.natAbs ((computed denominator ibox345).gradient k).hi.natAbs : Int)*((ibox345 k).hi-(ibox345 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox345
    (computed denominator ibox345) (computed denominator (FixedTape.midBox ibox345))
    (by decide +kernel)
private theorem midpoint_even_345 : ∀ k, 2 ∣ (ibox345 k).lo+(ibox345 k).hi := by decide +kernel
private theorem accepted_345 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox345) tree345 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox345 midpoint_even_345
  simp only [tree345,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox345,candidate_valid h (FixedTape.midBox ibox345),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox345 212 (FixedTape.rowsAux denominator ibox345 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox345) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_345
private noncomputable def tree344 : TapeTree := .centered (candidateRows ibox344) (candidateRows (FixedTape.midBox ibox344))
attribute [irreducible] tree344
private theorem sign_344 : 2*denominator*(computed denominator (FixedTape.midBox ibox344)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox344).gradient k).lo.natAbs ((computed denominator ibox344).gradient k).hi.natAbs : Int)*((ibox344 k).hi-(ibox344 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox344
    (computed denominator ibox344) (computed denominator (FixedTape.midBox ibox344))
    (by decide +kernel)
private theorem midpoint_even_344 : ∀ k, 2 ∣ (ibox344 k).lo+(ibox344 k).hi := by decide +kernel
private theorem accepted_344 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox344) tree344 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox344 midpoint_even_344
  simp only [tree344,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox344,candidate_valid h (FixedTape.midBox ibox344),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox344 212 (FixedTape.rowsAux denominator ibox344 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox344) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_344
private noncomputable def tree343 : TapeTree := .split 3 (((358604325984318123213052122608037055860572160000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree344 tree345
attribute [irreducible] tree343
private theorem accepted_343 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox343) tree343 = true := by
  simp only [tree343,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox343 3 (358604325984318123213052122608037055860572160000000000000000 : Int) false,decode_split denominator ibox343 3 (358604325984318123213052122608037055860572160000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_344 h,accepted_345 h⟩
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
private noncomputable def tree340 : TapeTree := .split 3 (((358604325984318123213052122608037055860572160000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree341 tree342
attribute [irreducible] tree340
private theorem accepted_340 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox340) tree340 = true := by
  simp only [tree340,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox340 3 (358604325984318123213052122608037055860572160000000000000000 : Int) false,decode_split denominator ibox340 3 (358604325984318123213052122608037055860572160000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_341 h,accepted_342 h⟩
private noncomputable def tree339 : TapeTree := .split 0 (((1569547631983967368969210162675333020273082368000000000000 : Int) : ℚ)/(denominator : ℚ)) tree340 tree343
attribute [irreducible] tree339
private theorem accepted_339 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox339) tree339 = true := by
  simp only [tree339,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox339 0 (1569547631983967368969210162675333020273082368000000000000 : Int) false,decode_split denominator ibox339 0 (1569547631983967368969210162675333020273082368000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_340 h,accepted_343 h⟩
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
private noncomputable def tree337 : TapeTree := .centered (candidateRows ibox337) (candidateRows (FixedTape.midBox ibox337))
attribute [irreducible] tree337
private theorem sign_337 : 2*denominator*(computed denominator (FixedTape.midBox ibox337)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox337).gradient k).lo.natAbs ((computed denominator ibox337).gradient k).hi.natAbs : Int)*((ibox337 k).hi-(ibox337 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox337
    (computed denominator ibox337) (computed denominator (FixedTape.midBox ibox337))
    (by decide +kernel)
private theorem midpoint_even_337 : ∀ k, 2 ∣ (ibox337 k).lo+(ibox337 k).hi := by decide +kernel
private theorem accepted_337 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox337) tree337 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox337 midpoint_even_337
  simp only [tree337,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox337,candidate_valid h (FixedTape.midBox ibox337),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox337 212 (FixedTape.rowsAux denominator ibox337 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox337) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_337
private noncomputable def tree336 : TapeTree := .split 3 (((119534775328106041071017374202679018620190720000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree337 tree338
attribute [irreducible] tree336
private theorem accepted_336 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox336) tree336 = true := by
  simp only [tree336,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox336 3 (119534775328106041071017374202679018620190720000000000000000 : Int) false,decode_split denominator ibox336 3 (119534775328106041071017374202679018620190720000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_337 h,accepted_338 h⟩
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
private noncomputable def tree333 : TapeTree := .split 3 (((119534775328106041071017374202679018620190720000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree334 tree335
attribute [irreducible] tree333
private theorem accepted_333 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox333) tree333 = true := by
  simp only [tree333,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox333 3 (119534775328106041071017374202679018620190720000000000000000 : Int) false,decode_split denominator ibox333 3 (119534775328106041071017374202679018620190720000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_334 h,accepted_335 h⟩
private noncomputable def tree332 : TapeTree := .split 0 (((1569547631983967368969210162675333020273082368000000000000 : Int) : ℚ)/(denominator : ℚ)) tree333 tree336
attribute [irreducible] tree332
private theorem accepted_332 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox332) tree332 = true := by
  simp only [tree332,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox332 0 (1569547631983967368969210162675333020273082368000000000000 : Int) false,decode_split denominator ibox332 0 (1569547631983967368969210162675333020273082368000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_333 h,accepted_336 h⟩
private noncomputable def tree331 : TapeTree := .split 3 (((239069550656212082142034748405358037240381440000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree332 tree339
attribute [irreducible] tree331
private theorem accepted_331 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox331) tree331 = true := by
  simp only [tree331,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox331 3 (239069550656212082142034748405358037240381440000000000000000 : Int) false,decode_split denominator ibox331 3 (239069550656212082142034748405358037240381440000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_332 h,accepted_339 h⟩
private noncomputable def tree330 : TapeTree := .split 0 (((1601579216310170784662459349668707163543961600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree331 tree346
attribute [irreducible] tree330
private theorem accepted_330 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox330) tree330 = true := by
  simp only [tree330,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox330 0 (1601579216310170784662459349668707163543961600000000000000 : Int) false,decode_split denominator ibox330 0 (1601579216310170784662459349668707163543961600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_331 h,accepted_346 h⟩
private noncomputable def tree329 : TapeTree := .split 3 (((478139101312424164284069496810716074480762880000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree330 tree361
attribute [irreducible] tree329
private theorem accepted_329 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox329) tree329 = true := by
  simp only [tree329,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox329 3 (478139101312424164284069496810716074480762880000000000000000 : Int) false,decode_split denominator ibox329 3 (478139101312424164284069496810716074480762880000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_330 h,accepted_361 h⟩
private noncomputable def tree328 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree329 tree392
attribute [irreducible] tree328
private theorem accepted_328 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox328) tree328 = true := by
  simp only [tree328,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox328 3 (956278202624848328568138993621432148961525760000000000000000 : Int) false,decode_split denominator ibox328 3 (956278202624848328568138993621432148961525760000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_329 h,accepted_392 h⟩
private noncomputable def tree327 : TapeTree := .face 1 false (candidateRows ibox327) tree328
attribute [irreducible] tree327
private theorem sign_327 : ((computed denominator ibox327).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_327 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox327) tree327 = true := by
  simp only [tree327,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox327,?_,accepted_328 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox327)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox327).gradient 1).hi) denominator_positive).1 sign_327
private noncomputable def tree326 : TapeTree := .split 0 (((1665642384962577616048957723655455450085720064000000000000 : Int) : ℚ)/(denominator : ℚ)) tree327 tree453
attribute [irreducible] tree326
private theorem accepted_326 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox326) tree326 = true := by
  simp only [tree326,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox326 0 (1665642384962577616048957723655455450085720064000000000000 : Int) false,decode_split denominator ibox326 0 (1665642384962577616048957723655455450085720064000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_327 h,accepted_453 h⟩
private noncomputable def tree325 : TapeTree := .split 1 (((239069550656212082142034748405358037240381440000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree326 tree533
attribute [irreducible] tree325
private theorem accepted_325 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox325) tree325 = true := by
  simp only [tree325,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox325 1 (239069550656212082142034748405358037240381440000000000000000 : Int) false,decode_split denominator ibox325 1 (239069550656212082142034748405358037240381440000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_326 h,accepted_533 h⟩
private noncomputable def tree324 : TapeTree := .split 1 (((478139101312424164284069496810716074480762880000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree325 tree542
attribute [irreducible] tree324
private theorem accepted_324 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox324) tree324 = true := by
  simp only [tree324,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox324 1 (478139101312424164284069496810716074480762880000000000000000 : Int) false,decode_split denominator ibox324 1 (478139101312424164284069496810716074480762880000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_325 h,accepted_542 h⟩
private noncomputable def tree323 : TapeTree := .face 2 true (candidateRows ibox323) tree324
attribute [irreducible] tree323
private theorem sign_323 : 0 ≤ ((computed denominator ibox323).gradient 2).lo := by decide +kernel
private theorem accepted_323 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox323) tree323 = true := by
  simp only [tree323,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox323,?_,accepted_324 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox323)).gradient 2).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox323).gradient 2).lo) denominator_positive).2 sign_323
private noncomputable def tree322 : TapeTree := .split 1 (((956278202624848328568138993621432148961525760000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree323 tree547
attribute [irreducible] tree322
private theorem accepted_322 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox322) tree322 = true := by
  simp only [tree322,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox322 1 (956278202624848328568138993621432148961525760000000000000000 : Int) false,decode_split denominator ibox322 1 (956278202624848328568138993621432148961525760000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_323 h,accepted_547 h⟩
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
private noncomputable def tree320 : TapeTree := .centered (candidateRows ibox320) (candidateRows (FixedTape.midBox ibox320))
attribute [irreducible] tree320
private theorem sign_320 : 2*denominator*(computed denominator (FixedTape.midBox ibox320)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox320).gradient k).lo.natAbs ((computed denominator ibox320).gradient k).hi.natAbs : Int)*((ibox320 k).hi-(ibox320 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox320
    (computed denominator ibox320) (computed denominator (FixedTape.midBox ibox320))
    (by decide +kernel)
private theorem midpoint_even_320 : ∀ k, 2 ∣ (ibox320 k).lo+(ibox320 k).hi := by decide +kernel
private theorem accepted_320 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox320) tree320 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox320 midpoint_even_320
  simp only [tree320,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox320,candidate_valid h (FixedTape.midBox ibox320),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox320 212 (FixedTape.rowsAux denominator ibox320 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox320) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_320
private noncomputable def tree319 : TapeTree := .split 1 (((956278202624848328568138993621432148961525760000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree320 tree321
attribute [irreducible] tree319
private theorem accepted_319 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox319) tree319 = true := by
  simp only [tree319,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox319 1 (956278202624848328568138993621432148961525760000000000000000 : Int) false,decode_split denominator ibox319 1 (956278202624848328568138993621432148961525760000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_320 h,accepted_321 h⟩
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
private noncomputable def tree317 : TapeTree := .centered (candidateRows ibox317) (candidateRows (FixedTape.midBox ibox317))
attribute [irreducible] tree317
private theorem sign_317 : 2*denominator*(computed denominator (FixedTape.midBox ibox317)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox317).gradient k).lo.natAbs ((computed denominator ibox317).gradient k).hi.natAbs : Int)*((ibox317 k).hi-(ibox317 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox317
    (computed denominator ibox317) (computed denominator (FixedTape.midBox ibox317))
    (by decide +kernel)
private theorem midpoint_even_317 : ∀ k, 2 ∣ (ibox317 k).lo+(ibox317 k).hi := by decide +kernel
private theorem accepted_317 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox317) tree317 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox317 midpoint_even_317
  simp only [tree317,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox317,candidate_valid h (FixedTape.midBox ibox317),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox317 212 (FixedTape.rowsAux denominator ibox317 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox317) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_317
private noncomputable def tree316 : TapeTree := .split 1 (((956278202624848328568138993621432148961525760000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree317 tree318
attribute [irreducible] tree316
private theorem accepted_316 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox316) tree316 = true := by
  simp only [tree316,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox316 1 (956278202624848328568138993621432148961525760000000000000000 : Int) false,decode_split denominator ibox316 1 (956278202624848328568138993621432148961525760000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_317 h,accepted_318 h⟩
private noncomputable def tree315 : TapeTree := .split 0 (((1665642384962577616048957723655455450085720064000000000000 : Int) : ℚ)/(denominator : ℚ)) tree316 tree319
attribute [irreducible] tree315
private theorem accepted_315 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox315) tree315 = true := by
  simp only [tree315,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox315 0 (1665642384962577616048957723655455450085720064000000000000 : Int) false,decode_split denominator ibox315 0 (1665642384962577616048957723655455450085720064000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_316 h,accepted_319 h⟩
private noncomputable def tree314 : TapeTree := .face 3 false (candidateRows ibox314) tree315
attribute [irreducible] tree314
private theorem sign_314 : ((computed denominator ibox314).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_314 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox314) tree314 = true := by
  simp only [tree314,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox314,?_,accepted_315 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox314)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox314).gradient 3).hi) denominator_positive).1 sign_314
private noncomputable def tree313 : TapeTree := .split 2 (((1434417303937272492852208490432148223442288640000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree314 tree322
attribute [irreducible] tree313
private theorem accepted_313 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox313) tree313 = true := by
  simp only [tree313,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox313 2 (1434417303937272492852208490432148223442288640000000000000000 : Int) false,decode_split denominator ibox313 2 (1434417303937272492852208490432148223442288640000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_314 h,accepted_322 h⟩
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
private noncomputable def tree310 : TapeTree := .split 1 (((1434417303937272492852208490432148223442288640000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree311 tree312
attribute [irreducible] tree310
private theorem accepted_310 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox310) tree310 = true := by
  simp only [tree310,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox310 1 (1434417303937272492852208490432148223442288640000000000000000 : Int) false,decode_split denominator ibox310 1 (1434417303937272492852208490432148223442288640000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_311 h,accepted_312 h⟩
private noncomputable def tree309 : TapeTree := .centered (candidateRows ibox309) (candidateRows (FixedTape.midBox ibox309))
attribute [irreducible] tree309
private theorem sign_309 : 2*denominator*(computed denominator (FixedTape.midBox ibox309)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox309).gradient k).lo.natAbs ((computed denominator ibox309).gradient k).hi.natAbs : Int)*((ibox309 k).hi-(ibox309 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox309
    (computed denominator ibox309) (computed denominator (FixedTape.midBox ibox309))
    (by decide +kernel)
private theorem midpoint_even_309 : ∀ k, 2 ∣ (ibox309 k).lo+(ibox309 k).hi := by decide +kernel
private theorem accepted_309 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox309) tree309 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox309 midpoint_even_309
  simp only [tree309,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox309,candidate_valid h (FixedTape.midBox ibox309),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox309 212 (FixedTape.rowsAux denominator ibox309 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox309) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_309
private noncomputable def tree308 : TapeTree := .centered (candidateRows ibox308) (candidateRows (FixedTape.midBox ibox308))
attribute [irreducible] tree308
private theorem sign_308 : 2*denominator*(computed denominator (FixedTape.midBox ibox308)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox308).gradient k).lo.natAbs ((computed denominator ibox308).gradient k).hi.natAbs : Int)*((ibox308 k).hi-(ibox308 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox308
    (computed denominator ibox308) (computed denominator (FixedTape.midBox ibox308))
    (by decide +kernel)
private theorem midpoint_even_308 : ∀ k, 2 ∣ (ibox308 k).lo+(ibox308 k).hi := by decide +kernel
private theorem accepted_308 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox308) tree308 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox308 midpoint_even_308
  simp only [tree308,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox308,candidate_valid h (FixedTape.midBox ibox308),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox308 212 (FixedTape.rowsAux denominator ibox308 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox308) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_308
private noncomputable def tree307 : TapeTree := .split 1 (((1434417303937272492852208490432148223442288640000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree308 tree309
attribute [irreducible] tree307
private theorem accepted_307 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox307) tree307 = true := by
  simp only [tree307,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox307 1 (1434417303937272492852208490432148223442288640000000000000000 : Int) false,decode_split denominator ibox307 1 (1434417303937272492852208490432148223442288640000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_308 h,accepted_309 h⟩
private noncomputable def tree306 : TapeTree := .split 0 (((1409389710352950290502964227708462303918686208000000000000 : Int) : ℚ)/(denominator : ℚ)) tree307 tree310
attribute [irreducible] tree306
private theorem accepted_306 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox306) tree306 = true := by
  simp only [tree306,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox306 0 (1409389710352950290502964227708462303918686208000000000000 : Int) false,decode_split denominator ibox306 0 (1409389710352950290502964227708462303918686208000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_307 h,accepted_310 h⟩
private noncomputable def tree305 : TapeTree := .face 3 false (candidateRows ibox305) tree306
attribute [irreducible] tree305
private theorem sign_305 : ((computed denominator ibox305).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_305 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox305) tree305 = true := by
  simp only [tree305,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox305,?_,accepted_306 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox305)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox305).gradient 3).hi) denominator_positive).1 sign_305
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
private noncomputable def tree303 : TapeTree := .face 1 false (candidateRows ibox303) tree304
attribute [irreducible] tree303
private theorem sign_303 : ((computed denominator ibox303).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_303 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox303) tree303 = true := by
  simp only [tree303,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox303,?_,accepted_304 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox303)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox303).gradient 1).hi) denominator_positive).1 sign_303
private noncomputable def tree302 : TapeTree := .centered (candidateRows ibox302) (candidateRows (FixedTape.midBox ibox302))
attribute [irreducible] tree302
private theorem sign_302 : 2*denominator*(computed denominator (FixedTape.midBox ibox302)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox302).gradient k).lo.natAbs ((computed denominator ibox302).gradient k).hi.natAbs : Int)*((ibox302 k).hi-(ibox302 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox302
    (computed denominator ibox302) (computed denominator (FixedTape.midBox ibox302))
    (by decide +kernel)
private theorem midpoint_even_302 : ∀ k, 2 ∣ (ibox302 k).lo+(ibox302 k).hi := by decide +kernel
private theorem accepted_302 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox302) tree302 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox302 midpoint_even_302
  simp only [tree302,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox302,candidate_valid h (FixedTape.midBox ibox302),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox302 212 (FixedTape.rowsAux denominator ibox302 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox302) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_302
private noncomputable def tree301 : TapeTree := .face 1 false (candidateRows ibox301) tree302
attribute [irreducible] tree301
private theorem sign_301 : ((computed denominator ibox301).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_301 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox301) tree301 = true := by
  simp only [tree301,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox301,?_,accepted_302 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox301)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox301).gradient 1).hi) denominator_positive).1 sign_301
private noncomputable def tree300 : TapeTree := .split 0 (((1409389710352950290502964227708462303918686208000000000000 : Int) : ℚ)/(denominator : ℚ)) tree301 tree303
attribute [irreducible] tree300
private theorem accepted_300 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox300) tree300 = true := by
  simp only [tree300,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox300 0 (1409389710352950290502964227708462303918686208000000000000 : Int) false,decode_split denominator ibox300 0 (1409389710352950290502964227708462303918686208000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_301 h,accepted_303 h⟩
private noncomputable def tree299 : TapeTree := .centered (candidateRows ibox299) (candidateRows (FixedTape.midBox ibox299))
attribute [irreducible] tree299
private theorem sign_299 : 2*denominator*(computed denominator (FixedTape.midBox ibox299)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox299).gradient k).lo.natAbs ((computed denominator ibox299).gradient k).hi.natAbs : Int)*((ibox299 k).hi-(ibox299 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox299
    (computed denominator ibox299) (computed denominator (FixedTape.midBox ibox299))
    (by decide +kernel)
private theorem midpoint_even_299 : ∀ k, 2 ∣ (ibox299 k).lo+(ibox299 k).hi := by decide +kernel
private theorem accepted_299 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox299) tree299 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox299 midpoint_even_299
  simp only [tree299,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox299,candidate_valid h (FixedTape.midBox ibox299),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox299 212 (FixedTape.rowsAux denominator ibox299 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox299) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_299
private noncomputable def tree298 : TapeTree := .centered (candidateRows ibox298) (candidateRows (FixedTape.midBox ibox298))
attribute [irreducible] tree298
private theorem sign_298 : 2*denominator*(computed denominator (FixedTape.midBox ibox298)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox298).gradient k).lo.natAbs ((computed denominator ibox298).gradient k).hi.natAbs : Int)*((ibox298 k).hi-(ibox298 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox298
    (computed denominator ibox298) (computed denominator (FixedTape.midBox ibox298))
    (by decide +kernel)
private theorem midpoint_even_298 : ∀ k, 2 ∣ (ibox298 k).lo+(ibox298 k).hi := by decide +kernel
private theorem accepted_298 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox298) tree298 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox298 midpoint_even_298
  simp only [tree298,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox298,candidate_valid h (FixedTape.midBox ibox298),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox298 212 (FixedTape.rowsAux denominator ibox298 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox298) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_298
private noncomputable def tree297 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree298 tree299
attribute [irreducible] tree297
private theorem accepted_297 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox297) tree297 = true := by
  simp only [tree297,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox297 3 (956278202624848328568138993621432148961525760000000000000000 : Int) false,decode_split denominator ibox297 3 (956278202624848328568138993621432148961525760000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_298 h,accepted_299 h⟩
private noncomputable def tree296 : TapeTree := .face 1 false (candidateRows ibox296) tree297
attribute [irreducible] tree296
private theorem sign_296 : ((computed denominator ibox296).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_296 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox296) tree296 = true := by
  simp only [tree296,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox296,?_,accepted_297 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox296)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox296).gradient 1).hi) denominator_positive).1 sign_296
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
private noncomputable def tree294 : TapeTree := .centered (candidateRows ibox294) (candidateRows (FixedTape.midBox ibox294))
attribute [irreducible] tree294
private theorem sign_294 : 2*denominator*(computed denominator (FixedTape.midBox ibox294)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox294).gradient k).lo.natAbs ((computed denominator ibox294).gradient k).hi.natAbs : Int)*((ibox294 k).hi-(ibox294 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox294
    (computed denominator ibox294) (computed denominator (FixedTape.midBox ibox294))
    (by decide +kernel)
private theorem midpoint_even_294 : ∀ k, 2 ∣ (ibox294 k).lo+(ibox294 k).hi := by decide +kernel
private theorem accepted_294 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox294) tree294 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox294 midpoint_even_294
  simp only [tree294,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox294,candidate_valid h (FixedTape.midBox ibox294),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox294 212 (FixedTape.rowsAux denominator ibox294 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox294) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_294
private noncomputable def tree293 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree294 tree295
attribute [irreducible] tree293
private theorem accepted_293 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox293) tree293 = true := by
  simp only [tree293,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox293 3 (956278202624848328568138993621432148961525760000000000000000 : Int) false,decode_split denominator ibox293 3 (956278202624848328568138993621432148961525760000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_294 h,accepted_295 h⟩
private noncomputable def tree292 : TapeTree := .face 1 false (candidateRows ibox292) tree293
attribute [irreducible] tree292
private theorem sign_292 : ((computed denominator ibox292).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_292 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox292) tree292 = true := by
  simp only [tree292,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox292,?_,accepted_293 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox292)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox292).gradient 1).hi) denominator_positive).1 sign_292
private noncomputable def tree291 : TapeTree := .split 0 (((1409389710352950290502964227708462303918686208000000000000 : Int) : ℚ)/(denominator : ℚ)) tree292 tree296
attribute [irreducible] tree291
private theorem accepted_291 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox291) tree291 = true := by
  simp only [tree291,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox291 0 (1409389710352950290502964227708462303918686208000000000000 : Int) false,decode_split denominator ibox291 0 (1409389710352950290502964227708462303918686208000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_292 h,accepted_296 h⟩
private noncomputable def tree290 : TapeTree := .centered (candidateRows ibox290) (candidateRows (FixedTape.midBox ibox290))
attribute [irreducible] tree290
private theorem sign_290 : 2*denominator*(computed denominator (FixedTape.midBox ibox290)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox290).gradient k).lo.natAbs ((computed denominator ibox290).gradient k).hi.natAbs : Int)*((ibox290 k).hi-(ibox290 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox290
    (computed denominator ibox290) (computed denominator (FixedTape.midBox ibox290))
    (by decide +kernel)
private theorem midpoint_even_290 : ∀ k, 2 ∣ (ibox290 k).lo+(ibox290 k).hi := by decide +kernel
private theorem accepted_290 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox290) tree290 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox290 midpoint_even_290
  simp only [tree290,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox290,candidate_valid h (FixedTape.midBox ibox290),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox290 212 (FixedTape.rowsAux denominator ibox290 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox290) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_290
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
private noncomputable def tree288 : TapeTree := .split 0 (((1505484463331560537582711788688584733731323904000000000000 : Int) : ℚ)/(denominator : ℚ)) tree289 tree290
attribute [irreducible] tree288
private theorem accepted_288 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox288) tree288 = true := by
  simp only [tree288,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox288 0 (1505484463331560537582711788688584733731323904000000000000 : Int) false,decode_split denominator ibox288 0 (1505484463331560537582711788688584733731323904000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_289 h,accepted_290 h⟩
private noncomputable def tree287 : TapeTree := .centered (candidateRows ibox287) (candidateRows (FixedTape.midBox ibox287))
attribute [irreducible] tree287
private theorem sign_287 : 2*denominator*(computed denominator (FixedTape.midBox ibox287)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox287).gradient k).lo.natAbs ((computed denominator ibox287).gradient k).hi.natAbs : Int)*((ibox287 k).hi-(ibox287 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox287
    (computed denominator ibox287) (computed denominator (FixedTape.midBox ibox287))
    (by decide +kernel)
private theorem midpoint_even_287 : ∀ k, 2 ∣ (ibox287 k).lo+(ibox287 k).hi := by decide +kernel
private theorem accepted_287 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox287) tree287 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox287 midpoint_even_287
  simp only [tree287,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox287,candidate_valid h (FixedTape.midBox ibox287),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox287 212 (FixedTape.rowsAux denominator ibox287 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox287) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_287
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
private noncomputable def tree285 : TapeTree := .split 0 (((1505484463331560537582711788688584733731323904000000000000 : Int) : ℚ)/(denominator : ℚ)) tree286 tree287
attribute [irreducible] tree285
private theorem accepted_285 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox285) tree285 = true := by
  simp only [tree285,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox285 0 (1505484463331560537582711788688584733731323904000000000000 : Int) false,decode_split denominator ibox285 0 (1505484463331560537582711788688584733731323904000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_286 h,accepted_287 h⟩
private noncomputable def tree284 : TapeTree := .split 3 (((1793021629921590616065260613040185279302860800000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree285 tree288
attribute [irreducible] tree284
private theorem accepted_284 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox284) tree284 = true := by
  simp only [tree284,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox284 3 (1793021629921590616065260613040185279302860800000000000000000 : Int) false,decode_split denominator ibox284 3 (1793021629921590616065260613040185279302860800000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_285 h,accepted_288 h⟩
private noncomputable def tree283 : TapeTree := .centered (candidateRows ibox283) (candidateRows (FixedTape.midBox ibox283))
attribute [irreducible] tree283
private theorem sign_283 : 2*denominator*(computed denominator (FixedTape.midBox ibox283)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox283).gradient k).lo.natAbs ((computed denominator ibox283).gradient k).hi.natAbs : Int)*((ibox283 k).hi-(ibox283 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox283
    (computed denominator ibox283) (computed denominator (FixedTape.midBox ibox283))
    (by decide +kernel)
private theorem midpoint_even_283 : ∀ k, 2 ∣ (ibox283 k).lo+(ibox283 k).hi := by decide +kernel
private theorem accepted_283 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox283) tree283 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox283 midpoint_even_283
  simp only [tree283,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox283,candidate_valid h (FixedTape.midBox ibox283),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox283 212 (FixedTape.rowsAux denominator ibox283 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox283) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_283
private noncomputable def tree282 : TapeTree := .centered (candidateRows ibox282) (candidateRows (FixedTape.midBox ibox282))
attribute [irreducible] tree282
private theorem sign_282 : 2*denominator*(computed denominator (FixedTape.midBox ibox282)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox282).gradient k).lo.natAbs ((computed denominator ibox282).gradient k).hi.natAbs : Int)*((ibox282 k).hi-(ibox282 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox282
    (computed denominator ibox282) (computed denominator (FixedTape.midBox ibox282))
    (by decide +kernel)
private theorem midpoint_even_282 : ∀ k, 2 ∣ (ibox282 k).lo+(ibox282 k).hi := by decide +kernel
private theorem accepted_282 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox282) tree282 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox282 midpoint_even_282
  simp only [tree282,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox282,candidate_valid h (FixedTape.midBox ibox282),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox282 212 (FixedTape.rowsAux denominator ibox282 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox282) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_282
private noncomputable def tree281 : TapeTree := .split 0 (((1441421294679153706196213414701836447189565440000000000000 : Int) : ℚ)/(denominator : ℚ)) tree282 tree283
attribute [irreducible] tree281
private theorem accepted_281 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox281) tree281 = true := by
  simp only [tree281,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox281 0 (1441421294679153706196213414701836447189565440000000000000 : Int) false,decode_split denominator ibox281 0 (1441421294679153706196213414701836447189565440000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_282 h,accepted_283 h⟩
private noncomputable def tree280 : TapeTree := .centered (candidateRows ibox280) (candidateRows (FixedTape.midBox ibox280))
attribute [irreducible] tree280
private theorem sign_280 : 2*denominator*(computed denominator (FixedTape.midBox ibox280)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox280).gradient k).lo.natAbs ((computed denominator ibox280).gradient k).hi.natAbs : Int)*((ibox280 k).hi-(ibox280 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox280
    (computed denominator ibox280) (computed denominator (FixedTape.midBox ibox280))
    (by decide +kernel)
private theorem midpoint_even_280 : ∀ k, 2 ∣ (ibox280 k).lo+(ibox280 k).hi := by decide +kernel
private theorem accepted_280 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox280) tree280 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox280 midpoint_even_280
  simp only [tree280,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox280,candidate_valid h (FixedTape.midBox ibox280),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox280 212 (FixedTape.rowsAux denominator ibox280 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox280) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_280
private noncomputable def tree279 : TapeTree := .centered (candidateRows ibox279) (candidateRows (FixedTape.midBox ibox279))
attribute [irreducible] tree279
private theorem sign_279 : 2*denominator*(computed denominator (FixedTape.midBox ibox279)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox279).gradient k).lo.natAbs ((computed denominator ibox279).gradient k).hi.natAbs : Int)*((ibox279 k).hi-(ibox279 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox279
    (computed denominator ibox279) (computed denominator (FixedTape.midBox ibox279))
    (by decide +kernel)
private theorem midpoint_even_279 : ∀ k, 2 ∣ (ibox279 k).lo+(ibox279 k).hi := by decide +kernel
private theorem accepted_279 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox279) tree279 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox279 midpoint_even_279
  simp only [tree279,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox279,candidate_valid h (FixedTape.midBox ibox279),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox279 212 (FixedTape.rowsAux denominator ibox279 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox279) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_279
private noncomputable def tree278 : TapeTree := .split 0 (((1441421294679153706196213414701836447189565440000000000000 : Int) : ℚ)/(denominator : ℚ)) tree279 tree280
attribute [irreducible] tree278
private theorem accepted_278 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox278) tree278 = true := by
  simp only [tree278,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox278 0 (1441421294679153706196213414701836447189565440000000000000 : Int) false,decode_split denominator ibox278 0 (1441421294679153706196213414701836447189565440000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_279 h,accepted_280 h⟩
private noncomputable def tree277 : TapeTree := .split 3 (((1793021629921590616065260613040185279302860800000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree278 tree281
attribute [irreducible] tree277
private theorem accepted_277 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox277) tree277 = true := by
  simp only [tree277,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox277 3 (1793021629921590616065260613040185279302860800000000000000000 : Int) false,decode_split denominator ibox277 3 (1793021629921590616065260613040185279302860800000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_278 h,accepted_281 h⟩
private noncomputable def tree276 : TapeTree := .split 0 (((1473452879005357121889462601695210590460444672000000000000 : Int) : ℚ)/(denominator : ℚ)) tree277 tree284
attribute [irreducible] tree276
private theorem accepted_276 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox276) tree276 = true := by
  simp only [tree276,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox276 0 (1473452879005357121889462601695210590460444672000000000000 : Int) false,decode_split denominator ibox276 0 (1473452879005357121889462601695210590460444672000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_277 h,accepted_284 h⟩
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
private noncomputable def tree274 : TapeTree := .centered (candidateRows ibox274) (candidateRows (FixedTape.midBox ibox274))
attribute [irreducible] tree274
private theorem sign_274 : 2*denominator*(computed denominator (FixedTape.midBox ibox274)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox274).gradient k).lo.natAbs ((computed denominator ibox274).gradient k).hi.natAbs : Int)*((ibox274 k).hi-(ibox274 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox274
    (computed denominator ibox274) (computed denominator (FixedTape.midBox ibox274))
    (by decide +kernel)
private theorem midpoint_even_274 : ∀ k, 2 ∣ (ibox274 k).lo+(ibox274 k).hi := by decide +kernel
private theorem accepted_274 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox274) tree274 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox274 midpoint_even_274
  simp only [tree274,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox274,candidate_valid h (FixedTape.midBox ibox274),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox274 212 (FixedTape.rowsAux denominator ibox274 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox274) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_274
private noncomputable def tree273 : TapeTree := .split 3 (((1553952079265378533923225864634827242062479360000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree274 tree275
attribute [irreducible] tree273
private theorem accepted_273 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox273) tree273 = true := by
  simp only [tree273,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox273 3 (1553952079265378533923225864634827242062479360000000000000000 : Int) false,decode_split denominator ibox273 3 (1553952079265378533923225864634827242062479360000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_274 h,accepted_275 h⟩
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
private noncomputable def tree270 : TapeTree := .split 3 (((1553952079265378533923225864634827242062479360000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree271 tree272
attribute [irreducible] tree270
private theorem accepted_270 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox270) tree270 = true := by
  simp only [tree270,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox270 3 (1553952079265378533923225864634827242062479360000000000000000 : Int) false,decode_split denominator ibox270 3 (1553952079265378533923225864634827242062479360000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_271 h,accepted_272 h⟩
private noncomputable def tree269 : TapeTree := .split 0 (((1505484463331560537582711788688584733731323904000000000000 : Int) : ℚ)/(denominator : ℚ)) tree270 tree273
attribute [irreducible] tree269
private theorem accepted_269 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox269) tree269 = true := by
  simp only [tree269,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox269 0 (1505484463331560537582711788688584733731323904000000000000 : Int) false,decode_split denominator ibox269 0 (1505484463331560537582711788688584733731323904000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_270 h,accepted_273 h⟩
private noncomputable def tree268 : TapeTree := .centered (candidateRows ibox268) (candidateRows (FixedTape.midBox ibox268))
attribute [irreducible] tree268
private theorem sign_268 : 2*denominator*(computed denominator (FixedTape.midBox ibox268)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox268).gradient k).lo.natAbs ((computed denominator ibox268).gradient k).hi.natAbs : Int)*((ibox268 k).hi-(ibox268 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox268
    (computed denominator ibox268) (computed denominator (FixedTape.midBox ibox268))
    (by decide +kernel)
private theorem midpoint_even_268 : ∀ k, 2 ∣ (ibox268 k).lo+(ibox268 k).hi := by decide +kernel
private theorem accepted_268 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox268) tree268 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox268 midpoint_even_268
  simp only [tree268,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox268,candidate_valid h (FixedTape.midBox ibox268),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox268 212 (FixedTape.rowsAux denominator ibox268 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox268) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_268
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
private noncomputable def tree266 : TapeTree := .split 3 (((1553952079265378533923225864634827242062479360000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree267 tree268
attribute [irreducible] tree266
private theorem accepted_266 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox266) tree266 = true := by
  simp only [tree266,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox266 3 (1553952079265378533923225864634827242062479360000000000000000 : Int) false,decode_split denominator ibox266 3 (1553952079265378533923225864634827242062479360000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_267 h,accepted_268 h⟩
private noncomputable def tree265 : TapeTree := .centered (candidateRows ibox265) (candidateRows (FixedTape.midBox ibox265))
attribute [irreducible] tree265
private theorem sign_265 : 2*denominator*(computed denominator (FixedTape.midBox ibox265)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox265).gradient k).lo.natAbs ((computed denominator ibox265).gradient k).hi.natAbs : Int)*((ibox265 k).hi-(ibox265 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox265
    (computed denominator ibox265) (computed denominator (FixedTape.midBox ibox265))
    (by decide +kernel)
private theorem midpoint_even_265 : ∀ k, 2 ∣ (ibox265 k).lo+(ibox265 k).hi := by decide +kernel
private theorem accepted_265 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox265) tree265 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox265 midpoint_even_265
  simp only [tree265,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox265,candidate_valid h (FixedTape.midBox ibox265),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox265 212 (FixedTape.rowsAux denominator ibox265 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox265) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_265
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
private noncomputable def tree263 : TapeTree := .split 3 (((1553952079265378533923225864634827242062479360000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree264 tree265
attribute [irreducible] tree263
private theorem accepted_263 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox263) tree263 = true := by
  simp only [tree263,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox263 3 (1553952079265378533923225864634827242062479360000000000000000 : Int) false,decode_split denominator ibox263 3 (1553952079265378533923225864634827242062479360000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_264 h,accepted_265 h⟩
private noncomputable def tree262 : TapeTree := .split 0 (((1441421294679153706196213414701836447189565440000000000000 : Int) : ℚ)/(denominator : ℚ)) tree263 tree266
attribute [irreducible] tree262
private theorem accepted_262 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox262) tree262 = true := by
  simp only [tree262,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox262 0 (1441421294679153706196213414701836447189565440000000000000 : Int) false,decode_split denominator ibox262 0 (1441421294679153706196213414701836447189565440000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_263 h,accepted_266 h⟩
private noncomputable def tree261 : TapeTree := .split 0 (((1473452879005357121889462601695210590460444672000000000000 : Int) : ℚ)/(denominator : ℚ)) tree262 tree269
attribute [irreducible] tree261
private theorem accepted_261 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox261) tree261 = true := by
  simp only [tree261,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox261 0 (1473452879005357121889462601695210590460444672000000000000 : Int) false,decode_split denominator ibox261 0 (1473452879005357121889462601695210590460444672000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_262 h,accepted_269 h⟩
private noncomputable def tree260 : TapeTree := .split 3 (((1673486854593484574994243238837506260682670080000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree261 tree276
attribute [irreducible] tree260
private theorem accepted_260 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox260) tree260 = true := by
  simp only [tree260,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox260 3 (1673486854593484574994243238837506260682670080000000000000000 : Int) false,decode_split denominator ibox260 3 (1673486854593484574994243238837506260682670080000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_261 h,accepted_276 h⟩
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
private noncomputable def tree258 : TapeTree := .centered (candidateRows ibox258) (candidateRows (FixedTape.midBox ibox258))
attribute [irreducible] tree258
private theorem sign_258 : 2*denominator*(computed denominator (FixedTape.midBox ibox258)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox258).gradient k).lo.natAbs ((computed denominator ibox258).gradient k).hi.natAbs : Int)*((ibox258 k).hi-(ibox258 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox258
    (computed denominator ibox258) (computed denominator (FixedTape.midBox ibox258))
    (by decide +kernel)
private theorem midpoint_even_258 : ∀ k, 2 ∣ (ibox258 k).lo+(ibox258 k).hi := by decide +kernel
private theorem accepted_258 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox258) tree258 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox258 midpoint_even_258
  simp only [tree258,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox258,candidate_valid h (FixedTape.midBox ibox258),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox258 212 (FixedTape.rowsAux denominator ibox258 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox258) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_258
private noncomputable def tree257 : TapeTree := .split 3 (((1314882528609166451781191116229469204822097920000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree258 tree259
attribute [irreducible] tree257
private theorem accepted_257 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox257) tree257 = true := by
  simp only [tree257,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox257 3 (1314882528609166451781191116229469204822097920000000000000000 : Int) false,decode_split denominator ibox257 3 (1314882528609166451781191116229469204822097920000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_258 h,accepted_259 h⟩
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
private noncomputable def tree255 : TapeTree := .centered (candidateRows ibox255) (candidateRows (FixedTape.midBox ibox255))
attribute [irreducible] tree255
private theorem sign_255 : 2*denominator*(computed denominator (FixedTape.midBox ibox255)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox255).gradient k).lo.natAbs ((computed denominator ibox255).gradient k).hi.natAbs : Int)*((ibox255 k).hi-(ibox255 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox255
    (computed denominator ibox255) (computed denominator (FixedTape.midBox ibox255))
    (by decide +kernel)
private theorem midpoint_even_255 : ∀ k, 2 ∣ (ibox255 k).lo+(ibox255 k).hi := by decide +kernel
private theorem accepted_255 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox255) tree255 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox255 midpoint_even_255
  simp only [tree255,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox255,candidate_valid h (FixedTape.midBox ibox255),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox255 212 (FixedTape.rowsAux denominator ibox255 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox255) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_255
private noncomputable def tree254 : TapeTree := .split 3 (((1314882528609166451781191116229469204822097920000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree255 tree256
attribute [irreducible] tree254
private theorem accepted_254 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox254) tree254 = true := by
  simp only [tree254,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox254 3 (1314882528609166451781191116229469204822097920000000000000000 : Int) false,decode_split denominator ibox254 3 (1314882528609166451781191116229469204822097920000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_255 h,accepted_256 h⟩
private noncomputable def tree253 : TapeTree := .split 0 (((1505484463331560537582711788688584733731323904000000000000 : Int) : ℚ)/(denominator : ℚ)) tree254 tree257
attribute [irreducible] tree253
private theorem accepted_253 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox253) tree253 = true := by
  simp only [tree253,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox253 0 (1505484463331560537582711788688584733731323904000000000000 : Int) false,decode_split denominator ibox253 0 (1505484463331560537582711788688584733731323904000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_254 h,accepted_257 h⟩
private noncomputable def tree252 : TapeTree := .centered (candidateRows ibox252) (candidateRows (FixedTape.midBox ibox252))
attribute [irreducible] tree252
private theorem sign_252 : 2*denominator*(computed denominator (FixedTape.midBox ibox252)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox252).gradient k).lo.natAbs ((computed denominator ibox252).gradient k).hi.natAbs : Int)*((ibox252 k).hi-(ibox252 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox252
    (computed denominator ibox252) (computed denominator (FixedTape.midBox ibox252))
    (by decide +kernel)
private theorem midpoint_even_252 : ∀ k, 2 ∣ (ibox252 k).lo+(ibox252 k).hi := by decide +kernel
private theorem accepted_252 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox252) tree252 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox252 midpoint_even_252
  simp only [tree252,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox252,candidate_valid h (FixedTape.midBox ibox252),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox252 212 (FixedTape.rowsAux denominator ibox252 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox252) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_252
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
private noncomputable def tree250 : TapeTree := .split 3 (((1075812977952954369639156367824111167581716480000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree251 tree252
attribute [irreducible] tree250
private theorem accepted_250 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox250) tree250 = true := by
  simp only [tree250,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox250 3 (1075812977952954369639156367824111167581716480000000000000000 : Int) false,decode_split denominator ibox250 3 (1075812977952954369639156367824111167581716480000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_251 h,accepted_252 h⟩
private noncomputable def tree249 : TapeTree := .centered (candidateRows ibox249) (candidateRows (FixedTape.midBox ibox249))
attribute [irreducible] tree249
private theorem sign_249 : 2*denominator*(computed denominator (FixedTape.midBox ibox249)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox249).gradient k).lo.natAbs ((computed denominator ibox249).gradient k).hi.natAbs : Int)*((ibox249 k).hi-(ibox249 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox249
    (computed denominator ibox249) (computed denominator (FixedTape.midBox ibox249))
    (by decide +kernel)
private theorem midpoint_even_249 : ∀ k, 2 ∣ (ibox249 k).lo+(ibox249 k).hi := by decide +kernel
private theorem accepted_249 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox249) tree249 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox249 midpoint_even_249
  simp only [tree249,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox249,candidate_valid h (FixedTape.midBox ibox249),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox249 212 (FixedTape.rowsAux denominator ibox249 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox249) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_249
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
private noncomputable def tree247 : TapeTree := .split 3 (((1075812977952954369639156367824111167581716480000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree248 tree249
attribute [irreducible] tree247
private theorem accepted_247 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox247) tree247 = true := by
  simp only [tree247,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox247 3 (1075812977952954369639156367824111167581716480000000000000000 : Int) false,decode_split denominator ibox247 3 (1075812977952954369639156367824111167581716480000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_248 h,accepted_249 h⟩
private noncomputable def tree246 : TapeTree := .split 0 (((1505484463331560537582711788688584733731323904000000000000 : Int) : ℚ)/(denominator : ℚ)) tree247 tree250
attribute [irreducible] tree246
private theorem accepted_246 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox246) tree246 = true := by
  simp only [tree246,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox246 0 (1505484463331560537582711788688584733731323904000000000000 : Int) false,decode_split denominator ibox246 0 (1505484463331560537582711788688584733731323904000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_247 h,accepted_250 h⟩
private noncomputable def tree245 : TapeTree := .split 3 (((1195347753281060410710173742026790186201907200000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree246 tree253
attribute [irreducible] tree245
private theorem accepted_245 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox245) tree245 = true := by
  simp only [tree245,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox245 3 (1195347753281060410710173742026790186201907200000000000000000 : Int) false,decode_split denominator ibox245 3 (1195347753281060410710173742026790186201907200000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_246 h,accepted_253 h⟩
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
private noncomputable def tree243 : TapeTree := .centered (candidateRows ibox243) (candidateRows (FixedTape.midBox ibox243))
attribute [irreducible] tree243
private theorem sign_243 : 2*denominator*(computed denominator (FixedTape.midBox ibox243)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox243).gradient k).lo.natAbs ((computed denominator ibox243).gradient k).hi.natAbs : Int)*((ibox243 k).hi-(ibox243 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox243
    (computed denominator ibox243) (computed denominator (FixedTape.midBox ibox243))
    (by decide +kernel)
private theorem midpoint_even_243 : ∀ k, 2 ∣ (ibox243 k).lo+(ibox243 k).hi := by decide +kernel
private theorem accepted_243 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox243) tree243 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox243 midpoint_even_243
  simp only [tree243,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox243,candidate_valid h (FixedTape.midBox ibox243),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox243 212 (FixedTape.rowsAux denominator ibox243 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox243) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_243
private noncomputable def tree242 : TapeTree := .split 3 (((1314882528609166451781191116229469204822097920000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree243 tree244
attribute [irreducible] tree242
private theorem accepted_242 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox242) tree242 = true := by
  simp only [tree242,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox242 3 (1314882528609166451781191116229469204822097920000000000000000 : Int) false,decode_split denominator ibox242 3 (1314882528609166451781191116229469204822097920000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_243 h,accepted_244 h⟩
private noncomputable def tree241 : TapeTree := .centered (candidateRows ibox241) (candidateRows (FixedTape.midBox ibox241))
attribute [irreducible] tree241
private theorem sign_241 : 2*denominator*(computed denominator (FixedTape.midBox ibox241)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox241).gradient k).lo.natAbs ((computed denominator ibox241).gradient k).hi.natAbs : Int)*((ibox241 k).hi-(ibox241 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox241
    (computed denominator ibox241) (computed denominator (FixedTape.midBox ibox241))
    (by decide +kernel)
private theorem midpoint_even_241 : ∀ k, 2 ∣ (ibox241 k).lo+(ibox241 k).hi := by decide +kernel
private theorem accepted_241 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox241) tree241 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox241 midpoint_even_241
  simp only [tree241,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox241,candidate_valid h (FixedTape.midBox ibox241),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox241 212 (FixedTape.rowsAux denominator ibox241 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox241) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_241
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
private noncomputable def tree239 : TapeTree := .split 3 (((1314882528609166451781191116229469204822097920000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree240 tree241
attribute [irreducible] tree239
private theorem accepted_239 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox239) tree239 = true := by
  simp only [tree239,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox239 3 (1314882528609166451781191116229469204822097920000000000000000 : Int) false,decode_split denominator ibox239 3 (1314882528609166451781191116229469204822097920000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_240 h,accepted_241 h⟩
private noncomputable def tree238 : TapeTree := .split 0 (((1441421294679153706196213414701836447189565440000000000000 : Int) : ℚ)/(denominator : ℚ)) tree239 tree242
attribute [irreducible] tree238
private theorem accepted_238 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox238) tree238 = true := by
  simp only [tree238,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox238 0 (1441421294679153706196213414701836447189565440000000000000 : Int) false,decode_split denominator ibox238 0 (1441421294679153706196213414701836447189565440000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_239 h,accepted_242 h⟩
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
private noncomputable def tree235 : TapeTree := .split 3 (((1075812977952954369639156367824111167581716480000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree236 tree237
attribute [irreducible] tree235
private theorem accepted_235 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox235) tree235 = true := by
  simp only [tree235,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox235 3 (1075812977952954369639156367824111167581716480000000000000000 : Int) false,decode_split denominator ibox235 3 (1075812977952954369639156367824111167581716480000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_236 h,accepted_237 h⟩
private noncomputable def tree234 : TapeTree := .centered (candidateRows ibox234) (candidateRows (FixedTape.midBox ibox234))
attribute [irreducible] tree234
private theorem sign_234 : 2*denominator*(computed denominator (FixedTape.midBox ibox234)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox234).gradient k).lo.natAbs ((computed denominator ibox234).gradient k).hi.natAbs : Int)*((ibox234 k).hi-(ibox234 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox234
    (computed denominator ibox234) (computed denominator (FixedTape.midBox ibox234))
    (by decide +kernel)
private theorem midpoint_even_234 : ∀ k, 2 ∣ (ibox234 k).lo+(ibox234 k).hi := by decide +kernel
private theorem accepted_234 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox234) tree234 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox234 midpoint_even_234
  simp only [tree234,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox234,candidate_valid h (FixedTape.midBox ibox234),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox234 212 (FixedTape.rowsAux denominator ibox234 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox234) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_234
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
private noncomputable def tree232 : TapeTree := .split 3 (((1075812977952954369639156367824111167581716480000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree233 tree234
attribute [irreducible] tree232
private theorem accepted_232 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox232) tree232 = true := by
  simp only [tree232,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox232 3 (1075812977952954369639156367824111167581716480000000000000000 : Int) false,decode_split denominator ibox232 3 (1075812977952954369639156367824111167581716480000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_233 h,accepted_234 h⟩
private noncomputable def tree231 : TapeTree := .split 0 (((1441421294679153706196213414701836447189565440000000000000 : Int) : ℚ)/(denominator : ℚ)) tree232 tree235
attribute [irreducible] tree231
private theorem accepted_231 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox231) tree231 = true := by
  simp only [tree231,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox231 0 (1441421294679153706196213414701836447189565440000000000000 : Int) false,decode_split denominator ibox231 0 (1441421294679153706196213414701836447189565440000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_232 h,accepted_235 h⟩
private noncomputable def tree230 : TapeTree := .split 3 (((1195347753281060410710173742026790186201907200000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree231 tree238
attribute [irreducible] tree230
private theorem accepted_230 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox230) tree230 = true := by
  simp only [tree230,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox230 3 (1195347753281060410710173742026790186201907200000000000000000 : Int) false,decode_split denominator ibox230 3 (1195347753281060410710173742026790186201907200000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_231 h,accepted_238 h⟩
private noncomputable def tree229 : TapeTree := .split 0 (((1473452879005357121889462601695210590460444672000000000000 : Int) : ℚ)/(denominator : ℚ)) tree230 tree245
attribute [irreducible] tree229
private theorem accepted_229 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox229) tree229 = true := by
  simp only [tree229,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox229 0 (1473452879005357121889462601695210590460444672000000000000 : Int) false,decode_split denominator ibox229 0 (1473452879005357121889462601695210590460444672000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_230 h,accepted_245 h⟩
private noncomputable def tree228 : TapeTree := .split 3 (((1434417303937272492852208490432148223442288640000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree229 tree260
attribute [irreducible] tree228
private theorem accepted_228 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox228) tree228 = true := by
  simp only [tree228,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox228 3 (1434417303937272492852208490432148223442288640000000000000000 : Int) false,decode_split denominator ibox228 3 (1434417303937272492852208490432148223442288640000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_229 h,accepted_260 h⟩
private noncomputable def tree227 : TapeTree := .centered (candidateRows ibox227) (candidateRows (FixedTape.midBox ibox227))
attribute [irreducible] tree227
private theorem sign_227 : 2*denominator*(computed denominator (FixedTape.midBox ibox227)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox227).gradient k).lo.natAbs ((computed denominator ibox227).gradient k).hi.natAbs : Int)*((ibox227 k).hi-(ibox227 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox227
    (computed denominator ibox227) (computed denominator (FixedTape.midBox ibox227))
    (by decide +kernel)
private theorem midpoint_even_227 : ∀ k, 2 ∣ (ibox227 k).lo+(ibox227 k).hi := by decide +kernel
private theorem accepted_227 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox227) tree227 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox227 midpoint_even_227
  simp only [tree227,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox227,candidate_valid h (FixedTape.midBox ibox227),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox227 212 (FixedTape.rowsAux denominator ibox227 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox227) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_227
private noncomputable def tree226 : TapeTree := .centered (candidateRows ibox226) (candidateRows (FixedTape.midBox ibox226))
attribute [irreducible] tree226
private theorem sign_226 : 2*denominator*(computed denominator (FixedTape.midBox ibox226)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox226).gradient k).lo.natAbs ((computed denominator ibox226).gradient k).hi.natAbs : Int)*((ibox226 k).hi-(ibox226 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox226
    (computed denominator ibox226) (computed denominator (FixedTape.midBox ibox226))
    (by decide +kernel)
private theorem midpoint_even_226 : ∀ k, 2 ∣ (ibox226 k).lo+(ibox226 k).hi := by decide +kernel
private theorem accepted_226 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox226) tree226 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox226 midpoint_even_226
  simp only [tree226,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox226,candidate_valid h (FixedTape.midBox ibox226),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox226 212 (FixedTape.rowsAux denominator ibox226 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox226) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_226
private noncomputable def tree225 : TapeTree := .split 3 (((836743427296742287497121619418753130341335040000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree226 tree227
attribute [irreducible] tree225
private theorem accepted_225 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox225) tree225 = true := by
  simp only [tree225,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox225 3 (836743427296742287497121619418753130341335040000000000000000 : Int) false,decode_split denominator ibox225 3 (836743427296742287497121619418753130341335040000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_226 h,accepted_227 h⟩
private noncomputable def tree224 : TapeTree := .centered (candidateRows ibox224) (candidateRows (FixedTape.midBox ibox224))
attribute [irreducible] tree224
private theorem sign_224 : 2*denominator*(computed denominator (FixedTape.midBox ibox224)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox224).gradient k).lo.natAbs ((computed denominator ibox224).gradient k).hi.natAbs : Int)*((ibox224 k).hi-(ibox224 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox224
    (computed denominator ibox224) (computed denominator (FixedTape.midBox ibox224))
    (by decide +kernel)
private theorem midpoint_even_224 : ∀ k, 2 ∣ (ibox224 k).lo+(ibox224 k).hi := by decide +kernel
private theorem accepted_224 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox224) tree224 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox224 midpoint_even_224
  simp only [tree224,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox224,candidate_valid h (FixedTape.midBox ibox224),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox224 212 (FixedTape.rowsAux denominator ibox224 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox224) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_224
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
private noncomputable def tree222 : TapeTree := .split 3 (((836743427296742287497121619418753130341335040000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree223 tree224
attribute [irreducible] tree222
private theorem accepted_222 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox222) tree222 = true := by
  simp only [tree222,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox222 3 (836743427296742287497121619418753130341335040000000000000000 : Int) false,decode_split denominator ibox222 3 (836743427296742287497121619418753130341335040000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_223 h,accepted_224 h⟩
private noncomputable def tree221 : TapeTree := .split 0 (((1505484463331560537582711788688584733731323904000000000000 : Int) : ℚ)/(denominator : ℚ)) tree222 tree225
attribute [irreducible] tree221
private theorem accepted_221 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox221) tree221 = true := by
  simp only [tree221,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox221 0 (1505484463331560537582711788688584733731323904000000000000 : Int) false,decode_split denominator ibox221 0 (1505484463331560537582711788688584733731323904000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_222 h,accepted_225 h⟩
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
private noncomputable def tree218 : TapeTree := .split 3 (((597673876640530205355086871013395093100953600000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree219 tree220
attribute [irreducible] tree218
private theorem accepted_218 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox218) tree218 = true := by
  simp only [tree218,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox218 3 (597673876640530205355086871013395093100953600000000000000000 : Int) false,decode_split denominator ibox218 3 (597673876640530205355086871013395093100953600000000000000000 : Int) true]
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
private noncomputable def tree215 : TapeTree := .split 3 (((597673876640530205355086871013395093100953600000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree216 tree217
attribute [irreducible] tree215
private theorem accepted_215 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox215) tree215 = true := by
  simp only [tree215,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox215 3 (597673876640530205355086871013395093100953600000000000000000 : Int) false,decode_split denominator ibox215 3 (597673876640530205355086871013395093100953600000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_216 h,accepted_217 h⟩
private noncomputable def tree214 : TapeTree := .split 0 (((1505484463331560537582711788688584733731323904000000000000 : Int) : ℚ)/(denominator : ℚ)) tree215 tree218
attribute [irreducible] tree214
private theorem accepted_214 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox214) tree214 = true := by
  simp only [tree214,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox214 0 (1505484463331560537582711788688584733731323904000000000000 : Int) false,decode_split denominator ibox214 0 (1505484463331560537582711788688584733731323904000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_215 h,accepted_218 h⟩
private noncomputable def tree213 : TapeTree := .split 3 (((717208651968636246426104245216074111721144320000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree214 tree221
attribute [irreducible] tree213
private theorem accepted_213 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox213) tree213 = true := by
  simp only [tree213,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox213 3 (717208651968636246426104245216074111721144320000000000000000 : Int) false,decode_split denominator ibox213 3 (717208651968636246426104245216074111721144320000000000000000 : Int) true]
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
private noncomputable def tree210 : TapeTree := .split 3 (((836743427296742287497121619418753130341335040000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree211 tree212
attribute [irreducible] tree210
private theorem accepted_210 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox210) tree210 = true := by
  simp only [tree210,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox210 3 (836743427296742287497121619418753130341335040000000000000000 : Int) false,decode_split denominator ibox210 3 (836743427296742287497121619418753130341335040000000000000000 : Int) true]
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
private noncomputable def tree207 : TapeTree := .split 3 (((836743427296742287497121619418753130341335040000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree208 tree209
attribute [irreducible] tree207
private theorem accepted_207 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox207) tree207 = true := by
  simp only [tree207,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox207 3 (836743427296742287497121619418753130341335040000000000000000 : Int) false,decode_split denominator ibox207 3 (836743427296742287497121619418753130341335040000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_208 h,accepted_209 h⟩
private noncomputable def tree206 : TapeTree := .split 0 (((1441421294679153706196213414701836447189565440000000000000 : Int) : ℚ)/(denominator : ℚ)) tree207 tree210
attribute [irreducible] tree206
private theorem accepted_206 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox206) tree206 = true := by
  simp only [tree206,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox206 0 (1441421294679153706196213414701836447189565440000000000000 : Int) false,decode_split denominator ibox206 0 (1441421294679153706196213414701836447189565440000000000000 : Int) true]
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
private noncomputable def tree203 : TapeTree := .split 3 (((597673876640530205355086871013395093100953600000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree204 tree205
attribute [irreducible] tree203
private theorem accepted_203 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox203) tree203 = true := by
  simp only [tree203,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox203 3 (597673876640530205355086871013395093100953600000000000000000 : Int) false,decode_split denominator ibox203 3 (597673876640530205355086871013395093100953600000000000000000 : Int) true]
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
private noncomputable def tree200 : TapeTree := .split 3 (((597673876640530205355086871013395093100953600000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree201 tree202
attribute [irreducible] tree200
private theorem accepted_200 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox200) tree200 = true := by
  simp only [tree200,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox200 3 (597673876640530205355086871013395093100953600000000000000000 : Int) false,decode_split denominator ibox200 3 (597673876640530205355086871013395093100953600000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_201 h,accepted_202 h⟩
private noncomputable def tree199 : TapeTree := .split 0 (((1441421294679153706196213414701836447189565440000000000000 : Int) : ℚ)/(denominator : ℚ)) tree200 tree203
attribute [irreducible] tree199
private theorem accepted_199 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox199) tree199 = true := by
  simp only [tree199,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox199 0 (1441421294679153706196213414701836447189565440000000000000 : Int) false,decode_split denominator ibox199 0 (1441421294679153706196213414701836447189565440000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_200 h,accepted_203 h⟩
private noncomputable def tree198 : TapeTree := .split 3 (((717208651968636246426104245216074111721144320000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree199 tree206
attribute [irreducible] tree198
private theorem accepted_198 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox198) tree198 = true := by
  simp only [tree198,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox198 3 (717208651968636246426104245216074111721144320000000000000000 : Int) false,decode_split denominator ibox198 3 (717208651968636246426104245216074111721144320000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_199 h,accepted_206 h⟩
private noncomputable def tree197 : TapeTree := .split 0 (((1473452879005357121889462601695210590460444672000000000000 : Int) : ℚ)/(denominator : ℚ)) tree198 tree213
attribute [irreducible] tree197
private theorem accepted_197 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox197) tree197 = true := by
  simp only [tree197,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox197 0 (1473452879005357121889462601695210590460444672000000000000 : Int) false,decode_split denominator ibox197 0 (1473452879005357121889462601695210590460444672000000000000 : Int) true]
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
private noncomputable def tree194 : TapeTree := .split 3 (((358604325984318123213052122608037055860572160000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree195 tree196
attribute [irreducible] tree194
private theorem accepted_194 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox194) tree194 = true := by
  simp only [tree194,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox194 3 (358604325984318123213052122608037055860572160000000000000000 : Int) false,decode_split denominator ibox194 3 (358604325984318123213052122608037055860572160000000000000000 : Int) true]
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
private noncomputable def tree191 : TapeTree := .split 3 (((358604325984318123213052122608037055860572160000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree192 tree193
attribute [irreducible] tree191
private theorem accepted_191 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox191) tree191 = true := by
  simp only [tree191,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox191 3 (358604325984318123213052122608037055860572160000000000000000 : Int) false,decode_split denominator ibox191 3 (358604325984318123213052122608037055860572160000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_192 h,accepted_193 h⟩
private noncomputable def tree190 : TapeTree := .split 0 (((1505484463331560537582711788688584733731323904000000000000 : Int) : ℚ)/(denominator : ℚ)) tree191 tree194
attribute [irreducible] tree190
private theorem accepted_190 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox190) tree190 = true := by
  simp only [tree190,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox190 0 (1505484463331560537582711788688584733731323904000000000000 : Int) false,decode_split denominator ibox190 0 (1505484463331560537582711788688584733731323904000000000000 : Int) true]
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
private noncomputable def tree187 : TapeTree := .split 3 (((119534775328106041071017374202679018620190720000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree188 tree189
attribute [irreducible] tree187
private theorem accepted_187 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox187) tree187 = true := by
  simp only [tree187,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox187 3 (119534775328106041071017374202679018620190720000000000000000 : Int) false,decode_split denominator ibox187 3 (119534775328106041071017374202679018620190720000000000000000 : Int) true]
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
private noncomputable def tree184 : TapeTree := .split 0 (((1489468671168458829736087195191897662095884288000000000000 : Int) : ℚ)/(denominator : ℚ)) tree185 tree186
attribute [irreducible] tree184
private theorem accepted_184 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox184) tree184 = true := by
  simp only [tree184,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox184 0 (1489468671168458829736087195191897662095884288000000000000 : Int) false,decode_split denominator ibox184 0 (1489468671168458829736087195191897662095884288000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_185 h,accepted_186 h⟩
private noncomputable def tree183 : TapeTree := .split 0 (((1505484463331560537582711788688584733731323904000000000000 : Int) : ℚ)/(denominator : ℚ)) tree184 tree187
attribute [irreducible] tree183
private theorem accepted_183 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox183) tree183 = true := by
  simp only [tree183,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox183 0 (1505484463331560537582711788688584733731323904000000000000 : Int) false,decode_split denominator ibox183 0 (1505484463331560537582711788688584733731323904000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_184 h,accepted_187 h⟩
private noncomputable def tree182 : TapeTree := .split 3 (((239069550656212082142034748405358037240381440000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree183 tree190
attribute [irreducible] tree182
private theorem accepted_182 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox182) tree182 = true := by
  simp only [tree182,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox182 3 (239069550656212082142034748405358037240381440000000000000000 : Int) false,decode_split denominator ibox182 3 (239069550656212082142034748405358037240381440000000000000000 : Int) true]
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
private noncomputable def tree179 : TapeTree := .split 3 (((358604325984318123213052122608037055860572160000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree180 tree181
attribute [irreducible] tree179
private theorem accepted_179 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox179) tree179 = true := by
  simp only [tree179,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox179 3 (358604325984318123213052122608037055860572160000000000000000 : Int) false,decode_split denominator ibox179 3 (358604325984318123213052122608037055860572160000000000000000 : Int) true]
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
private noncomputable def tree176 : TapeTree := .split 3 (((358604325984318123213052122608037055860572160000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree177 tree178
attribute [irreducible] tree176
private theorem accepted_176 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox176) tree176 = true := by
  simp only [tree176,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox176 3 (358604325984318123213052122608037055860572160000000000000000 : Int) false,decode_split denominator ibox176 3 (358604325984318123213052122608037055860572160000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_177 h,accepted_178 h⟩
private noncomputable def tree175 : TapeTree := .split 0 (((1441421294679153706196213414701836447189565440000000000000 : Int) : ℚ)/(denominator : ℚ)) tree176 tree179
attribute [irreducible] tree175
private theorem accepted_175 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox175) tree175 = true := by
  simp only [tree175,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox175 0 (1441421294679153706196213414701836447189565440000000000000 : Int) false,decode_split denominator ibox175 0 (1441421294679153706196213414701836447189565440000000000000 : Int) true]
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
private noncomputable def tree172 : TapeTree := .split 0 (((1457437086842255414042838008198523518825005056000000000000 : Int) : ℚ)/(denominator : ℚ)) tree173 tree174
attribute [irreducible] tree172
private theorem accepted_172 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox172) tree172 = true := by
  simp only [tree172,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox172 0 (1457437086842255414042838008198523518825005056000000000000 : Int) false,decode_split denominator ibox172 0 (1457437086842255414042838008198523518825005056000000000000 : Int) true]
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
private noncomputable def tree169 : TapeTree := .split 0 (((1425405502516051998349588821205149375554125824000000000000 : Int) : ℚ)/(denominator : ℚ)) tree170 tree171
attribute [irreducible] tree169
private theorem accepted_169 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox169) tree169 = true := by
  simp only [tree169,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox169 0 (1425405502516051998349588821205149375554125824000000000000 : Int) false,decode_split denominator ibox169 0 (1425405502516051998349588821205149375554125824000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_170 h,accepted_171 h⟩
private noncomputable def tree168 : TapeTree := .split 0 (((1441421294679153706196213414701836447189565440000000000000 : Int) : ℚ)/(denominator : ℚ)) tree169 tree172
attribute [irreducible] tree168
private theorem accepted_168 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox168) tree168 = true := by
  simp only [tree168,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox168 0 (1441421294679153706196213414701836447189565440000000000000 : Int) false,decode_split denominator ibox168 0 (1441421294679153706196213414701836447189565440000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_169 h,accepted_172 h⟩
private noncomputable def tree167 : TapeTree := .split 3 (((239069550656212082142034748405358037240381440000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree168 tree175
attribute [irreducible] tree167
private theorem accepted_167 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox167) tree167 = true := by
  simp only [tree167,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox167 3 (239069550656212082142034748405358037240381440000000000000000 : Int) false,decode_split denominator ibox167 3 (239069550656212082142034748405358037240381440000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_168 h,accepted_175 h⟩
private noncomputable def tree166 : TapeTree := .split 0 (((1473452879005357121889462601695210590460444672000000000000 : Int) : ℚ)/(denominator : ℚ)) tree167 tree182
attribute [irreducible] tree166
private theorem accepted_166 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox166) tree166 = true := by
  simp only [tree166,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox166 0 (1473452879005357121889462601695210590460444672000000000000 : Int) false,decode_split denominator ibox166 0 (1473452879005357121889462601695210590460444672000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_167 h,accepted_182 h⟩
private noncomputable def tree165 : TapeTree := .split 3 (((478139101312424164284069496810716074480762880000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree166 tree197
attribute [irreducible] tree165
private theorem accepted_165 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox165) tree165 = true := by
  simp only [tree165,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox165 3 (478139101312424164284069496810716074480762880000000000000000 : Int) false,decode_split denominator ibox165 3 (478139101312424164284069496810716074480762880000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_166 h,accepted_197 h⟩
private noncomputable def tree164 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree165 tree228
attribute [irreducible] tree164
private theorem accepted_164 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox164) tree164 = true := by
  simp only [tree164,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox164 3 (956278202624848328568138993621432148961525760000000000000000 : Int) false,decode_split denominator ibox164 3 (956278202624848328568138993621432148961525760000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_165 h,accepted_228 h⟩
private noncomputable def tree163 : TapeTree := .face 1 false (candidateRows ibox163) tree164
attribute [irreducible] tree163
private theorem sign_163 : ((computed denominator ibox163).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_163 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox163) tree163 = true := by
  simp only [tree163,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox163,?_,accepted_164 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox163)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox163).gradient 1).hi) denominator_positive).1 sign_163
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
private noncomputable def tree161 : TapeTree := .centered (candidateRows ibox161) (candidateRows (FixedTape.midBox ibox161))
attribute [irreducible] tree161
private theorem sign_161 : 2*denominator*(computed denominator (FixedTape.midBox ibox161)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox161).gradient k).lo.natAbs ((computed denominator ibox161).gradient k).hi.natAbs : Int)*((ibox161 k).hi-(ibox161 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox161
    (computed denominator ibox161) (computed denominator (FixedTape.midBox ibox161))
    (by decide +kernel)
private theorem midpoint_even_161 : ∀ k, 2 ∣ (ibox161 k).lo+(ibox161 k).hi := by decide +kernel
private theorem accepted_161 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox161) tree161 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox161 midpoint_even_161
  simp only [tree161,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox161,candidate_valid h (FixedTape.midBox ibox161),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox161 212 (FixedTape.rowsAux denominator ibox161 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox161) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_161
private noncomputable def tree160 : TapeTree := .split 0 (((1377358126026746874809715040715088160647806976000000000000 : Int) : ℚ)/(denominator : ℚ)) tree161 tree162
attribute [irreducible] tree160
private theorem accepted_160 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox160) tree160 = true := by
  simp only [tree160,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox160 0 (1377358126026746874809715040715088160647806976000000000000 : Int) false,decode_split denominator ibox160 0 (1377358126026746874809715040715088160647806976000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_161 h,accepted_162 h⟩
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
private noncomputable def tree158 : TapeTree := .centered (candidateRows ibox158) (candidateRows (FixedTape.midBox ibox158))
attribute [irreducible] tree158
private theorem sign_158 : 2*denominator*(computed denominator (FixedTape.midBox ibox158)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox158).gradient k).lo.natAbs ((computed denominator ibox158).gradient k).hi.natAbs : Int)*((ibox158 k).hi-(ibox158 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox158
    (computed denominator ibox158) (computed denominator (FixedTape.midBox ibox158))
    (by decide +kernel)
private theorem midpoint_even_158 : ∀ k, 2 ∣ (ibox158 k).lo+(ibox158 k).hi := by decide +kernel
private theorem accepted_158 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox158) tree158 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox158 midpoint_even_158
  simp only [tree158,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox158,candidate_valid h (FixedTape.midBox ibox158),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox158 212 (FixedTape.rowsAux denominator ibox158 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox158) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_158
private noncomputable def tree157 : TapeTree := .split 0 (((1377358126026746874809715040715088160647806976000000000000 : Int) : ℚ)/(denominator : ℚ)) tree158 tree159
attribute [irreducible] tree157
private theorem accepted_157 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox157) tree157 = true := by
  simp only [tree157,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox157 0 (1377358126026746874809715040715088160647806976000000000000 : Int) false,decode_split denominator ibox157 0 (1377358126026746874809715040715088160647806976000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_158 h,accepted_159 h⟩
private noncomputable def tree156 : TapeTree := .split 3 (((1793021629921590616065260613040185279302860800000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree157 tree160
attribute [irreducible] tree156
private theorem accepted_156 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox156) tree156 = true := by
  simp only [tree156,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox156 3 (1793021629921590616065260613040185279302860800000000000000000 : Int) false,decode_split denominator ibox156 3 (1793021629921590616065260613040185279302860800000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_157 h,accepted_160 h⟩
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
private noncomputable def tree154 : TapeTree := .centered (candidateRows ibox154) (candidateRows (FixedTape.midBox ibox154))
attribute [irreducible] tree154
private theorem sign_154 : 2*denominator*(computed denominator (FixedTape.midBox ibox154)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox154).gradient k).lo.natAbs ((computed denominator ibox154).gradient k).hi.natAbs : Int)*((ibox154 k).hi-(ibox154 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox154
    (computed denominator ibox154) (computed denominator (FixedTape.midBox ibox154))
    (by decide +kernel)
private theorem midpoint_even_154 : ∀ k, 2 ∣ (ibox154 k).lo+(ibox154 k).hi := by decide +kernel
private theorem accepted_154 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox154) tree154 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox154 midpoint_even_154
  simp only [tree154,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox154,candidate_valid h (FixedTape.midBox ibox154),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox154 212 (FixedTape.rowsAux denominator ibox154 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox154) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_154
private noncomputable def tree153 : TapeTree := .split 0 (((1313294957374340043423216666728339874106048512000000000000 : Int) : ℚ)/(denominator : ℚ)) tree154 tree155
attribute [irreducible] tree153
private theorem accepted_153 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox153) tree153 = true := by
  simp only [tree153,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox153 0 (1313294957374340043423216666728339874106048512000000000000 : Int) false,decode_split denominator ibox153 0 (1313294957374340043423216666728339874106048512000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_154 h,accepted_155 h⟩
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
private noncomputable def tree151 : TapeTree := .centered (candidateRows ibox151) (candidateRows (FixedTape.midBox ibox151))
attribute [irreducible] tree151
private theorem sign_151 : 2*denominator*(computed denominator (FixedTape.midBox ibox151)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox151).gradient k).lo.natAbs ((computed denominator ibox151).gradient k).hi.natAbs : Int)*((ibox151 k).hi-(ibox151 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox151
    (computed denominator ibox151) (computed denominator (FixedTape.midBox ibox151))
    (by decide +kernel)
private theorem midpoint_even_151 : ∀ k, 2 ∣ (ibox151 k).lo+(ibox151 k).hi := by decide +kernel
private theorem accepted_151 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox151) tree151 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox151 midpoint_even_151
  simp only [tree151,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox151,candidate_valid h (FixedTape.midBox ibox151),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox151 212 (FixedTape.rowsAux denominator ibox151 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox151) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_151
private noncomputable def tree150 : TapeTree := .split 0 (((1313294957374340043423216666728339874106048512000000000000 : Int) : ℚ)/(denominator : ℚ)) tree151 tree152
attribute [irreducible] tree150
private theorem accepted_150 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox150) tree150 = true := by
  simp only [tree150,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox150 0 (1313294957374340043423216666728339874106048512000000000000 : Int) false,decode_split denominator ibox150 0 (1313294957374340043423216666728339874106048512000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_151 h,accepted_152 h⟩
private noncomputable def tree149 : TapeTree := .split 3 (((1793021629921590616065260613040185279302860800000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree150 tree153
attribute [irreducible] tree149
private theorem accepted_149 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox149) tree149 = true := by
  simp only [tree149,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox149 3 (1793021629921590616065260613040185279302860800000000000000000 : Int) false,decode_split denominator ibox149 3 (1793021629921590616065260613040185279302860800000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_150 h,accepted_153 h⟩
private noncomputable def tree148 : TapeTree := .split 0 (((1345326541700543459116465853721714017376927744000000000000 : Int) : ℚ)/(denominator : ℚ)) tree149 tree156
attribute [irreducible] tree148
private theorem accepted_148 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox148) tree148 = true := by
  simp only [tree148,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox148 0 (1345326541700543459116465853721714017376927744000000000000 : Int) false,decode_split denominator ibox148 0 (1345326541700543459116465853721714017376927744000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_149 h,accepted_156 h⟩
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
private noncomputable def tree146 : TapeTree := .centered (candidateRows ibox146) (candidateRows (FixedTape.midBox ibox146))
attribute [irreducible] tree146
private theorem sign_146 : 2*denominator*(computed denominator (FixedTape.midBox ibox146)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox146).gradient k).lo.natAbs ((computed denominator ibox146).gradient k).hi.natAbs : Int)*((ibox146 k).hi-(ibox146 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox146
    (computed denominator ibox146) (computed denominator (FixedTape.midBox ibox146))
    (by decide +kernel)
private theorem midpoint_even_146 : ∀ k, 2 ∣ (ibox146 k).lo+(ibox146 k).hi := by decide +kernel
private theorem accepted_146 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox146) tree146 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox146 midpoint_even_146
  simp only [tree146,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox146,candidate_valid h (FixedTape.midBox ibox146),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox146 212 (FixedTape.rowsAux denominator ibox146 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox146) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_146
private noncomputable def tree145 : TapeTree := .split 3 (((1553952079265378533923225864634827242062479360000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree146 tree147
attribute [irreducible] tree145
private theorem accepted_145 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox145) tree145 = true := by
  simp only [tree145,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox145 3 (1553952079265378533923225864634827242062479360000000000000000 : Int) false,decode_split denominator ibox145 3 (1553952079265378533923225864634827242062479360000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_146 h,accepted_147 h⟩
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
private noncomputable def tree143 : TapeTree := .centered (candidateRows ibox143) (candidateRows (FixedTape.midBox ibox143))
attribute [irreducible] tree143
private theorem sign_143 : 2*denominator*(computed denominator (FixedTape.midBox ibox143)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox143).gradient k).lo.natAbs ((computed denominator ibox143).gradient k).hi.natAbs : Int)*((ibox143 k).hi-(ibox143 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox143
    (computed denominator ibox143) (computed denominator (FixedTape.midBox ibox143))
    (by decide +kernel)
private theorem midpoint_even_143 : ∀ k, 2 ∣ (ibox143 k).lo+(ibox143 k).hi := by decide +kernel
private theorem accepted_143 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox143) tree143 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox143 midpoint_even_143
  simp only [tree143,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox143,candidate_valid h (FixedTape.midBox ibox143),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox143 212 (FixedTape.rowsAux denominator ibox143 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox143) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_143
private noncomputable def tree142 : TapeTree := .split 3 (((1553952079265378533923225864634827242062479360000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree143 tree144
attribute [irreducible] tree142
private theorem accepted_142 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox142) tree142 = true := by
  simp only [tree142,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox142 3 (1553952079265378533923225864634827242062479360000000000000000 : Int) false,decode_split denominator ibox142 3 (1553952079265378533923225864634827242062479360000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_143 h,accepted_144 h⟩
private noncomputable def tree141 : TapeTree := .split 0 (((1377358126026746874809715040715088160647806976000000000000 : Int) : ℚ)/(denominator : ℚ)) tree142 tree145
attribute [irreducible] tree141
private theorem accepted_141 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox141) tree141 = true := by
  simp only [tree141,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox141 0 (1377358126026746874809715040715088160647806976000000000000 : Int) false,decode_split denominator ibox141 0 (1377358126026746874809715040715088160647806976000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_142 h,accepted_145 h⟩
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
private noncomputable def tree139 : TapeTree := .centered (candidateRows ibox139) (candidateRows (FixedTape.midBox ibox139))
attribute [irreducible] tree139
private theorem sign_139 : 2*denominator*(computed denominator (FixedTape.midBox ibox139)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox139).gradient k).lo.natAbs ((computed denominator ibox139).gradient k).hi.natAbs : Int)*((ibox139 k).hi-(ibox139 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox139
    (computed denominator ibox139) (computed denominator (FixedTape.midBox ibox139))
    (by decide +kernel)
private theorem midpoint_even_139 : ∀ k, 2 ∣ (ibox139 k).lo+(ibox139 k).hi := by decide +kernel
private theorem accepted_139 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox139) tree139 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox139 midpoint_even_139
  simp only [tree139,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox139,candidate_valid h (FixedTape.midBox ibox139),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox139 212 (FixedTape.rowsAux denominator ibox139 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox139) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_139
private noncomputable def tree138 : TapeTree := .split 3 (((1553952079265378533923225864634827242062479360000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree139 tree140
attribute [irreducible] tree138
private theorem accepted_138 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox138) tree138 = true := by
  simp only [tree138,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox138 3 (1553952079265378533923225864634827242062479360000000000000000 : Int) false,decode_split denominator ibox138 3 (1553952079265378533923225864634827242062479360000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_139 h,accepted_140 h⟩
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
private noncomputable def tree136 : TapeTree := .centered (candidateRows ibox136) (candidateRows (FixedTape.midBox ibox136))
attribute [irreducible] tree136
private theorem sign_136 : 2*denominator*(computed denominator (FixedTape.midBox ibox136)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox136).gradient k).lo.natAbs ((computed denominator ibox136).gradient k).hi.natAbs : Int)*((ibox136 k).hi-(ibox136 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox136
    (computed denominator ibox136) (computed denominator (FixedTape.midBox ibox136))
    (by decide +kernel)
private theorem midpoint_even_136 : ∀ k, 2 ∣ (ibox136 k).lo+(ibox136 k).hi := by decide +kernel
private theorem accepted_136 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox136) tree136 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox136 midpoint_even_136
  simp only [tree136,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox136,candidate_valid h (FixedTape.midBox ibox136),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox136 212 (FixedTape.rowsAux denominator ibox136 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox136) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_136
private noncomputable def tree135 : TapeTree := .split 3 (((1553952079265378533923225864634827242062479360000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree136 tree137
attribute [irreducible] tree135
private theorem accepted_135 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox135) tree135 = true := by
  simp only [tree135,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox135 3 (1553952079265378533923225864634827242062479360000000000000000 : Int) false,decode_split denominator ibox135 3 (1553952079265378533923225864634827242062479360000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_136 h,accepted_137 h⟩
private noncomputable def tree134 : TapeTree := .split 0 (((1313294957374340043423216666728339874106048512000000000000 : Int) : ℚ)/(denominator : ℚ)) tree135 tree138
attribute [irreducible] tree134
private theorem accepted_134 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox134) tree134 = true := by
  simp only [tree134,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox134 0 (1313294957374340043423216666728339874106048512000000000000 : Int) false,decode_split denominator ibox134 0 (1313294957374340043423216666728339874106048512000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_135 h,accepted_138 h⟩
private noncomputable def tree133 : TapeTree := .split 0 (((1345326541700543459116465853721714017376927744000000000000 : Int) : ℚ)/(denominator : ℚ)) tree134 tree141
attribute [irreducible] tree133
private theorem accepted_133 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox133) tree133 = true := by
  simp only [tree133,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox133 0 (1345326541700543459116465853721714017376927744000000000000 : Int) false,decode_split denominator ibox133 0 (1345326541700543459116465853721714017376927744000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_134 h,accepted_141 h⟩
private noncomputable def tree132 : TapeTree := .split 3 (((1673486854593484574994243238837506260682670080000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree133 tree148
attribute [irreducible] tree132
private theorem accepted_132 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox132) tree132 = true := by
  simp only [tree132,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox132 3 (1673486854593484574994243238837506260682670080000000000000000 : Int) false,decode_split denominator ibox132 3 (1673486854593484574994243238837506260682670080000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_133 h,accepted_148 h⟩
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
private noncomputable def tree130 : TapeTree := .centered (candidateRows ibox130) (candidateRows (FixedTape.midBox ibox130))
attribute [irreducible] tree130
private theorem sign_130 : 2*denominator*(computed denominator (FixedTape.midBox ibox130)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox130).gradient k).lo.natAbs ((computed denominator ibox130).gradient k).hi.natAbs : Int)*((ibox130 k).hi-(ibox130 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox130
    (computed denominator ibox130) (computed denominator (FixedTape.midBox ibox130))
    (by decide +kernel)
private theorem midpoint_even_130 : ∀ k, 2 ∣ (ibox130 k).lo+(ibox130 k).hi := by decide +kernel
private theorem accepted_130 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox130) tree130 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox130 midpoint_even_130
  simp only [tree130,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox130,candidate_valid h (FixedTape.midBox ibox130),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox130 212 (FixedTape.rowsAux denominator ibox130 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox130) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_130
private noncomputable def tree129 : TapeTree := .split 3 (((1314882528609166451781191116229469204822097920000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree130 tree131
attribute [irreducible] tree129
private theorem accepted_129 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox129) tree129 = true := by
  simp only [tree129,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox129 3 (1314882528609166451781191116229469204822097920000000000000000 : Int) false,decode_split denominator ibox129 3 (1314882528609166451781191116229469204822097920000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_130 h,accepted_131 h⟩
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
private noncomputable def tree127 : TapeTree := .centered (candidateRows ibox127) (candidateRows (FixedTape.midBox ibox127))
attribute [irreducible] tree127
private theorem sign_127 : 2*denominator*(computed denominator (FixedTape.midBox ibox127)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox127).gradient k).lo.natAbs ((computed denominator ibox127).gradient k).hi.natAbs : Int)*((ibox127 k).hi-(ibox127 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox127
    (computed denominator ibox127) (computed denominator (FixedTape.midBox ibox127))
    (by decide +kernel)
private theorem midpoint_even_127 : ∀ k, 2 ∣ (ibox127 k).lo+(ibox127 k).hi := by decide +kernel
private theorem accepted_127 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox127) tree127 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox127 midpoint_even_127
  simp only [tree127,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox127,candidate_valid h (FixedTape.midBox ibox127),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox127 212 (FixedTape.rowsAux denominator ibox127 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox127) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_127
private noncomputable def tree126 : TapeTree := .split 3 (((1314882528609166451781191116229469204822097920000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree127 tree128
attribute [irreducible] tree126
private theorem accepted_126 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox126) tree126 = true := by
  simp only [tree126,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox126 3 (1314882528609166451781191116229469204822097920000000000000000 : Int) false,decode_split denominator ibox126 3 (1314882528609166451781191116229469204822097920000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_127 h,accepted_128 h⟩
private noncomputable def tree125 : TapeTree := .split 0 (((1377358126026746874809715040715088160647806976000000000000 : Int) : ℚ)/(denominator : ℚ)) tree126 tree129
attribute [irreducible] tree125
private theorem accepted_125 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox125) tree125 = true := by
  simp only [tree125,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox125 0 (1377358126026746874809715040715088160647806976000000000000 : Int) false,decode_split denominator ibox125 0 (1377358126026746874809715040715088160647806976000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_126 h,accepted_129 h⟩
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
private noncomputable def tree123 : TapeTree := .centered (candidateRows ibox123) (candidateRows (FixedTape.midBox ibox123))
attribute [irreducible] tree123
private theorem sign_123 : 2*denominator*(computed denominator (FixedTape.midBox ibox123)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox123).gradient k).lo.natAbs ((computed denominator ibox123).gradient k).hi.natAbs : Int)*((ibox123 k).hi-(ibox123 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox123
    (computed denominator ibox123) (computed denominator (FixedTape.midBox ibox123))
    (by decide +kernel)
private theorem midpoint_even_123 : ∀ k, 2 ∣ (ibox123 k).lo+(ibox123 k).hi := by decide +kernel
private theorem accepted_123 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox123) tree123 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox123 midpoint_even_123
  simp only [tree123,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox123,candidate_valid h (FixedTape.midBox ibox123),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox123 212 (FixedTape.rowsAux denominator ibox123 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox123) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_123
private noncomputable def tree122 : TapeTree := .split 3 (((1075812977952954369639156367824111167581716480000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree123 tree124
attribute [irreducible] tree122
private theorem accepted_122 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox122) tree122 = true := by
  simp only [tree122,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox122 3 (1075812977952954369639156367824111167581716480000000000000000 : Int) false,decode_split denominator ibox122 3 (1075812977952954369639156367824111167581716480000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_123 h,accepted_124 h⟩
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
private noncomputable def tree120 : TapeTree := .centered (candidateRows ibox120) (candidateRows (FixedTape.midBox ibox120))
attribute [irreducible] tree120
private theorem sign_120 : 2*denominator*(computed denominator (FixedTape.midBox ibox120)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox120).gradient k).lo.natAbs ((computed denominator ibox120).gradient k).hi.natAbs : Int)*((ibox120 k).hi-(ibox120 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox120
    (computed denominator ibox120) (computed denominator (FixedTape.midBox ibox120))
    (by decide +kernel)
private theorem midpoint_even_120 : ∀ k, 2 ∣ (ibox120 k).lo+(ibox120 k).hi := by decide +kernel
private theorem accepted_120 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox120) tree120 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox120 midpoint_even_120
  simp only [tree120,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox120,candidate_valid h (FixedTape.midBox ibox120),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox120 212 (FixedTape.rowsAux denominator ibox120 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox120) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_120
private noncomputable def tree119 : TapeTree := .split 3 (((1075812977952954369639156367824111167581716480000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree120 tree121
attribute [irreducible] tree119
private theorem accepted_119 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox119) tree119 = true := by
  simp only [tree119,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox119 3 (1075812977952954369639156367824111167581716480000000000000000 : Int) false,decode_split denominator ibox119 3 (1075812977952954369639156367824111167581716480000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_120 h,accepted_121 h⟩
private noncomputable def tree118 : TapeTree := .split 0 (((1377358126026746874809715040715088160647806976000000000000 : Int) : ℚ)/(denominator : ℚ)) tree119 tree122
attribute [irreducible] tree118
private theorem accepted_118 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox118) tree118 = true := by
  simp only [tree118,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox118 0 (1377358126026746874809715040715088160647806976000000000000 : Int) false,decode_split denominator ibox118 0 (1377358126026746874809715040715088160647806976000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_119 h,accepted_122 h⟩
private noncomputable def tree117 : TapeTree := .split 3 (((1195347753281060410710173742026790186201907200000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree118 tree125
attribute [irreducible] tree117
private theorem accepted_117 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox117) tree117 = true := by
  simp only [tree117,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox117 3 (1195347753281060410710173742026790186201907200000000000000000 : Int) false,decode_split denominator ibox117 3 (1195347753281060410710173742026790186201907200000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_118 h,accepted_125 h⟩
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
private noncomputable def tree115 : TapeTree := .centered (candidateRows ibox115) (candidateRows (FixedTape.midBox ibox115))
attribute [irreducible] tree115
private theorem sign_115 : 2*denominator*(computed denominator (FixedTape.midBox ibox115)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox115).gradient k).lo.natAbs ((computed denominator ibox115).gradient k).hi.natAbs : Int)*((ibox115 k).hi-(ibox115 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox115
    (computed denominator ibox115) (computed denominator (FixedTape.midBox ibox115))
    (by decide +kernel)
private theorem midpoint_even_115 : ∀ k, 2 ∣ (ibox115 k).lo+(ibox115 k).hi := by decide +kernel
private theorem accepted_115 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox115) tree115 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox115 midpoint_even_115
  simp only [tree115,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox115,candidate_valid h (FixedTape.midBox ibox115),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox115 212 (FixedTape.rowsAux denominator ibox115 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox115) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_115
private noncomputable def tree114 : TapeTree := .split 3 (((1314882528609166451781191116229469204822097920000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree115 tree116
attribute [irreducible] tree114
private theorem accepted_114 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox114) tree114 = true := by
  simp only [tree114,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox114 3 (1314882528609166451781191116229469204822097920000000000000000 : Int) false,decode_split denominator ibox114 3 (1314882528609166451781191116229469204822097920000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_115 h,accepted_116 h⟩
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
private noncomputable def tree111 : TapeTree := .split 3 (((1314882528609166451781191116229469204822097920000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree112 tree113
attribute [irreducible] tree111
private theorem accepted_111 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox111) tree111 = true := by
  simp only [tree111,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox111 3 (1314882528609166451781191116229469204822097920000000000000000 : Int) false,decode_split denominator ibox111 3 (1314882528609166451781191116229469204822097920000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_112 h,accepted_113 h⟩
private noncomputable def tree110 : TapeTree := .split 0 (((1313294957374340043423216666728339874106048512000000000000 : Int) : ℚ)/(denominator : ℚ)) tree111 tree114
attribute [irreducible] tree110
private theorem accepted_110 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox110) tree110 = true := by
  simp only [tree110,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox110 0 (1313294957374340043423216666728339874106048512000000000000 : Int) false,decode_split denominator ibox110 0 (1313294957374340043423216666728339874106048512000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_111 h,accepted_114 h⟩
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
private noncomputable def tree107 : TapeTree := .split 3 (((1075812977952954369639156367824111167581716480000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree108 tree109
attribute [irreducible] tree107
private theorem accepted_107 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox107) tree107 = true := by
  simp only [tree107,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox107 3 (1075812977952954369639156367824111167581716480000000000000000 : Int) false,decode_split denominator ibox107 3 (1075812977952954369639156367824111167581716480000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_108 h,accepted_109 h⟩
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
private noncomputable def tree105 : TapeTree := .centered (candidateRows ibox105) (candidateRows (FixedTape.midBox ibox105))
attribute [irreducible] tree105
private theorem sign_105 : 2*denominator*(computed denominator (FixedTape.midBox ibox105)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox105).gradient k).lo.natAbs ((computed denominator ibox105).gradient k).hi.natAbs : Int)*((ibox105 k).hi-(ibox105 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox105
    (computed denominator ibox105) (computed denominator (FixedTape.midBox ibox105))
    (by decide +kernel)
private theorem midpoint_even_105 : ∀ k, 2 ∣ (ibox105 k).lo+(ibox105 k).hi := by decide +kernel
private theorem accepted_105 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox105) tree105 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox105 midpoint_even_105
  simp only [tree105,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox105,candidate_valid h (FixedTape.midBox ibox105),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox105 212 (FixedTape.rowsAux denominator ibox105 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox105) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_105
private noncomputable def tree104 : TapeTree := .split 3 (((1075812977952954369639156367824111167581716480000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree105 tree106
attribute [irreducible] tree104
private theorem accepted_104 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox104) tree104 = true := by
  simp only [tree104,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox104 3 (1075812977952954369639156367824111167581716480000000000000000 : Int) false,decode_split denominator ibox104 3 (1075812977952954369639156367824111167581716480000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_105 h,accepted_106 h⟩
private noncomputable def tree103 : TapeTree := .split 0 (((1313294957374340043423216666728339874106048512000000000000 : Int) : ℚ)/(denominator : ℚ)) tree104 tree107
attribute [irreducible] tree103
private theorem accepted_103 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox103) tree103 = true := by
  simp only [tree103,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox103 0 (1313294957374340043423216666728339874106048512000000000000 : Int) false,decode_split denominator ibox103 0 (1313294957374340043423216666728339874106048512000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_104 h,accepted_107 h⟩
private noncomputable def tree102 : TapeTree := .split 3 (((1195347753281060410710173742026790186201907200000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree103 tree110
attribute [irreducible] tree102
private theorem accepted_102 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox102) tree102 = true := by
  simp only [tree102,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox102 3 (1195347753281060410710173742026790186201907200000000000000000 : Int) false,decode_split denominator ibox102 3 (1195347753281060410710173742026790186201907200000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_103 h,accepted_110 h⟩
private noncomputable def tree101 : TapeTree := .split 0 (((1345326541700543459116465853721714017376927744000000000000 : Int) : ℚ)/(denominator : ℚ)) tree102 tree117
attribute [irreducible] tree101
private theorem accepted_101 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox101) tree101 = true := by
  simp only [tree101,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox101 0 (1345326541700543459116465853721714017376927744000000000000 : Int) false,decode_split denominator ibox101 0 (1345326541700543459116465853721714017376927744000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_102 h,accepted_117 h⟩
private noncomputable def tree100 : TapeTree := .split 3 (((1434417303937272492852208490432148223442288640000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree101 tree132
attribute [irreducible] tree100
private theorem accepted_100 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox100) tree100 = true := by
  simp only [tree100,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox100 3 (1434417303937272492852208490432148223442288640000000000000000 : Int) false,decode_split denominator ibox100 3 (1434417303937272492852208490432148223442288640000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_101 h,accepted_132 h⟩
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
private noncomputable def tree98 : TapeTree := .centered (candidateRows ibox98) (candidateRows (FixedTape.midBox ibox98))
attribute [irreducible] tree98
private theorem sign_98 : 2*denominator*(computed denominator (FixedTape.midBox ibox98)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox98).gradient k).lo.natAbs ((computed denominator ibox98).gradient k).hi.natAbs : Int)*((ibox98 k).hi-(ibox98 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox98
    (computed denominator ibox98) (computed denominator (FixedTape.midBox ibox98))
    (by decide +kernel)
private theorem midpoint_even_98 : ∀ k, 2 ∣ (ibox98 k).lo+(ibox98 k).hi := by decide +kernel
private theorem accepted_98 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox98) tree98 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox98 midpoint_even_98
  simp only [tree98,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox98,candidate_valid h (FixedTape.midBox ibox98),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox98 212 (FixedTape.rowsAux denominator ibox98 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox98) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_98
private noncomputable def tree97 : TapeTree := .split 3 (((836743427296742287497121619418753130341335040000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree98 tree99
attribute [irreducible] tree97
private theorem accepted_97 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox97) tree97 = true := by
  simp only [tree97,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox97 3 (836743427296742287497121619418753130341335040000000000000000 : Int) false,decode_split denominator ibox97 3 (836743427296742287497121619418753130341335040000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_98 h,accepted_99 h⟩
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
private noncomputable def tree95 : TapeTree := .centered (candidateRows ibox95) (candidateRows (FixedTape.midBox ibox95))
attribute [irreducible] tree95
private theorem sign_95 : 2*denominator*(computed denominator (FixedTape.midBox ibox95)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox95).gradient k).lo.natAbs ((computed denominator ibox95).gradient k).hi.natAbs : Int)*((ibox95 k).hi-(ibox95 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox95
    (computed denominator ibox95) (computed denominator (FixedTape.midBox ibox95))
    (by decide +kernel)
private theorem midpoint_even_95 : ∀ k, 2 ∣ (ibox95 k).lo+(ibox95 k).hi := by decide +kernel
private theorem accepted_95 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox95) tree95 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox95 midpoint_even_95
  simp only [tree95,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox95,candidate_valid h (FixedTape.midBox ibox95),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox95 212 (FixedTape.rowsAux denominator ibox95 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox95) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_95
private noncomputable def tree94 : TapeTree := .split 3 (((836743427296742287497121619418753130341335040000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree95 tree96
attribute [irreducible] tree94
private theorem accepted_94 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox94) tree94 = true := by
  simp only [tree94,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox94 3 (836743427296742287497121619418753130341335040000000000000000 : Int) false,decode_split denominator ibox94 3 (836743427296742287497121619418753130341335040000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_95 h,accepted_96 h⟩
private noncomputable def tree93 : TapeTree := .split 0 (((1377358126026746874809715040715088160647806976000000000000 : Int) : ℚ)/(denominator : ℚ)) tree94 tree97
attribute [irreducible] tree93
private theorem accepted_93 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox93) tree93 = true := by
  simp only [tree93,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox93 0 (1377358126026746874809715040715088160647806976000000000000 : Int) false,decode_split denominator ibox93 0 (1377358126026746874809715040715088160647806976000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_94 h,accepted_97 h⟩
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
private noncomputable def tree91 : TapeTree := .centered (candidateRows ibox91) (candidateRows (FixedTape.midBox ibox91))
attribute [irreducible] tree91
private theorem sign_91 : 2*denominator*(computed denominator (FixedTape.midBox ibox91)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox91).gradient k).lo.natAbs ((computed denominator ibox91).gradient k).hi.natAbs : Int)*((ibox91 k).hi-(ibox91 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox91
    (computed denominator ibox91) (computed denominator (FixedTape.midBox ibox91))
    (by decide +kernel)
private theorem midpoint_even_91 : ∀ k, 2 ∣ (ibox91 k).lo+(ibox91 k).hi := by decide +kernel
private theorem accepted_91 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox91) tree91 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox91 midpoint_even_91
  simp only [tree91,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox91,candidate_valid h (FixedTape.midBox ibox91),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox91 212 (FixedTape.rowsAux denominator ibox91 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox91) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_91
private noncomputable def tree90 : TapeTree := .split 3 (((597673876640530205355086871013395093100953600000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree91 tree92
attribute [irreducible] tree90
private theorem accepted_90 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox90) tree90 = true := by
  simp only [tree90,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox90 3 (597673876640530205355086871013395093100953600000000000000000 : Int) false,decode_split denominator ibox90 3 (597673876640530205355086871013395093100953600000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_91 h,accepted_92 h⟩
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
private noncomputable def tree87 : TapeTree := .split 3 (((597673876640530205355086871013395093100953600000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree88 tree89
attribute [irreducible] tree87
private theorem accepted_87 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox87) tree87 = true := by
  simp only [tree87,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox87 3 (597673876640530205355086871013395093100953600000000000000000 : Int) false,decode_split denominator ibox87 3 (597673876640530205355086871013395093100953600000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_88 h,accepted_89 h⟩
private noncomputable def tree86 : TapeTree := .split 0 (((1377358126026746874809715040715088160647806976000000000000 : Int) : ℚ)/(denominator : ℚ)) tree87 tree90
attribute [irreducible] tree86
private theorem accepted_86 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox86) tree86 = true := by
  simp only [tree86,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox86 0 (1377358126026746874809715040715088160647806976000000000000 : Int) false,decode_split denominator ibox86 0 (1377358126026746874809715040715088160647806976000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_87 h,accepted_90 h⟩
private noncomputable def tree85 : TapeTree := .split 3 (((717208651968636246426104245216074111721144320000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree86 tree93
attribute [irreducible] tree85
private theorem accepted_85 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox85) tree85 = true := by
  simp only [tree85,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox85 3 (717208651968636246426104245216074111721144320000000000000000 : Int) false,decode_split denominator ibox85 3 (717208651968636246426104245216074111721144320000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_86 h,accepted_93 h⟩
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
private noncomputable def tree82 : TapeTree := .split 3 (((836743427296742287497121619418753130341335040000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree83 tree84
attribute [irreducible] tree82
private theorem accepted_82 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox82) tree82 = true := by
  simp only [tree82,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox82 3 (836743427296742287497121619418753130341335040000000000000000 : Int) false,decode_split denominator ibox82 3 (836743427296742287497121619418753130341335040000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_83 h,accepted_84 h⟩
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
private noncomputable def tree79 : TapeTree := .split 3 (((836743427296742287497121619418753130341335040000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree80 tree81
attribute [irreducible] tree79
private theorem accepted_79 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox79) tree79 = true := by
  simp only [tree79,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox79 3 (836743427296742287497121619418753130341335040000000000000000 : Int) false,decode_split denominator ibox79 3 (836743427296742287497121619418753130341335040000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_80 h,accepted_81 h⟩
private noncomputable def tree78 : TapeTree := .split 0 (((1313294957374340043423216666728339874106048512000000000000 : Int) : ℚ)/(denominator : ℚ)) tree79 tree82
attribute [irreducible] tree78
private theorem accepted_78 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox78) tree78 = true := by
  simp only [tree78,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox78 0 (1313294957374340043423216666728339874106048512000000000000 : Int) false,decode_split denominator ibox78 0 (1313294957374340043423216666728339874106048512000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_79 h,accepted_82 h⟩
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
private noncomputable def tree76 : TapeTree := .centered (candidateRows ibox76) (candidateRows (FixedTape.midBox ibox76))
attribute [irreducible] tree76
private theorem sign_76 : 2*denominator*(computed denominator (FixedTape.midBox ibox76)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox76).gradient k).lo.natAbs ((computed denominator ibox76).gradient k).hi.natAbs : Int)*((ibox76 k).hi-(ibox76 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox76
    (computed denominator ibox76) (computed denominator (FixedTape.midBox ibox76))
    (by decide +kernel)
private theorem midpoint_even_76 : ∀ k, 2 ∣ (ibox76 k).lo+(ibox76 k).hi := by decide +kernel
private theorem accepted_76 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox76) tree76 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox76 midpoint_even_76
  simp only [tree76,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox76,candidate_valid h (FixedTape.midBox ibox76),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox76 212 (FixedTape.rowsAux denominator ibox76 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox76) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_76
private noncomputable def tree75 : TapeTree := .split 3 (((597673876640530205355086871013395093100953600000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree76 tree77
attribute [irreducible] tree75
private theorem accepted_75 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox75) tree75 = true := by
  simp only [tree75,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox75 3 (597673876640530205355086871013395093100953600000000000000000 : Int) false,decode_split denominator ibox75 3 (597673876640530205355086871013395093100953600000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_76 h,accepted_77 h⟩
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
private noncomputable def tree73 : TapeTree := .centered (candidateRows ibox73) (candidateRows (FixedTape.midBox ibox73))
attribute [irreducible] tree73
private theorem sign_73 : 2*denominator*(computed denominator (FixedTape.midBox ibox73)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox73).gradient k).lo.natAbs ((computed denominator ibox73).gradient k).hi.natAbs : Int)*((ibox73 k).hi-(ibox73 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox73
    (computed denominator ibox73) (computed denominator (FixedTape.midBox ibox73))
    (by decide +kernel)
private theorem midpoint_even_73 : ∀ k, 2 ∣ (ibox73 k).lo+(ibox73 k).hi := by decide +kernel
private theorem accepted_73 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox73) tree73 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox73 midpoint_even_73
  simp only [tree73,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox73,candidate_valid h (FixedTape.midBox ibox73),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox73 212 (FixedTape.rowsAux denominator ibox73 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox73) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_73
private noncomputable def tree72 : TapeTree := .split 3 (((597673876640530205355086871013395093100953600000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree73 tree74
attribute [irreducible] tree72
private theorem accepted_72 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox72) tree72 = true := by
  simp only [tree72,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox72 3 (597673876640530205355086871013395093100953600000000000000000 : Int) false,decode_split denominator ibox72 3 (597673876640530205355086871013395093100953600000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_73 h,accepted_74 h⟩
private noncomputable def tree71 : TapeTree := .split 0 (((1313294957374340043423216666728339874106048512000000000000 : Int) : ℚ)/(denominator : ℚ)) tree72 tree75
attribute [irreducible] tree71
private theorem accepted_71 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox71) tree71 = true := by
  simp only [tree71,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox71 0 (1313294957374340043423216666728339874106048512000000000000 : Int) false,decode_split denominator ibox71 0 (1313294957374340043423216666728339874106048512000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_72 h,accepted_75 h⟩
private noncomputable def tree70 : TapeTree := .split 3 (((717208651968636246426104245216074111721144320000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree71 tree78
attribute [irreducible] tree70
private theorem accepted_70 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox70) tree70 = true := by
  simp only [tree70,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox70 3 (717208651968636246426104245216074111721144320000000000000000 : Int) false,decode_split denominator ibox70 3 (717208651968636246426104245216074111721144320000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_71 h,accepted_78 h⟩
private noncomputable def tree69 : TapeTree := .split 0 (((1345326541700543459116465853721714017376927744000000000000 : Int) : ℚ)/(denominator : ℚ)) tree70 tree85
attribute [irreducible] tree69
private theorem accepted_69 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox69) tree69 = true := by
  simp only [tree69,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox69 0 (1345326541700543459116465853721714017376927744000000000000 : Int) false,decode_split denominator ibox69 0 (1345326541700543459116465853721714017376927744000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_70 h,accepted_85 h⟩
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
private noncomputable def tree66 : TapeTree := .split 0 (((1393373918189848582656339634211775232283246592000000000000 : Int) : ℚ)/(denominator : ℚ)) tree67 tree68
attribute [irreducible] tree66
private theorem accepted_66 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox66) tree66 = true := by
  simp only [tree66,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox66 0 (1393373918189848582656339634211775232283246592000000000000 : Int) false,decode_split denominator ibox66 0 (1393373918189848582656339634211775232283246592000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_67 h,accepted_68 h⟩
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
private noncomputable def tree64 : TapeTree := .centered (candidateRows ibox64) (candidateRows (FixedTape.midBox ibox64))
attribute [irreducible] tree64
private theorem sign_64 : 2*denominator*(computed denominator (FixedTape.midBox ibox64)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox64).gradient k).lo.natAbs ((computed denominator ibox64).gradient k).hi.natAbs : Int)*((ibox64 k).hi-(ibox64 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox64
    (computed denominator ibox64) (computed denominator (FixedTape.midBox ibox64))
    (by decide +kernel)
private theorem midpoint_even_64 : ∀ k, 2 ∣ (ibox64 k).lo+(ibox64 k).hi := by decide +kernel
private theorem accepted_64 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox64) tree64 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox64 midpoint_even_64
  simp only [tree64,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox64,candidate_valid h (FixedTape.midBox ibox64),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox64 212 (FixedTape.rowsAux denominator ibox64 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox64) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_64
private noncomputable def tree63 : TapeTree := .split 0 (((1361342333863645166963090447218401089012367360000000000000 : Int) : ℚ)/(denominator : ℚ)) tree64 tree65
attribute [irreducible] tree63
private theorem accepted_63 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox63) tree63 = true := by
  simp only [tree63,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox63 0 (1361342333863645166963090447218401089012367360000000000000 : Int) false,decode_split denominator ibox63 0 (1361342333863645166963090447218401089012367360000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_64 h,accepted_65 h⟩
private noncomputable def tree62 : TapeTree := .split 0 (((1377358126026746874809715040715088160647806976000000000000 : Int) : ℚ)/(denominator : ℚ)) tree63 tree66
attribute [irreducible] tree62
private theorem accepted_62 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox62) tree62 = true := by
  simp only [tree62,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox62 0 (1377358126026746874809715040715088160647806976000000000000 : Int) false,decode_split denominator ibox62 0 (1377358126026746874809715040715088160647806976000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_63 h,accepted_66 h⟩
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
private noncomputable def tree60 : TapeTree := .centered (candidateRows ibox60) (candidateRows (FixedTape.midBox ibox60))
attribute [irreducible] tree60
private theorem sign_60 : 2*denominator*(computed denominator (FixedTape.midBox ibox60)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox60).gradient k).lo.natAbs ((computed denominator ibox60).gradient k).hi.natAbs : Int)*((ibox60 k).hi-(ibox60 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox60
    (computed denominator ibox60) (computed denominator (FixedTape.midBox ibox60))
    (by decide +kernel)
private theorem midpoint_even_60 : ∀ k, 2 ∣ (ibox60 k).lo+(ibox60 k).hi := by decide +kernel
private theorem accepted_60 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox60) tree60 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox60 midpoint_even_60
  simp only [tree60,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox60,candidate_valid h (FixedTape.midBox ibox60),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox60 212 (FixedTape.rowsAux denominator ibox60 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox60) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_60
private noncomputable def tree59 : TapeTree := .split 0 (((1393373918189848582656339634211775232283246592000000000000 : Int) : ℚ)/(denominator : ℚ)) tree60 tree61
attribute [irreducible] tree59
private theorem accepted_59 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox59) tree59 = true := by
  simp only [tree59,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox59 0 (1393373918189848582656339634211775232283246592000000000000 : Int) false,decode_split denominator ibox59 0 (1393373918189848582656339634211775232283246592000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_60 h,accepted_61 h⟩
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
private noncomputable def tree57 : TapeTree := .centered (candidateRows ibox57) (candidateRows (FixedTape.midBox ibox57))
attribute [irreducible] tree57
private theorem sign_57 : 2*denominator*(computed denominator (FixedTape.midBox ibox57)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox57).gradient k).lo.natAbs ((computed denominator ibox57).gradient k).hi.natAbs : Int)*((ibox57 k).hi-(ibox57 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox57
    (computed denominator ibox57) (computed denominator (FixedTape.midBox ibox57))
    (by decide +kernel)
private theorem midpoint_even_57 : ∀ k, 2 ∣ (ibox57 k).lo+(ibox57 k).hi := by decide +kernel
private theorem accepted_57 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox57) tree57 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox57 midpoint_even_57
  simp only [tree57,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox57,candidate_valid h (FixedTape.midBox ibox57),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox57 212 (FixedTape.rowsAux denominator ibox57 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox57) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_57
private noncomputable def tree56 : TapeTree := .split 0 (((1361342333863645166963090447218401089012367360000000000000 : Int) : ℚ)/(denominator : ℚ)) tree57 tree58
attribute [irreducible] tree56
private theorem accepted_56 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox56) tree56 = true := by
  simp only [tree56,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox56 0 (1361342333863645166963090447218401089012367360000000000000 : Int) false,decode_split denominator ibox56 0 (1361342333863645166963090447218401089012367360000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_57 h,accepted_58 h⟩
private noncomputable def tree55 : TapeTree := .split 0 (((1377358126026746874809715040715088160647806976000000000000 : Int) : ℚ)/(denominator : ℚ)) tree56 tree59
attribute [irreducible] tree55
private theorem accepted_55 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox55) tree55 = true := by
  simp only [tree55,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox55 0 (1377358126026746874809715040715088160647806976000000000000 : Int) false,decode_split denominator ibox55 0 (1377358126026746874809715040715088160647806976000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_56 h,accepted_59 h⟩
private noncomputable def tree54 : TapeTree := .split 3 (((239069550656212082142034748405358037240381440000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree55 tree62
attribute [irreducible] tree54
private theorem accepted_54 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox54) tree54 = true := by
  simp only [tree54,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox54 3 (239069550656212082142034748405358037240381440000000000000000 : Int) false,decode_split denominator ibox54 3 (239069550656212082142034748405358037240381440000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_55 h,accepted_62 h⟩
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
private noncomputable def tree51 : TapeTree := .split 0 (((1329310749537441751269841260225026945741488128000000000000 : Int) : ℚ)/(denominator : ℚ)) tree52 tree53
attribute [irreducible] tree51
private theorem accepted_51 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox51) tree51 = true := by
  simp only [tree51,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox51 0 (1329310749537441751269841260225026945741488128000000000000 : Int) false,decode_split denominator ibox51 0 (1329310749537441751269841260225026945741488128000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_52 h,accepted_53 h⟩
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
private noncomputable def tree48 : TapeTree := .split 0 (((1329310749537441751269841260225026945741488128000000000000 : Int) : ℚ)/(denominator : ℚ)) tree49 tree50
attribute [irreducible] tree48
private theorem accepted_48 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox48) tree48 = true := by
  simp only [tree48,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox48 0 (1329310749537441751269841260225026945741488128000000000000 : Int) false,decode_split denominator ibox48 0 (1329310749537441751269841260225026945741488128000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_49 h,accepted_50 h⟩
private noncomputable def tree47 : TapeTree := .split 3 (((239069550656212082142034748405358037240381440000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree48 tree51
attribute [irreducible] tree47
private theorem accepted_47 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox47) tree47 = true := by
  simp only [tree47,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox47 3 (239069550656212082142034748405358037240381440000000000000000 : Int) false,decode_split denominator ibox47 3 (239069550656212082142034748405358037240381440000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_48 h,accepted_51 h⟩
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
private noncomputable def tree45 : TapeTree := .centered (candidateRows ibox45) (candidateRows (FixedTape.midBox ibox45))
attribute [irreducible] tree45
private theorem sign_45 : 2*denominator*(computed denominator (FixedTape.midBox ibox45)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox45).gradient k).lo.natAbs ((computed denominator ibox45).gradient k).hi.natAbs : Int)*((ibox45 k).hi-(ibox45 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox45
    (computed denominator ibox45) (computed denominator (FixedTape.midBox ibox45))
    (by decide +kernel)
private theorem midpoint_even_45 : ∀ k, 2 ∣ (ibox45 k).lo+(ibox45 k).hi := by decide +kernel
private theorem accepted_45 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox45) tree45 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox45 midpoint_even_45
  simp only [tree45,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox45,candidate_valid h (FixedTape.midBox ibox45),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox45 212 (FixedTape.rowsAux denominator ibox45 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox45) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_45
private noncomputable def tree44 : TapeTree := .split 0 (((1297279165211238335576592073231652802470608896000000000000 : Int) : ℚ)/(denominator : ℚ)) tree45 tree46
attribute [irreducible] tree44
private theorem accepted_44 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox44) tree44 = true := by
  simp only [tree44,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox44 0 (1297279165211238335576592073231652802470608896000000000000 : Int) false,decode_split denominator ibox44 0 (1297279165211238335576592073231652802470608896000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_45 h,accepted_46 h⟩
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
private noncomputable def tree41 : TapeTree := .split 0 (((1297279165211238335576592073231652802470608896000000000000 : Int) : ℚ)/(denominator : ℚ)) tree42 tree43
attribute [irreducible] tree41
private theorem accepted_41 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox41) tree41 = true := by
  simp only [tree41,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox41 0 (1297279165211238335576592073231652802470608896000000000000 : Int) false,decode_split denominator ibox41 0 (1297279165211238335576592073231652802470608896000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_42 h,accepted_43 h⟩
private noncomputable def tree40 : TapeTree := .split 3 (((239069550656212082142034748405358037240381440000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree41 tree44
attribute [irreducible] tree40
private theorem accepted_40 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox40) tree40 = true := by
  simp only [tree40,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox40 3 (239069550656212082142034748405358037240381440000000000000000 : Int) false,decode_split denominator ibox40 3 (239069550656212082142034748405358037240381440000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_41 h,accepted_44 h⟩
private noncomputable def tree39 : TapeTree := .split 0 (((1313294957374340043423216666728339874106048512000000000000 : Int) : ℚ)/(denominator : ℚ)) tree40 tree47
attribute [irreducible] tree39
private theorem accepted_39 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox39) tree39 = true := by
  simp only [tree39,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox39 0 (1313294957374340043423216666728339874106048512000000000000 : Int) false,decode_split denominator ibox39 0 (1313294957374340043423216666728339874106048512000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_40 h,accepted_47 h⟩
private noncomputable def tree38 : TapeTree := .split 0 (((1345326541700543459116465853721714017376927744000000000000 : Int) : ℚ)/(denominator : ℚ)) tree39 tree54
attribute [irreducible] tree38
private theorem accepted_38 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox38) tree38 = true := by
  simp only [tree38,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox38 0 (1345326541700543459116465853721714017376927744000000000000 : Int) false,decode_split denominator ibox38 0 (1345326541700543459116465853721714017376927744000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_39 h,accepted_54 h⟩
private noncomputable def tree37 : TapeTree := .split 3 (((478139101312424164284069496810716074480762880000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree38 tree69
attribute [irreducible] tree37
private theorem accepted_37 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox37) tree37 = true := by
  simp only [tree37,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox37 3 (478139101312424164284069496810716074480762880000000000000000 : Int) false,decode_split denominator ibox37 3 (478139101312424164284069496810716074480762880000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_38 h,accepted_69 h⟩
private noncomputable def tree36 : TapeTree := .split 3 (((956278202624848328568138993621432148961525760000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree37 tree100
attribute [irreducible] tree36
private theorem accepted_36 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox36) tree36 = true := by
  simp only [tree36,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox36 3 (956278202624848328568138993621432148961525760000000000000000 : Int) false,decode_split denominator ibox36 3 (956278202624848328568138993621432148961525760000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_37 h,accepted_100 h⟩
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
private noncomputable def tree34 : TapeTree := .split 0 (((1409389710352950290502964227708462303918686208000000000000 : Int) : ℚ)/(denominator : ℚ)) tree35 tree163
attribute [irreducible] tree34
private theorem accepted_34 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox34) tree34 = true := by
  simp only [tree34,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox34 0 (1409389710352950290502964227708462303918686208000000000000 : Int) false,decode_split denominator ibox34 0 (1409389710352950290502964227708462303918686208000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_35 h,accepted_163 h⟩
private noncomputable def tree33 : TapeTree := .split 1 (((239069550656212082142034748405358037240381440000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree34 tree291
attribute [irreducible] tree33
private theorem accepted_33 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox33) tree33 = true := by
  simp only [tree33,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox33 1 (239069550656212082142034748405358037240381440000000000000000 : Int) false,decode_split denominator ibox33 1 (239069550656212082142034748405358037240381440000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_34 h,accepted_291 h⟩
private noncomputable def tree32 : TapeTree := .split 1 (((478139101312424164284069496810716074480762880000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree33 tree300
attribute [irreducible] tree32
private theorem accepted_32 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox32) tree32 = true := by
  simp only [tree32,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox32 1 (478139101312424164284069496810716074480762880000000000000000 : Int) false,decode_split denominator ibox32 1 (478139101312424164284069496810716074480762880000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_33 h,accepted_300 h⟩
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
private noncomputable def tree30 : TapeTree := .split 1 (((956278202624848328568138993621432148961525760000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree31 tree305
attribute [irreducible] tree30
private theorem accepted_30 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox30) tree30 = true := by
  simp only [tree30,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox30 1 (956278202624848328568138993621432148961525760000000000000000 : Int) false,decode_split denominator ibox30 1 (956278202624848328568138993621432148961525760000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_31 h,accepted_305 h⟩
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
private noncomputable def tree27 : TapeTree := .split 1 (((956278202624848328568138993621432148961525760000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree28 tree29
attribute [irreducible] tree27
private theorem accepted_27 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox27) tree27 = true := by
  simp only [tree27,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox27 1 (956278202624848328568138993621432148961525760000000000000000 : Int) false,decode_split denominator ibox27 1 (956278202624848328568138993621432148961525760000000000000000 : Int) true]
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
private noncomputable def tree23 : TapeTree := .split 1 (((956278202624848328568138993621432148961525760000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree24 tree25
attribute [irreducible] tree23
private theorem accepted_23 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox23) tree23 = true := by
  simp only [tree23,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox23 1 (956278202624848328568138993621432148961525760000000000000000 : Int) false,decode_split denominator ibox23 1 (956278202624848328568138993621432148961525760000000000000000 : Int) true]
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
private noncomputable def tree21 : TapeTree := .split 0 (((1409389710352950290502964227708462303918686208000000000000 : Int) : ℚ)/(denominator : ℚ)) tree22 tree26
attribute [irreducible] tree21
private theorem accepted_21 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox21) tree21 = true := by
  simp only [tree21,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox21 0 (1409389710352950290502964227708462303918686208000000000000 : Int) false,decode_split denominator ibox21 0 (1409389710352950290502964227708462303918686208000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_22 h,accepted_26 h⟩
private noncomputable def tree20 : TapeTree := .split 2 (((1434417303937272492852208490432148223442288640000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree21 tree30
attribute [irreducible] tree20
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox20 2 (1434417303937272492852208490432148223442288640000000000000000 : Int) false,decode_split denominator ibox20 2 (1434417303937272492852208490432148223442288640000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_21 h,accepted_30 h⟩
private noncomputable def tree19 : TapeTree := .split 0 (((1537516047657763953275960975681958877002203136000000000000 : Int) : ℚ)/(denominator : ℚ)) tree20 tree313
attribute [irreducible] tree19
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox19 0 (1537516047657763953275960975681958877002203136000000000000 : Int) false,decode_split denominator ibox19 0 (1537516047657763953275960975681958877002203136000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_20 h,accepted_313 h⟩
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
private noncomputable def tree16 : TapeTree := .split 0 (((1665642384962577616048957723655455450085720064000000000000 : Int) : ℚ)/(denominator : ℚ)) tree17 tree18
attribute [irreducible] tree16
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox16 0 (1665642384962577616048957723655455450085720064000000000000 : Int) false,decode_split denominator ibox16 0 (1665642384962577616048957723655455450085720064000000000000 : Int) true]
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
private noncomputable def tree14 : TapeTree := .split 1 (((1434417303937272492852208490432148223442288640000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree15 tree16
attribute [irreducible] tree14
private theorem accepted_14 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox14) tree14 = true := by
  simp only [tree14,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox14 1 (1434417303937272492852208490432148223442288640000000000000000 : Int) false,decode_split denominator ibox14 1 (1434417303937272492852208490432148223442288640000000000000000 : Int) true]
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
private noncomputable def tree11 : TapeTree := .split 1 (((956278202624848328568138993621432148961525760000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree12 tree14
attribute [irreducible] tree11
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox11 1 (956278202624848328568138993621432148961525760000000000000000 : Int) false,decode_split denominator ibox11 1 (956278202624848328568138993621432148961525760000000000000000 : Int) true]
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
private noncomputable def tree6 : TapeTree := .split 0 (((1409389710352950290502964227708462303918686208000000000000 : Int) : ℚ)/(denominator : ℚ)) tree7 tree9
attribute [irreducible] tree6
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox6 0 (1409389710352950290502964227708462303918686208000000000000 : Int) false,decode_split denominator ibox6 0 (1409389710352950290502964227708462303918686208000000000000 : Int) true]
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
private noncomputable def tree3 : TapeTree := .split 1 (((956278202624848328568138993621432148961525760000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree6
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 1 (956278202624848328568138993621432148961525760000000000000000 : Int) false,decode_split denominator ibox3 1 (956278202624848328568138993621432148961525760000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_6 h⟩
private noncomputable def tree2 : TapeTree := .split 0 (((1537516047657763953275960975681958877002203136000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree11
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 0 (1537516047657763953275960975681958877002203136000000000000 : Int) false,decode_split denominator ibox2 0 (1537516047657763953275960975681958877002203136000000000000 : Int) true]
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
private noncomputable def tree0 : TapeTree := .split 2 (((956278202624848328568138993621432148961525760000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree1 tree19
attribute [irreducible] tree0
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox0 2 (956278202624848328568138993621432148961525760000000000000000 : Int) false,decode_split denominator ibox0 2 (956278202624848328568138993621432148961525760000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_1 h,accepted_19 h⟩
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (343/512000 : ℚ) (2401/2560000 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 212 = e219 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (343/512000 : ℚ) (2401/2560000 : ℚ)) x → eval e219 x ≤ 0 := by
  have hb := h.child_4 tape 212 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell4_low_internal

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell4_low_internal
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((343/512000 : ℚ) : ℝ) < p ∧ p ≤ ((2401/2560000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 4 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 4 p)
    (hk0 : ((2401/2560000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((343/512000 : ℚ) : ℝ))
    (hk1 : ((2401/2560000 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((343/512000 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r), internalResidual (0 : Fin 9) a p A r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell4_low_internal.cell_bound h.child_8 h.child_9 (Cell4_low_internal.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell4_low_internal
