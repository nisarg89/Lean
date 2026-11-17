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
namespace Cell5_low_internal
private noncomputable def qValues : Fin 2 → ℚ := ![(5871974415391/819200000000000000 : ℚ),(464593469861/80000000000 : ℚ)]
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
    priceLambda 5 p = ((5871974415391/819200000000000000 : ℝ)+(464593469861/80000000000 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell5,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 5 p = (((145513/100000 : ℝ)+(145513/25000 : ℝ)*p)-(145513/100000 : ℝ)*(1/1 : ℝ))/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell5,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e219 x = (x 0*(1-x 0))*(aPoint x+priceLambda 5 (x 0)*(HStar (yPoint x)-HStar (aPoint x)-HStar (capPoint x))+priceTau 5 (x 0)*psiStar (rPoint x)+(0)-(0)) := by
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
    (hL : lambdaStar (x 0) = priceLambda 5 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 5 (x 0)) :
    (1)*eval e219 x = (x 0*(1-x 0))*(internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,if_pos hA,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (2401/2560000 : ℚ) (16807/12800000 : ℚ)) x → eval e219 x ≤ 0)
    (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((2401/2560000 : ℚ) : ℝ) < p ∧ p ≤ ((16807/12800000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 5 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 5 p)
    (hk0 : ((16807/12800000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((2401/2560000 : ℚ) : ℝ))
    (hk1 : ((16807/12800000 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((2401/2560000 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r) :
    internalResidual (0 : Fin 9) a p A r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxA,hxr⟩ := h3 (2401/2560000 : ℚ) (16807/12800000 : ℚ) ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ) p a A r hpcell hk0 hk1 hr ha hap hpA hAr
  have hcut : ((16807/12800000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) := by norm_num [bStar]
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxa
  have hAx : capPoint x = A := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxA
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 5 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 5 (x 0) := by simpa only [hxp] using hT
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
.const (5871974415391/819200000000000000 : ℚ),
.const (464593469861/80000000000 : ℚ),
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
private noncomputable def ssaQVals : Fin 16 → ℚ := ![(1/1 : ℚ),(49/100 : ℚ),(390189/5000000 : ℚ),(1085/4818 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(4818/3733 : ℚ),(5871974415391/819200000000000000 : ℚ),(464593469861/80000000000 : ℚ),(145513/100000 : ℚ),(145513/25000 : ℚ),(-145513/100000 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ)]
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
private noncomputable def denominator : Int := 239069550656212082142034748405358037240381440000000000000000000
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
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨224221090283423909852744308953619002896154624000000000000000,313909526396793473793842032535066604054616473600000000000000⟩,⟨0,239069550656212082142034748405358037240381440000000000000000000⟩,⟨0,239069550656212082142034748405358037240381440000000000000000000⟩,⟨0,239069550656212082142034748405358037240381440000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := splitI ibox0 2 119534775328106041071017374202679018620190720000000000000000000 false
private noncomputable def ibox2 : Fin 4 → FixedTape.I := faceI ibox1 3 false
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 0 269065308340108691823293170744342803475385548800000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 1 119534775328106041071017374202679018620190720000000000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := faceI ibox4 2 true
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox3 1 119534775328106041071017374202679018620190720000000000000000000 true
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox6 0 246643199311766300838018739848980903185770086400000000000000 false
private noncomputable def ibox8 : Fin 4 → FixedTape.I := faceI ibox7 1 true
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox6 0 246643199311766300838018739848980903185770086400000000000000 true
private noncomputable def ibox10 : Fin 4 → FixedTape.I := faceI ibox9 1 true
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox2 0 269065308340108691823293170744342803475385548800000000000000 true
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox11 1 119534775328106041071017374202679018620190720000000000000000000 false
private noncomputable def ibox13 : Fin 4 → FixedTape.I := faceI ibox12 2 true
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox11 1 119534775328106041071017374202679018620190720000000000000000000 true
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox14 1 179302162992159061606526061304018527930286080000000000000000000 false
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox14 1 179302162992159061606526061304018527930286080000000000000000000 true
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox16 0 291487417368451082808567601639704703765001011200000000000000 false
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox16 0 291487417368451082808567601639704703765001011200000000000000 true
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox0 2 119534775328106041071017374202679018620190720000000000000000000 true
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox19 0 269065308340108691823293170744342803475385548800000000000000 false
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox20 2 179302162992159061606526061304018527930286080000000000000000000 false
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox21 0 246643199311766300838018739848980903185770086400000000000000 false
private noncomputable def ibox23 : Fin 4 → FixedTape.I := faceI ibox22 3 false
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox23 1 119534775328106041071017374202679018620190720000000000000000000 false
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox23 1 119534775328106041071017374202679018620190720000000000000000000 true
private noncomputable def ibox26 : Fin 4 → FixedTape.I := splitI ibox21 0 246643199311766300838018739848980903185770086400000000000000 true
private noncomputable def ibox27 : Fin 4 → FixedTape.I := faceI ibox26 3 false
private noncomputable def ibox28 : Fin 4 → FixedTape.I := splitI ibox27 1 119534775328106041071017374202679018620190720000000000000000000 false
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox27 1 119534775328106041071017374202679018620190720000000000000000000 true
private noncomputable def ibox30 : Fin 4 → FixedTape.I := splitI ibox20 2 179302162992159061606526061304018527930286080000000000000000000 true
private noncomputable def ibox31 : Fin 4 → FixedTape.I := splitI ibox30 1 119534775328106041071017374202679018620190720000000000000000000 false
private noncomputable def ibox32 : Fin 4 → FixedTape.I := faceI ibox31 2 true
private noncomputable def ibox33 : Fin 4 → FixedTape.I := splitI ibox32 1 59767387664053020535508687101339509310095360000000000000000000 false
private noncomputable def ibox34 : Fin 4 → FixedTape.I := splitI ibox33 1 29883693832026510267754343550669754655047680000000000000000000 false
private noncomputable def ibox35 : Fin 4 → FixedTape.I := splitI ibox34 0 246643199311766300838018739848980903185770086400000000000000 false
private noncomputable def ibox36 : Fin 4 → FixedTape.I := faceI ibox35 1 false
private noncomputable def ibox37 : Fin 4 → FixedTape.I := splitI ibox36 3 119534775328106041071017374202679018620190720000000000000000000 false
private noncomputable def ibox38 : Fin 4 → FixedTape.I := splitI ibox37 3 59767387664053020535508687101339509310095360000000000000000000 false
private noncomputable def ibox39 : Fin 4 → FixedTape.I := splitI ibox38 0 235432144797595105345381524401299953040962355200000000000000 false
private noncomputable def ibox40 : Fin 4 → FixedTape.I := splitI ibox39 0 229826617540509507599062916677459477968558489600000000000000 false
private noncomputable def ibox41 : Fin 4 → FixedTape.I := splitI ibox40 3 29883693832026510267754343550669754655047680000000000000000000 false
private noncomputable def ibox42 : Fin 4 → FixedTape.I := splitI ibox41 0 227023853911966708725903612815539240432356556800000000000000 false
private noncomputable def ibox43 : Fin 4 → FixedTape.I := splitI ibox41 0 227023853911966708725903612815539240432356556800000000000000 true
private noncomputable def ibox44 : Fin 4 → FixedTape.I := splitI ibox40 3 29883693832026510267754343550669754655047680000000000000000000 true
private noncomputable def ibox45 : Fin 4 → FixedTape.I := splitI ibox44 0 227023853911966708725903612815539240432356556800000000000000 false
private noncomputable def ibox46 : Fin 4 → FixedTape.I := splitI ibox44 0 227023853911966708725903612815539240432356556800000000000000 true
private noncomputable def ibox47 : Fin 4 → FixedTape.I := splitI ibox39 0 229826617540509507599062916677459477968558489600000000000000 true
private noncomputable def ibox48 : Fin 4 → FixedTape.I := splitI ibox47 3 29883693832026510267754343550669754655047680000000000000000000 false
private noncomputable def ibox49 : Fin 4 → FixedTape.I := splitI ibox48 0 232629381169052306472222220539379715504760422400000000000000 false
private noncomputable def ibox50 : Fin 4 → FixedTape.I := splitI ibox48 0 232629381169052306472222220539379715504760422400000000000000 true
private noncomputable def ibox51 : Fin 4 → FixedTape.I := splitI ibox47 3 29883693832026510267754343550669754655047680000000000000000000 true
private noncomputable def ibox52 : Fin 4 → FixedTape.I := splitI ibox51 0 232629381169052306472222220539379715504760422400000000000000 false
private noncomputable def ibox53 : Fin 4 → FixedTape.I := splitI ibox51 0 232629381169052306472222220539379715504760422400000000000000 true
private noncomputable def ibox54 : Fin 4 → FixedTape.I := splitI ibox38 0 235432144797595105345381524401299953040962355200000000000000 true
private noncomputable def ibox55 : Fin 4 → FixedTape.I := splitI ibox54 0 241037672054680703091700132125140428113366220800000000000000 false
private noncomputable def ibox56 : Fin 4 → FixedTape.I := splitI ibox55 3 29883693832026510267754343550669754655047680000000000000000000 false
private noncomputable def ibox57 : Fin 4 → FixedTape.I := splitI ibox56 0 238234908426137904218540828263220190577164288000000000000000 false
private noncomputable def ibox58 : Fin 4 → FixedTape.I := splitI ibox56 0 238234908426137904218540828263220190577164288000000000000000 true
private noncomputable def ibox59 : Fin 4 → FixedTape.I := splitI ibox55 3 29883693832026510267754343550669754655047680000000000000000000 true
private noncomputable def ibox60 : Fin 4 → FixedTape.I := splitI ibox59 0 238234908426137904218540828263220190577164288000000000000000 false
private noncomputable def ibox61 : Fin 4 → FixedTape.I := splitI ibox59 0 238234908426137904218540828263220190577164288000000000000000 true
private noncomputable def ibox62 : Fin 4 → FixedTape.I := splitI ibox54 0 241037672054680703091700132125140428113366220800000000000000 true
private noncomputable def ibox63 : Fin 4 → FixedTape.I := splitI ibox62 3 29883693832026510267754343550669754655047680000000000000000000 false
private noncomputable def ibox64 : Fin 4 → FixedTape.I := splitI ibox63 0 243840435683223501964859435987060665649568153600000000000000 false
private noncomputable def ibox65 : Fin 4 → FixedTape.I := splitI ibox63 0 243840435683223501964859435987060665649568153600000000000000 true
private noncomputable def ibox66 : Fin 4 → FixedTape.I := splitI ibox62 3 29883693832026510267754343550669754655047680000000000000000000 true
private noncomputable def ibox67 : Fin 4 → FixedTape.I := splitI ibox66 0 243840435683223501964859435987060665649568153600000000000000 false
private noncomputable def ibox68 : Fin 4 → FixedTape.I := splitI ibox66 0 243840435683223501964859435987060665649568153600000000000000 true
private noncomputable def ibox69 : Fin 4 → FixedTape.I := splitI ibox37 3 59767387664053020535508687101339509310095360000000000000000000 true
private noncomputable def ibox70 : Fin 4 → FixedTape.I := splitI ibox69 0 235432144797595105345381524401299953040962355200000000000000 false
private noncomputable def ibox71 : Fin 4 → FixedTape.I := splitI ibox70 3 89651081496079530803263030652009263965143040000000000000000000 false
private noncomputable def ibox72 : Fin 4 → FixedTape.I := splitI ibox71 0 229826617540509507599062916677459477968558489600000000000000 false
private noncomputable def ibox73 : Fin 4 → FixedTape.I := splitI ibox72 0 227023853911966708725903612815539240432356556800000000000000 false
private noncomputable def ibox74 : Fin 4 → FixedTape.I := splitI ibox72 0 227023853911966708725903612815539240432356556800000000000000 true
private noncomputable def ibox75 : Fin 4 → FixedTape.I := splitI ibox71 0 229826617540509507599062916677459477968558489600000000000000 true
private noncomputable def ibox76 : Fin 4 → FixedTape.I := splitI ibox75 0 232629381169052306472222220539379715504760422400000000000000 false
private noncomputable def ibox77 : Fin 4 → FixedTape.I := splitI ibox75 0 232629381169052306472222220539379715504760422400000000000000 true
private noncomputable def ibox78 : Fin 4 → FixedTape.I := splitI ibox70 3 89651081496079530803263030652009263965143040000000000000000000 true
private noncomputable def ibox79 : Fin 4 → FixedTape.I := splitI ibox78 0 229826617540509507599062916677459477968558489600000000000000 false
private noncomputable def ibox80 : Fin 4 → FixedTape.I := splitI ibox79 3 104592928412092785937140202427344141292666880000000000000000000 false
private noncomputable def ibox81 : Fin 4 → FixedTape.I := splitI ibox79 3 104592928412092785937140202427344141292666880000000000000000000 true
private noncomputable def ibox82 : Fin 4 → FixedTape.I := splitI ibox78 0 229826617540509507599062916677459477968558489600000000000000 true
private noncomputable def ibox83 : Fin 4 → FixedTape.I := splitI ibox82 3 104592928412092785937140202427344141292666880000000000000000000 false
private noncomputable def ibox84 : Fin 4 → FixedTape.I := splitI ibox82 3 104592928412092785937140202427344141292666880000000000000000000 true
private noncomputable def ibox85 : Fin 4 → FixedTape.I := splitI ibox69 0 235432144797595105345381524401299953040962355200000000000000 true
private noncomputable def ibox86 : Fin 4 → FixedTape.I := splitI ibox85 3 89651081496079530803263030652009263965143040000000000000000000 false
private noncomputable def ibox87 : Fin 4 → FixedTape.I := splitI ibox86 0 241037672054680703091700132125140428113366220800000000000000 false
private noncomputable def ibox88 : Fin 4 → FixedTape.I := splitI ibox87 0 238234908426137904218540828263220190577164288000000000000000 false
private noncomputable def ibox89 : Fin 4 → FixedTape.I := splitI ibox87 0 238234908426137904218540828263220190577164288000000000000000 true
private noncomputable def ibox90 : Fin 4 → FixedTape.I := splitI ibox86 0 241037672054680703091700132125140428113366220800000000000000 true
private noncomputable def ibox91 : Fin 4 → FixedTape.I := splitI ibox90 3 74709234580066275669385858876674386637619200000000000000000000 false
private noncomputable def ibox92 : Fin 4 → FixedTape.I := splitI ibox90 3 74709234580066275669385858876674386637619200000000000000000000 true
private noncomputable def ibox93 : Fin 4 → FixedTape.I := splitI ibox85 3 89651081496079530803263030652009263965143040000000000000000000 true
private noncomputable def ibox94 : Fin 4 → FixedTape.I := splitI ibox93 0 241037672054680703091700132125140428113366220800000000000000 false
private noncomputable def ibox95 : Fin 4 → FixedTape.I := splitI ibox94 3 104592928412092785937140202427344141292666880000000000000000000 false
private noncomputable def ibox96 : Fin 4 → FixedTape.I := splitI ibox94 3 104592928412092785937140202427344141292666880000000000000000000 true
private noncomputable def ibox97 : Fin 4 → FixedTape.I := splitI ibox93 0 241037672054680703091700132125140428113366220800000000000000 true
private noncomputable def ibox98 : Fin 4 → FixedTape.I := splitI ibox97 3 104592928412092785937140202427344141292666880000000000000000000 false
private noncomputable def ibox99 : Fin 4 → FixedTape.I := splitI ibox97 3 104592928412092785937140202427344141292666880000000000000000000 true
private noncomputable def ibox100 : Fin 4 → FixedTape.I := splitI ibox36 3 119534775328106041071017374202679018620190720000000000000000000 true
private noncomputable def ibox101 : Fin 4 → FixedTape.I := splitI ibox100 3 179302162992159061606526061304018527930286080000000000000000000 false
private noncomputable def ibox102 : Fin 4 → FixedTape.I := splitI ibox101 0 235432144797595105345381524401299953040962355200000000000000 false
private noncomputable def ibox103 : Fin 4 → FixedTape.I := splitI ibox102 3 149418469160132551338771717753348773275238400000000000000000000 false
private noncomputable def ibox104 : Fin 4 → FixedTape.I := splitI ibox103 0 229826617540509507599062916677459477968558489600000000000000 false
private noncomputable def ibox105 : Fin 4 → FixedTape.I := splitI ibox104 3 134476622244119296204894545978013895947714560000000000000000000 false
private noncomputable def ibox106 : Fin 4 → FixedTape.I := splitI ibox104 3 134476622244119296204894545978013895947714560000000000000000000 true
private noncomputable def ibox107 : Fin 4 → FixedTape.I := splitI ibox103 0 229826617540509507599062916677459477968558489600000000000000 true
private noncomputable def ibox108 : Fin 4 → FixedTape.I := splitI ibox107 3 134476622244119296204894545978013895947714560000000000000000000 false
private noncomputable def ibox109 : Fin 4 → FixedTape.I := splitI ibox107 3 134476622244119296204894545978013895947714560000000000000000000 true
private noncomputable def ibox110 : Fin 4 → FixedTape.I := splitI ibox102 3 149418469160132551338771717753348773275238400000000000000000000 true
private noncomputable def ibox111 : Fin 4 → FixedTape.I := splitI ibox110 0 229826617540509507599062916677459477968558489600000000000000 false
private noncomputable def ibox112 : Fin 4 → FixedTape.I := splitI ibox111 3 164360316076145806472648889528683650602762240000000000000000000 false
private noncomputable def ibox113 : Fin 4 → FixedTape.I := splitI ibox111 3 164360316076145806472648889528683650602762240000000000000000000 true
private noncomputable def ibox114 : Fin 4 → FixedTape.I := splitI ibox110 0 229826617540509507599062916677459477968558489600000000000000 true
private noncomputable def ibox115 : Fin 4 → FixedTape.I := splitI ibox114 3 164360316076145806472648889528683650602762240000000000000000000 false
private noncomputable def ibox116 : Fin 4 → FixedTape.I := splitI ibox114 3 164360316076145806472648889528683650602762240000000000000000000 true
private noncomputable def ibox117 : Fin 4 → FixedTape.I := splitI ibox101 0 235432144797595105345381524401299953040962355200000000000000 true
private noncomputable def ibox118 : Fin 4 → FixedTape.I := splitI ibox117 3 149418469160132551338771717753348773275238400000000000000000000 false
private noncomputable def ibox119 : Fin 4 → FixedTape.I := splitI ibox118 0 241037672054680703091700132125140428113366220800000000000000 false
private noncomputable def ibox120 : Fin 4 → FixedTape.I := splitI ibox119 3 134476622244119296204894545978013895947714560000000000000000000 false
private noncomputable def ibox121 : Fin 4 → FixedTape.I := splitI ibox119 3 134476622244119296204894545978013895947714560000000000000000000 true
private noncomputable def ibox122 : Fin 4 → FixedTape.I := splitI ibox118 0 241037672054680703091700132125140428113366220800000000000000 true
private noncomputable def ibox123 : Fin 4 → FixedTape.I := splitI ibox122 3 134476622244119296204894545978013895947714560000000000000000000 false
private noncomputable def ibox124 : Fin 4 → FixedTape.I := splitI ibox122 3 134476622244119296204894545978013895947714560000000000000000000 true
private noncomputable def ibox125 : Fin 4 → FixedTape.I := splitI ibox117 3 149418469160132551338771717753348773275238400000000000000000000 true
private noncomputable def ibox126 : Fin 4 → FixedTape.I := splitI ibox125 0 241037672054680703091700132125140428113366220800000000000000 false
private noncomputable def ibox127 : Fin 4 → FixedTape.I := splitI ibox126 3 164360316076145806472648889528683650602762240000000000000000000 false
private noncomputable def ibox128 : Fin 4 → FixedTape.I := splitI ibox126 3 164360316076145806472648889528683650602762240000000000000000000 true
private noncomputable def ibox129 : Fin 4 → FixedTape.I := splitI ibox125 0 241037672054680703091700132125140428113366220800000000000000 true
private noncomputable def ibox130 : Fin 4 → FixedTape.I := splitI ibox129 3 164360316076145806472648889528683650602762240000000000000000000 false
private noncomputable def ibox131 : Fin 4 → FixedTape.I := splitI ibox129 3 164360316076145806472648889528683650602762240000000000000000000 true
private noncomputable def ibox132 : Fin 4 → FixedTape.I := splitI ibox100 3 179302162992159061606526061304018527930286080000000000000000000 true
private noncomputable def ibox133 : Fin 4 → FixedTape.I := splitI ibox132 3 209185856824185571874280404854688282585333760000000000000000000 false
private noncomputable def ibox134 : Fin 4 → FixedTape.I := splitI ibox133 0 235432144797595105345381524401299953040962355200000000000000 false
private noncomputable def ibox135 : Fin 4 → FixedTape.I := splitI ibox134 0 229826617540509507599062916677459477968558489600000000000000 false
private noncomputable def ibox136 : Fin 4 → FixedTape.I := splitI ibox135 3 194244009908172316740403233079353405257809920000000000000000000 false
private noncomputable def ibox137 : Fin 4 → FixedTape.I := splitI ibox135 3 194244009908172316740403233079353405257809920000000000000000000 true
private noncomputable def ibox138 : Fin 4 → FixedTape.I := splitI ibox134 0 229826617540509507599062916677459477968558489600000000000000 true
private noncomputable def ibox139 : Fin 4 → FixedTape.I := splitI ibox138 3 194244009908172316740403233079353405257809920000000000000000000 false
private noncomputable def ibox140 : Fin 4 → FixedTape.I := splitI ibox138 3 194244009908172316740403233079353405257809920000000000000000000 true
private noncomputable def ibox141 : Fin 4 → FixedTape.I := splitI ibox133 0 235432144797595105345381524401299953040962355200000000000000 true
private noncomputable def ibox142 : Fin 4 → FixedTape.I := splitI ibox141 0 241037672054680703091700132125140428113366220800000000000000 false
private noncomputable def ibox143 : Fin 4 → FixedTape.I := splitI ibox142 3 194244009908172316740403233079353405257809920000000000000000000 false
private noncomputable def ibox144 : Fin 4 → FixedTape.I := splitI ibox142 3 194244009908172316740403233079353405257809920000000000000000000 true
private noncomputable def ibox145 : Fin 4 → FixedTape.I := splitI ibox141 0 241037672054680703091700132125140428113366220800000000000000 true
private noncomputable def ibox146 : Fin 4 → FixedTape.I := splitI ibox145 3 194244009908172316740403233079353405257809920000000000000000000 false
private noncomputable def ibox147 : Fin 4 → FixedTape.I := splitI ibox145 3 194244009908172316740403233079353405257809920000000000000000000 true
private noncomputable def ibox148 : Fin 4 → FixedTape.I := splitI ibox132 3 209185856824185571874280404854688282585333760000000000000000000 true
private noncomputable def ibox149 : Fin 4 → FixedTape.I := splitI ibox148 0 235432144797595105345381524401299953040962355200000000000000 false
private noncomputable def ibox150 : Fin 4 → FixedTape.I := splitI ibox149 0 229826617540509507599062916677459477968558489600000000000000 false
private noncomputable def ibox151 : Fin 4 → FixedTape.I := splitI ibox150 3 224127703740198827008157576630023159912857600000000000000000000 false
private noncomputable def ibox152 : Fin 4 → FixedTape.I := splitI ibox150 3 224127703740198827008157576630023159912857600000000000000000000 true
private noncomputable def ibox153 : Fin 4 → FixedTape.I := splitI ibox149 0 229826617540509507599062916677459477968558489600000000000000 true
private noncomputable def ibox154 : Fin 4 → FixedTape.I := splitI ibox153 3 224127703740198827008157576630023159912857600000000000000000000 false
private noncomputable def ibox155 : Fin 4 → FixedTape.I := splitI ibox153 3 224127703740198827008157576630023159912857600000000000000000000 true
private noncomputable def ibox156 : Fin 4 → FixedTape.I := splitI ibox148 0 235432144797595105345381524401299953040962355200000000000000 true
private noncomputable def ibox157 : Fin 4 → FixedTape.I := splitI ibox156 0 241037672054680703091700132125140428113366220800000000000000 false
private noncomputable def ibox158 : Fin 4 → FixedTape.I := splitI ibox157 3 224127703740198827008157576630023159912857600000000000000000000 false
private noncomputable def ibox159 : Fin 4 → FixedTape.I := splitI ibox157 3 224127703740198827008157576630023159912857600000000000000000000 true
private noncomputable def ibox160 : Fin 4 → FixedTape.I := splitI ibox156 0 241037672054680703091700132125140428113366220800000000000000 true
private noncomputable def ibox161 : Fin 4 → FixedTape.I := splitI ibox160 3 224127703740198827008157576630023159912857600000000000000000000 false
private noncomputable def ibox162 : Fin 4 → FixedTape.I := splitI ibox160 3 224127703740198827008157576630023159912857600000000000000000000 true
private noncomputable def ibox163 : Fin 4 → FixedTape.I := splitI ibox34 0 246643199311766300838018739848980903185770086400000000000000 true
private noncomputable def ibox164 : Fin 4 → FixedTape.I := faceI ibox163 1 false
private noncomputable def ibox165 : Fin 4 → FixedTape.I := splitI ibox164 3 119534775328106041071017374202679018620190720000000000000000000 false
private noncomputable def ibox166 : Fin 4 → FixedTape.I := splitI ibox165 3 59767387664053020535508687101339509310095360000000000000000000 false
private noncomputable def ibox167 : Fin 4 → FixedTape.I := splitI ibox166 0 257854253825937496330655955296661853330577817600000000000000 false
private noncomputable def ibox168 : Fin 4 → FixedTape.I := splitI ibox167 3 29883693832026510267754343550669754655047680000000000000000000 false
private noncomputable def ibox169 : Fin 4 → FixedTape.I := splitI ibox168 0 252248726568851898584337347572821378258173952000000000000000 false
private noncomputable def ibox170 : Fin 4 → FixedTape.I := splitI ibox169 0 249445962940309099711178043710901140721972019200000000000000 false
private noncomputable def ibox171 : Fin 4 → FixedTape.I := splitI ibox169 0 249445962940309099711178043710901140721972019200000000000000 true
private noncomputable def ibox172 : Fin 4 → FixedTape.I := splitI ibox168 0 252248726568851898584337347572821378258173952000000000000000 true
private noncomputable def ibox173 : Fin 4 → FixedTape.I := splitI ibox172 0 255051490197394697457496651434741615794375884800000000000000 false
private noncomputable def ibox174 : Fin 4 → FixedTape.I := splitI ibox172 0 255051490197394697457496651434741615794375884800000000000000 true
private noncomputable def ibox175 : Fin 4 → FixedTape.I := splitI ibox167 3 29883693832026510267754343550669754655047680000000000000000000 true
private noncomputable def ibox176 : Fin 4 → FixedTape.I := splitI ibox175 0 252248726568851898584337347572821378258173952000000000000000 false
private noncomputable def ibox177 : Fin 4 → FixedTape.I := splitI ibox176 0 249445962940309099711178043710901140721972019200000000000000 false
private noncomputable def ibox178 : Fin 4 → FixedTape.I := splitI ibox176 0 249445962940309099711178043710901140721972019200000000000000 true
private noncomputable def ibox179 : Fin 4 → FixedTape.I := splitI ibox175 0 252248726568851898584337347572821378258173952000000000000000 true
private noncomputable def ibox180 : Fin 4 → FixedTape.I := splitI ibox166 0 257854253825937496330655955296661853330577817600000000000000 true
private noncomputable def ibox181 : Fin 4 → FixedTape.I := splitI ibox180 3 29883693832026510267754343550669754655047680000000000000000000 false
private noncomputable def ibox182 : Fin 4 → FixedTape.I := splitI ibox181 0 263459781083023094076974563020502328402981683200000000000000 false
private noncomputable def ibox183 : Fin 4 → FixedTape.I := splitI ibox181 0 263459781083023094076974563020502328402981683200000000000000 true
private noncomputable def ibox184 : Fin 4 → FixedTape.I := splitI ibox180 3 29883693832026510267754343550669754655047680000000000000000000 true
private noncomputable def ibox185 : Fin 4 → FixedTape.I := splitI ibox184 0 263459781083023094076974563020502328402981683200000000000000 false
private noncomputable def ibox186 : Fin 4 → FixedTape.I := splitI ibox184 0 263459781083023094076974563020502328402981683200000000000000 true
private noncomputable def ibox187 : Fin 4 → FixedTape.I := splitI ibox165 3 59767387664053020535508687101339509310095360000000000000000000 true
private noncomputable def ibox188 : Fin 4 → FixedTape.I := splitI ibox187 0 257854253825937496330655955296661853330577817600000000000000 false
private noncomputable def ibox189 : Fin 4 → FixedTape.I := splitI ibox188 3 89651081496079530803263030652009263965143040000000000000000000 false
private noncomputable def ibox190 : Fin 4 → FixedTape.I := splitI ibox189 0 252248726568851898584337347572821378258173952000000000000000 false
private noncomputable def ibox191 : Fin 4 → FixedTape.I := splitI ibox190 3 74709234580066275669385858876674386637619200000000000000000000 false
private noncomputable def ibox192 : Fin 4 → FixedTape.I := splitI ibox190 3 74709234580066275669385858876674386637619200000000000000000000 true
private noncomputable def ibox193 : Fin 4 → FixedTape.I := splitI ibox189 0 252248726568851898584337347572821378258173952000000000000000 true
private noncomputable def ibox194 : Fin 4 → FixedTape.I := splitI ibox188 3 89651081496079530803263030652009263965143040000000000000000000 true
private noncomputable def ibox195 : Fin 4 → FixedTape.I := splitI ibox194 0 252248726568851898584337347572821378258173952000000000000000 false
private noncomputable def ibox196 : Fin 4 → FixedTape.I := splitI ibox195 3 104592928412092785937140202427344141292666880000000000000000000 false
private noncomputable def ibox197 : Fin 4 → FixedTape.I := splitI ibox195 3 104592928412092785937140202427344141292666880000000000000000000 true
private noncomputable def ibox198 : Fin 4 → FixedTape.I := splitI ibox194 0 252248726568851898584337347572821378258173952000000000000000 true
private noncomputable def ibox199 : Fin 4 → FixedTape.I := splitI ibox187 0 257854253825937496330655955296661853330577817600000000000000 true
private noncomputable def ibox200 : Fin 4 → FixedTape.I := splitI ibox199 3 89651081496079530803263030652009263965143040000000000000000000 false
private noncomputable def ibox201 : Fin 4 → FixedTape.I := splitI ibox200 0 263459781083023094076974563020502328402981683200000000000000 false
private noncomputable def ibox202 : Fin 4 → FixedTape.I := splitI ibox200 0 263459781083023094076974563020502328402981683200000000000000 true
private noncomputable def ibox203 : Fin 4 → FixedTape.I := splitI ibox199 3 89651081496079530803263030652009263965143040000000000000000000 true
private noncomputable def ibox204 : Fin 4 → FixedTape.I := splitI ibox203 0 263459781083023094076974563020502328402981683200000000000000 false
private noncomputable def ibox205 : Fin 4 → FixedTape.I := splitI ibox203 0 263459781083023094076974563020502328402981683200000000000000 true
private noncomputable def ibox206 : Fin 4 → FixedTape.I := splitI ibox164 3 119534775328106041071017374202679018620190720000000000000000000 true
private noncomputable def ibox207 : Fin 4 → FixedTape.I := splitI ibox206 3 179302162992159061606526061304018527930286080000000000000000000 false
private noncomputable def ibox208 : Fin 4 → FixedTape.I := splitI ibox207 0 257854253825937496330655955296661853330577817600000000000000 false
private noncomputable def ibox209 : Fin 4 → FixedTape.I := splitI ibox208 3 149418469160132551338771717753348773275238400000000000000000000 false
private noncomputable def ibox210 : Fin 4 → FixedTape.I := splitI ibox209 0 252248726568851898584337347572821378258173952000000000000000 false
private noncomputable def ibox211 : Fin 4 → FixedTape.I := splitI ibox210 3 134476622244119296204894545978013895947714560000000000000000000 false
private noncomputable def ibox212 : Fin 4 → FixedTape.I := splitI ibox210 3 134476622244119296204894545978013895947714560000000000000000000 true
private noncomputable def ibox213 : Fin 4 → FixedTape.I := splitI ibox209 0 252248726568851898584337347572821378258173952000000000000000 true
private noncomputable def ibox214 : Fin 4 → FixedTape.I := splitI ibox208 3 149418469160132551338771717753348773275238400000000000000000000 true
private noncomputable def ibox215 : Fin 4 → FixedTape.I := splitI ibox214 0 252248726568851898584337347572821378258173952000000000000000 false
private noncomputable def ibox216 : Fin 4 → FixedTape.I := splitI ibox214 0 252248726568851898584337347572821378258173952000000000000000 true
private noncomputable def ibox217 : Fin 4 → FixedTape.I := splitI ibox207 0 257854253825937496330655955296661853330577817600000000000000 true
private noncomputable def ibox218 : Fin 4 → FixedTape.I := splitI ibox217 3 149418469160132551338771717753348773275238400000000000000000000 false
private noncomputable def ibox219 : Fin 4 → FixedTape.I := splitI ibox218 0 263459781083023094076974563020502328402981683200000000000000 false
private noncomputable def ibox220 : Fin 4 → FixedTape.I := splitI ibox218 0 263459781083023094076974563020502328402981683200000000000000 true
private noncomputable def ibox221 : Fin 4 → FixedTape.I := splitI ibox217 3 149418469160132551338771717753348773275238400000000000000000000 true
private noncomputable def ibox222 : Fin 4 → FixedTape.I := splitI ibox221 0 263459781083023094076974563020502328402981683200000000000000 false
private noncomputable def ibox223 : Fin 4 → FixedTape.I := splitI ibox221 0 263459781083023094076974563020502328402981683200000000000000 true
private noncomputable def ibox224 : Fin 4 → FixedTape.I := splitI ibox206 3 179302162992159061606526061304018527930286080000000000000000000 true
private noncomputable def ibox225 : Fin 4 → FixedTape.I := splitI ibox224 3 209185856824185571874280404854688282585333760000000000000000000 false
private noncomputable def ibox226 : Fin 4 → FixedTape.I := splitI ibox225 0 257854253825937496330655955296661853330577817600000000000000 false
private noncomputable def ibox227 : Fin 4 → FixedTape.I := splitI ibox226 0 252248726568851898584337347572821378258173952000000000000000 false
private noncomputable def ibox228 : Fin 4 → FixedTape.I := splitI ibox226 0 252248726568851898584337347572821378258173952000000000000000 true
private noncomputable def ibox229 : Fin 4 → FixedTape.I := splitI ibox225 0 257854253825937496330655955296661853330577817600000000000000 true
private noncomputable def ibox230 : Fin 4 → FixedTape.I := splitI ibox229 0 263459781083023094076974563020502328402981683200000000000000 false
private noncomputable def ibox231 : Fin 4 → FixedTape.I := splitI ibox229 0 263459781083023094076974563020502328402981683200000000000000 true
private noncomputable def ibox232 : Fin 4 → FixedTape.I := splitI ibox224 3 209185856824185571874280404854688282585333760000000000000000000 true
private noncomputable def ibox233 : Fin 4 → FixedTape.I := splitI ibox232 0 257854253825937496330655955296661853330577817600000000000000 false
private noncomputable def ibox234 : Fin 4 → FixedTape.I := splitI ibox233 0 252248726568851898584337347572821378258173952000000000000000 false
private noncomputable def ibox235 : Fin 4 → FixedTape.I := splitI ibox233 0 252248726568851898584337347572821378258173952000000000000000 true
private noncomputable def ibox236 : Fin 4 → FixedTape.I := splitI ibox232 0 257854253825937496330655955296661853330577817600000000000000 true
private noncomputable def ibox237 : Fin 4 → FixedTape.I := splitI ibox236 0 263459781083023094076974563020502328402981683200000000000000 false
private noncomputable def ibox238 : Fin 4 → FixedTape.I := splitI ibox236 0 263459781083023094076974563020502328402981683200000000000000 true
private noncomputable def ibox239 : Fin 4 → FixedTape.I := splitI ibox33 1 29883693832026510267754343550669754655047680000000000000000000 true
private noncomputable def ibox240 : Fin 4 → FixedTape.I := splitI ibox239 0 246643199311766300838018739848980903185770086400000000000000 false
private noncomputable def ibox241 : Fin 4 → FixedTape.I := faceI ibox240 1 false
private noncomputable def ibox242 : Fin 4 → FixedTape.I := splitI ibox241 3 119534775328106041071017374202679018620190720000000000000000000 false
private noncomputable def ibox243 : Fin 4 → FixedTape.I := splitI ibox241 3 119534775328106041071017374202679018620190720000000000000000000 true
private noncomputable def ibox244 : Fin 4 → FixedTape.I := splitI ibox239 0 246643199311766300838018739848980903185770086400000000000000 true
private noncomputable def ibox245 : Fin 4 → FixedTape.I := faceI ibox244 1 false
private noncomputable def ibox246 : Fin 4 → FixedTape.I := splitI ibox245 3 119534775328106041071017374202679018620190720000000000000000000 false
private noncomputable def ibox247 : Fin 4 → FixedTape.I := splitI ibox245 3 119534775328106041071017374202679018620190720000000000000000000 true
private noncomputable def ibox248 : Fin 4 → FixedTape.I := splitI ibox32 1 59767387664053020535508687101339509310095360000000000000000000 true
private noncomputable def ibox249 : Fin 4 → FixedTape.I := splitI ibox248 0 246643199311766300838018739848980903185770086400000000000000 false
private noncomputable def ibox250 : Fin 4 → FixedTape.I := faceI ibox249 1 false
private noncomputable def ibox251 : Fin 4 → FixedTape.I := splitI ibox248 0 246643199311766300838018739848980903185770086400000000000000 true
private noncomputable def ibox252 : Fin 4 → FixedTape.I := faceI ibox251 1 false
private noncomputable def ibox253 : Fin 4 → FixedTape.I := splitI ibox30 1 119534775328106041071017374202679018620190720000000000000000000 true
private noncomputable def ibox254 : Fin 4 → FixedTape.I := faceI ibox253 3 false
private noncomputable def ibox255 : Fin 4 → FixedTape.I := splitI ibox254 0 246643199311766300838018739848980903185770086400000000000000 false
private noncomputable def ibox256 : Fin 4 → FixedTape.I := splitI ibox255 1 179302162992159061606526061304018527930286080000000000000000000 false
private noncomputable def ibox257 : Fin 4 → FixedTape.I := splitI ibox255 1 179302162992159061606526061304018527930286080000000000000000000 true
private noncomputable def ibox258 : Fin 4 → FixedTape.I := splitI ibox254 0 246643199311766300838018739848980903185770086400000000000000 true
private noncomputable def ibox259 : Fin 4 → FixedTape.I := splitI ibox258 1 179302162992159061606526061304018527930286080000000000000000000 false
private noncomputable def ibox260 : Fin 4 → FixedTape.I := splitI ibox258 1 179302162992159061606526061304018527930286080000000000000000000 true
private noncomputable def ibox261 : Fin 4 → FixedTape.I := splitI ibox19 0 269065308340108691823293170744342803475385548800000000000000 true
private noncomputable def ibox262 : Fin 4 → FixedTape.I := splitI ibox261 2 179302162992159061606526061304018527930286080000000000000000000 false
private noncomputable def ibox263 : Fin 4 → FixedTape.I := faceI ibox262 3 false
private noncomputable def ibox264 : Fin 4 → FixedTape.I := splitI ibox263 0 291487417368451082808567601639704703765001011200000000000000 false
private noncomputable def ibox265 : Fin 4 → FixedTape.I := splitI ibox264 1 119534775328106041071017374202679018620190720000000000000000000 false
private noncomputable def ibox266 : Fin 4 → FixedTape.I := splitI ibox264 1 119534775328106041071017374202679018620190720000000000000000000 true
private noncomputable def ibox267 : Fin 4 → FixedTape.I := splitI ibox263 0 291487417368451082808567601639704703765001011200000000000000 true
private noncomputable def ibox268 : Fin 4 → FixedTape.I := splitI ibox267 1 119534775328106041071017374202679018620190720000000000000000000 false
private noncomputable def ibox269 : Fin 4 → FixedTape.I := splitI ibox267 1 119534775328106041071017374202679018620190720000000000000000000 true
private noncomputable def ibox270 : Fin 4 → FixedTape.I := splitI ibox261 2 179302162992159061606526061304018527930286080000000000000000000 true
private noncomputable def ibox271 : Fin 4 → FixedTape.I := splitI ibox270 1 119534775328106041071017374202679018620190720000000000000000000 false
private noncomputable def ibox272 : Fin 4 → FixedTape.I := faceI ibox271 2 true
private noncomputable def ibox273 : Fin 4 → FixedTape.I := splitI ibox272 1 59767387664053020535508687101339509310095360000000000000000000 false
private noncomputable def ibox274 : Fin 4 → FixedTape.I := splitI ibox273 1 29883693832026510267754343550669754655047680000000000000000000 false
private noncomputable def ibox275 : Fin 4 → FixedTape.I := splitI ibox274 0 291487417368451082808567601639704703765001011200000000000000 false
private noncomputable def ibox276 : Fin 4 → FixedTape.I := faceI ibox275 1 false
private noncomputable def ibox277 : Fin 4 → FixedTape.I := splitI ibox276 3 119534775328106041071017374202679018620190720000000000000000000 false
private noncomputable def ibox278 : Fin 4 → FixedTape.I := splitI ibox277 3 59767387664053020535508687101339509310095360000000000000000000 false
private noncomputable def ibox279 : Fin 4 → FixedTape.I := splitI ibox278 0 280276362854279887315930386192023753620193280000000000000000 false
private noncomputable def ibox280 : Fin 4 → FixedTape.I := splitI ibox279 3 29883693832026510267754343550669754655047680000000000000000000 false
private noncomputable def ibox281 : Fin 4 → FixedTape.I := splitI ibox280 0 274670835597194289569611778468183278547789414400000000000000 false
private noncomputable def ibox282 : Fin 4 → FixedTape.I := splitI ibox280 0 274670835597194289569611778468183278547789414400000000000000 true
private noncomputable def ibox283 : Fin 4 → FixedTape.I := splitI ibox279 3 29883693832026510267754343550669754655047680000000000000000000 true
private noncomputable def ibox284 : Fin 4 → FixedTape.I := splitI ibox283 0 274670835597194289569611778468183278547789414400000000000000 false
private noncomputable def ibox285 : Fin 4 → FixedTape.I := splitI ibox283 0 274670835597194289569611778468183278547789414400000000000000 true
private noncomputable def ibox286 : Fin 4 → FixedTape.I := splitI ibox278 0 280276362854279887315930386192023753620193280000000000000000 true
private noncomputable def ibox287 : Fin 4 → FixedTape.I := splitI ibox286 3 29883693832026510267754343550669754655047680000000000000000000 false
private noncomputable def ibox288 : Fin 4 → FixedTape.I := splitI ibox287 0 285881890111365485062248993915864228692597145600000000000000 false
private noncomputable def ibox289 : Fin 4 → FixedTape.I := splitI ibox287 0 285881890111365485062248993915864228692597145600000000000000 true
private noncomputable def ibox290 : Fin 4 → FixedTape.I := splitI ibox286 3 29883693832026510267754343550669754655047680000000000000000000 true
private noncomputable def ibox291 : Fin 4 → FixedTape.I := splitI ibox290 0 285881890111365485062248993915864228692597145600000000000000 false
private noncomputable def ibox292 : Fin 4 → FixedTape.I := splitI ibox290 0 285881890111365485062248993915864228692597145600000000000000 true
private noncomputable def ibox293 : Fin 4 → FixedTape.I := splitI ibox277 3 59767387664053020535508687101339509310095360000000000000000000 true
private noncomputable def ibox294 : Fin 4 → FixedTape.I := splitI ibox293 0 280276362854279887315930386192023753620193280000000000000000 false
private noncomputable def ibox295 : Fin 4 → FixedTape.I := splitI ibox294 3 89651081496079530803263030652009263965143040000000000000000000 false
private noncomputable def ibox296 : Fin 4 → FixedTape.I := splitI ibox295 0 274670835597194289569611778468183278547789414400000000000000 false
private noncomputable def ibox297 : Fin 4 → FixedTape.I := splitI ibox295 0 274670835597194289569611778468183278547789414400000000000000 true
private noncomputable def ibox298 : Fin 4 → FixedTape.I := splitI ibox294 3 89651081496079530803263030652009263965143040000000000000000000 true
private noncomputable def ibox299 : Fin 4 → FixedTape.I := splitI ibox298 0 274670835597194289569611778468183278547789414400000000000000 false
private noncomputable def ibox300 : Fin 4 → FixedTape.I := splitI ibox298 0 274670835597194289569611778468183278547789414400000000000000 true
private noncomputable def ibox301 : Fin 4 → FixedTape.I := splitI ibox293 0 280276362854279887315930386192023753620193280000000000000000 true
private noncomputable def ibox302 : Fin 4 → FixedTape.I := splitI ibox301 3 89651081496079530803263030652009263965143040000000000000000000 false
private noncomputable def ibox303 : Fin 4 → FixedTape.I := splitI ibox302 0 285881890111365485062248993915864228692597145600000000000000 false
private noncomputable def ibox304 : Fin 4 → FixedTape.I := splitI ibox302 0 285881890111365485062248993915864228692597145600000000000000 true
private noncomputable def ibox305 : Fin 4 → FixedTape.I := splitI ibox301 3 89651081496079530803263030652009263965143040000000000000000000 true
private noncomputable def ibox306 : Fin 4 → FixedTape.I := splitI ibox305 0 285881890111365485062248993915864228692597145600000000000000 false
private noncomputable def ibox307 : Fin 4 → FixedTape.I := splitI ibox305 0 285881890111365485062248993915864228692597145600000000000000 true
private noncomputable def ibox308 : Fin 4 → FixedTape.I := splitI ibox276 3 119534775328106041071017374202679018620190720000000000000000000 true
private noncomputable def ibox309 : Fin 4 → FixedTape.I := splitI ibox308 3 179302162992159061606526061304018527930286080000000000000000000 false
private noncomputable def ibox310 : Fin 4 → FixedTape.I := splitI ibox309 0 280276362854279887315930386192023753620193280000000000000000 false
private noncomputable def ibox311 : Fin 4 → FixedTape.I := splitI ibox310 3 149418469160132551338771717753348773275238400000000000000000000 false
private noncomputable def ibox312 : Fin 4 → FixedTape.I := splitI ibox311 0 274670835597194289569611778468183278547789414400000000000000 false
private noncomputable def ibox313 : Fin 4 → FixedTape.I := splitI ibox311 0 274670835597194289569611778468183278547789414400000000000000 true
private noncomputable def ibox314 : Fin 4 → FixedTape.I := splitI ibox310 3 149418469160132551338771717753348773275238400000000000000000000 true
private noncomputable def ibox315 : Fin 4 → FixedTape.I := splitI ibox314 0 274670835597194289569611778468183278547789414400000000000000 false
private noncomputable def ibox316 : Fin 4 → FixedTape.I := splitI ibox314 0 274670835597194289569611778468183278547789414400000000000000 true
private noncomputable def ibox317 : Fin 4 → FixedTape.I := splitI ibox309 0 280276362854279887315930386192023753620193280000000000000000 true
private noncomputable def ibox318 : Fin 4 → FixedTape.I := splitI ibox317 3 149418469160132551338771717753348773275238400000000000000000000 false
private noncomputable def ibox319 : Fin 4 → FixedTape.I := splitI ibox318 0 285881890111365485062248993915864228692597145600000000000000 false
private noncomputable def ibox320 : Fin 4 → FixedTape.I := splitI ibox318 0 285881890111365485062248993915864228692597145600000000000000 true
private noncomputable def ibox321 : Fin 4 → FixedTape.I := splitI ibox317 3 149418469160132551338771717753348773275238400000000000000000000 true
private noncomputable def ibox322 : Fin 4 → FixedTape.I := splitI ibox321 0 285881890111365485062248993915864228692597145600000000000000 false
private noncomputable def ibox323 : Fin 4 → FixedTape.I := splitI ibox321 0 285881890111365485062248993915864228692597145600000000000000 true
private noncomputable def ibox324 : Fin 4 → FixedTape.I := splitI ibox308 3 179302162992159061606526061304018527930286080000000000000000000 true
private noncomputable def ibox325 : Fin 4 → FixedTape.I := splitI ibox324 3 209185856824185571874280404854688282585333760000000000000000000 false
private noncomputable def ibox326 : Fin 4 → FixedTape.I := splitI ibox325 0 280276362854279887315930386192023753620193280000000000000000 false
private noncomputable def ibox327 : Fin 4 → FixedTape.I := splitI ibox326 0 274670835597194289569611778468183278547789414400000000000000 false
private noncomputable def ibox328 : Fin 4 → FixedTape.I := splitI ibox326 0 274670835597194289569611778468183278547789414400000000000000 true
private noncomputable def ibox329 : Fin 4 → FixedTape.I := splitI ibox325 0 280276362854279887315930386192023753620193280000000000000000 true
private noncomputable def ibox330 : Fin 4 → FixedTape.I := splitI ibox329 0 285881890111365485062248993915864228692597145600000000000000 false
private noncomputable def ibox331 : Fin 4 → FixedTape.I := splitI ibox329 0 285881890111365485062248993915864228692597145600000000000000 true
private noncomputable def ibox332 : Fin 4 → FixedTape.I := splitI ibox324 3 209185856824185571874280404854688282585333760000000000000000000 true
private noncomputable def ibox333 : Fin 4 → FixedTape.I := splitI ibox332 0 280276362854279887315930386192023753620193280000000000000000 false
private noncomputable def ibox334 : Fin 4 → FixedTape.I := splitI ibox333 0 274670835597194289569611778468183278547789414400000000000000 false
private noncomputable def ibox335 : Fin 4 → FixedTape.I := splitI ibox333 0 274670835597194289569611778468183278547789414400000000000000 true
private noncomputable def ibox336 : Fin 4 → FixedTape.I := splitI ibox332 0 280276362854279887315930386192023753620193280000000000000000 true
private noncomputable def ibox337 : Fin 4 → FixedTape.I := splitI ibox336 3 224127703740198827008157576630023159912857600000000000000000000 false
private noncomputable def ibox338 : Fin 4 → FixedTape.I := splitI ibox336 3 224127703740198827008157576630023159912857600000000000000000000 true
private noncomputable def ibox339 : Fin 4 → FixedTape.I := splitI ibox274 0 291487417368451082808567601639704703765001011200000000000000 true
private noncomputable def ibox340 : Fin 4 → FixedTape.I := faceI ibox339 1 false
private noncomputable def ibox341 : Fin 4 → FixedTape.I := splitI ibox340 3 119534775328106041071017374202679018620190720000000000000000000 false
private noncomputable def ibox342 : Fin 4 → FixedTape.I := splitI ibox341 3 59767387664053020535508687101339509310095360000000000000000000 false
private noncomputable def ibox343 : Fin 4 → FixedTape.I := splitI ibox342 0 302698471882622278301204817087385653909808742400000000000000 false
private noncomputable def ibox344 : Fin 4 → FixedTape.I := splitI ibox343 3 29883693832026510267754343550669754655047680000000000000000000 false
private noncomputable def ibox345 : Fin 4 → FixedTape.I := splitI ibox344 0 297092944625536680554886209363545178837404876800000000000000 false
private noncomputable def ibox346 : Fin 4 → FixedTape.I := splitI ibox344 0 297092944625536680554886209363545178837404876800000000000000 true
private noncomputable def ibox347 : Fin 4 → FixedTape.I := splitI ibox343 3 29883693832026510267754343550669754655047680000000000000000000 true
private noncomputable def ibox348 : Fin 4 → FixedTape.I := splitI ibox347 0 297092944625536680554886209363545178837404876800000000000000 false
private noncomputable def ibox349 : Fin 4 → FixedTape.I := splitI ibox347 0 297092944625536680554886209363545178837404876800000000000000 true
private noncomputable def ibox350 : Fin 4 → FixedTape.I := splitI ibox342 0 302698471882622278301204817087385653909808742400000000000000 true
private noncomputable def ibox351 : Fin 4 → FixedTape.I := splitI ibox350 3 29883693832026510267754343550669754655047680000000000000000000 false
private noncomputable def ibox352 : Fin 4 → FixedTape.I := splitI ibox351 0 308303999139707876047523424811226128982212608000000000000000 false
private noncomputable def ibox353 : Fin 4 → FixedTape.I := splitI ibox351 0 308303999139707876047523424811226128982212608000000000000000 true
private noncomputable def ibox354 : Fin 4 → FixedTape.I := splitI ibox350 3 29883693832026510267754343550669754655047680000000000000000000 true
private noncomputable def ibox355 : Fin 4 → FixedTape.I := splitI ibox354 0 308303999139707876047523424811226128982212608000000000000000 false
private noncomputable def ibox356 : Fin 4 → FixedTape.I := splitI ibox354 0 308303999139707876047523424811226128982212608000000000000000 true
private noncomputable def ibox357 : Fin 4 → FixedTape.I := splitI ibox341 3 59767387664053020535508687101339509310095360000000000000000000 true
private noncomputable def ibox358 : Fin 4 → FixedTape.I := splitI ibox357 0 302698471882622278301204817087385653909808742400000000000000 false
private noncomputable def ibox359 : Fin 4 → FixedTape.I := splitI ibox358 3 89651081496079530803263030652009263965143040000000000000000000 false
private noncomputable def ibox360 : Fin 4 → FixedTape.I := splitI ibox359 0 297092944625536680554886209363545178837404876800000000000000 false
private noncomputable def ibox361 : Fin 4 → FixedTape.I := splitI ibox359 0 297092944625536680554886209363545178837404876800000000000000 true
private noncomputable def ibox362 : Fin 4 → FixedTape.I := splitI ibox358 3 89651081496079530803263030652009263965143040000000000000000000 true
private noncomputable def ibox363 : Fin 4 → FixedTape.I := splitI ibox362 0 297092944625536680554886209363545178837404876800000000000000 false
private noncomputable def ibox364 : Fin 4 → FixedTape.I := splitI ibox362 0 297092944625536680554886209363545178837404876800000000000000 true
private noncomputable def ibox365 : Fin 4 → FixedTape.I := splitI ibox357 0 302698471882622278301204817087385653909808742400000000000000 true
private noncomputable def ibox366 : Fin 4 → FixedTape.I := splitI ibox365 3 89651081496079530803263030652009263965143040000000000000000000 false
private noncomputable def ibox367 : Fin 4 → FixedTape.I := splitI ibox366 0 308303999139707876047523424811226128982212608000000000000000 false
private noncomputable def ibox368 : Fin 4 → FixedTape.I := splitI ibox366 0 308303999139707876047523424811226128982212608000000000000000 true
private noncomputable def ibox369 : Fin 4 → FixedTape.I := splitI ibox365 3 89651081496079530803263030652009263965143040000000000000000000 true
private noncomputable def ibox370 : Fin 4 → FixedTape.I := splitI ibox369 0 308303999139707876047523424811226128982212608000000000000000 false
private noncomputable def ibox371 : Fin 4 → FixedTape.I := splitI ibox369 0 308303999139707876047523424811226128982212608000000000000000 true
private noncomputable def ibox372 : Fin 4 → FixedTape.I := splitI ibox340 3 119534775328106041071017374202679018620190720000000000000000000 true
private noncomputable def ibox373 : Fin 4 → FixedTape.I := splitI ibox372 3 179302162992159061606526061304018527930286080000000000000000000 false
private noncomputable def ibox374 : Fin 4 → FixedTape.I := splitI ibox373 0 302698471882622278301204817087385653909808742400000000000000 false
private noncomputable def ibox375 : Fin 4 → FixedTape.I := splitI ibox374 3 149418469160132551338771717753348773275238400000000000000000000 false
private noncomputable def ibox376 : Fin 4 → FixedTape.I := splitI ibox375 0 297092944625536680554886209363545178837404876800000000000000 false
private noncomputable def ibox377 : Fin 4 → FixedTape.I := splitI ibox375 0 297092944625536680554886209363545178837404876800000000000000 true
private noncomputable def ibox378 : Fin 4 → FixedTape.I := splitI ibox374 3 149418469160132551338771717753348773275238400000000000000000000 true
private noncomputable def ibox379 : Fin 4 → FixedTape.I := splitI ibox378 0 297092944625536680554886209363545178837404876800000000000000 false
private noncomputable def ibox380 : Fin 4 → FixedTape.I := splitI ibox378 0 297092944625536680554886209363545178837404876800000000000000 true
private noncomputable def ibox381 : Fin 4 → FixedTape.I := splitI ibox373 0 302698471882622278301204817087385653909808742400000000000000 true
private noncomputable def ibox382 : Fin 4 → FixedTape.I := splitI ibox381 3 149418469160132551338771717753348773275238400000000000000000000 false
private noncomputable def ibox383 : Fin 4 → FixedTape.I := splitI ibox382 0 308303999139707876047523424811226128982212608000000000000000 false
private noncomputable def ibox384 : Fin 4 → FixedTape.I := splitI ibox382 0 308303999139707876047523424811226128982212608000000000000000 true
private noncomputable def ibox385 : Fin 4 → FixedTape.I := splitI ibox381 3 149418469160132551338771717753348773275238400000000000000000000 true
private noncomputable def ibox386 : Fin 4 → FixedTape.I := splitI ibox385 0 308303999139707876047523424811226128982212608000000000000000 false
private noncomputable def ibox387 : Fin 4 → FixedTape.I := splitI ibox385 0 308303999139707876047523424811226128982212608000000000000000 true
private noncomputable def ibox388 : Fin 4 → FixedTape.I := splitI ibox372 3 179302162992159061606526061304018527930286080000000000000000000 true
private noncomputable def ibox389 : Fin 4 → FixedTape.I := splitI ibox388 3 209185856824185571874280404854688282585333760000000000000000000 false
private noncomputable def ibox390 : Fin 4 → FixedTape.I := splitI ibox389 0 302698471882622278301204817087385653909808742400000000000000 false
private noncomputable def ibox391 : Fin 4 → FixedTape.I := splitI ibox390 0 297092944625536680554886209363545178837404876800000000000000 false
private noncomputable def ibox392 : Fin 4 → FixedTape.I := splitI ibox390 0 297092944625536680554886209363545178837404876800000000000000 true
private noncomputable def ibox393 : Fin 4 → FixedTape.I := splitI ibox389 0 302698471882622278301204817087385653909808742400000000000000 true
private noncomputable def ibox394 : Fin 4 → FixedTape.I := splitI ibox393 0 308303999139707876047523424811226128982212608000000000000000 false
private noncomputable def ibox395 : Fin 4 → FixedTape.I := splitI ibox393 0 308303999139707876047523424811226128982212608000000000000000 true
private noncomputable def ibox396 : Fin 4 → FixedTape.I := splitI ibox388 3 209185856824185571874280404854688282585333760000000000000000000 true
private noncomputable def ibox397 : Fin 4 → FixedTape.I := splitI ibox396 0 302698471882622278301204817087385653909808742400000000000000 false
private noncomputable def ibox398 : Fin 4 → FixedTape.I := splitI ibox397 3 224127703740198827008157576630023159912857600000000000000000000 false
private noncomputable def ibox399 : Fin 4 → FixedTape.I := splitI ibox397 3 224127703740198827008157576630023159912857600000000000000000000 true
private noncomputable def ibox400 : Fin 4 → FixedTape.I := splitI ibox396 0 302698471882622278301204817087385653909808742400000000000000 true
private noncomputable def ibox401 : Fin 4 → FixedTape.I := splitI ibox400 3 224127703740198827008157576630023159912857600000000000000000000 false
private noncomputable def ibox402 : Fin 4 → FixedTape.I := splitI ibox400 3 224127703740198827008157576630023159912857600000000000000000000 true
private noncomputable def ibox403 : Fin 4 → FixedTape.I := splitI ibox273 1 29883693832026510267754343550669754655047680000000000000000000 true
private noncomputable def ibox404 : Fin 4 → FixedTape.I := splitI ibox403 0 291487417368451082808567601639704703765001011200000000000000 false
private noncomputable def ibox405 : Fin 4 → FixedTape.I := faceI ibox404 1 false
private noncomputable def ibox406 : Fin 4 → FixedTape.I := splitI ibox405 3 119534775328106041071017374202679018620190720000000000000000000 false
private noncomputable def ibox407 : Fin 4 → FixedTape.I := splitI ibox405 3 119534775328106041071017374202679018620190720000000000000000000 true
private noncomputable def ibox408 : Fin 4 → FixedTape.I := splitI ibox403 0 291487417368451082808567601639704703765001011200000000000000 true
private noncomputable def ibox409 : Fin 4 → FixedTape.I := faceI ibox408 1 false
private noncomputable def ibox410 : Fin 4 → FixedTape.I := splitI ibox409 3 119534775328106041071017374202679018620190720000000000000000000 false
private noncomputable def ibox411 : Fin 4 → FixedTape.I := splitI ibox409 3 119534775328106041071017374202679018620190720000000000000000000 true
private noncomputable def ibox412 : Fin 4 → FixedTape.I := splitI ibox272 1 59767387664053020535508687101339509310095360000000000000000000 true
private noncomputable def ibox413 : Fin 4 → FixedTape.I := splitI ibox412 0 291487417368451082808567601639704703765001011200000000000000 false
private noncomputable def ibox414 : Fin 4 → FixedTape.I := faceI ibox413 1 false
private noncomputable def ibox415 : Fin 4 → FixedTape.I := splitI ibox412 0 291487417368451082808567601639704703765001011200000000000000 true
private noncomputable def ibox416 : Fin 4 → FixedTape.I := faceI ibox415 1 false
private noncomputable def ibox417 : Fin 4 → FixedTape.I := splitI ibox270 1 119534775328106041071017374202679018620190720000000000000000000 true
private noncomputable def ibox418 : Fin 4 → FixedTape.I := faceI ibox417 3 false
private noncomputable def ibox419 : Fin 4 → FixedTape.I := splitI ibox418 0 291487417368451082808567601639704703765001011200000000000000 false
private noncomputable def ibox420 : Fin 4 → FixedTape.I := splitI ibox419 1 179302162992159061606526061304018527930286080000000000000000000 false
private noncomputable def ibox421 : Fin 4 → FixedTape.I := splitI ibox419 1 179302162992159061606526061304018527930286080000000000000000000 true
private noncomputable def ibox422 : Fin 4 → FixedTape.I := splitI ibox418 0 291487417368451082808567601639704703765001011200000000000000 true
private noncomputable def ibox423 : Fin 4 → FixedTape.I := splitI ibox422 1 179302162992159061606526061304018527930286080000000000000000000 false
private noncomputable def ibox424 : Fin 4 → FixedTape.I := splitI ibox422 1 179302162992159061606526061304018527930286080000000000000000000 true
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
private noncomputable def tree422 : TapeTree := .split 1 (((179302162992159061606526061304018527930286080000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree423 tree424
attribute [irreducible] tree422
private theorem accepted_422 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox422) tree422 = true := by
  simp only [tree422,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox422 1 (179302162992159061606526061304018527930286080000000000000000000 : Int) false,decode_split denominator ibox422 1 (179302162992159061606526061304018527930286080000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_423 h,accepted_424 h⟩
private noncomputable def tree421 : TapeTree := .centered (candidateRows ibox421) (candidateRows (FixedTape.midBox ibox421))
attribute [irreducible] tree421
private theorem sign_421 : 2*denominator*(computed denominator (FixedTape.midBox ibox421)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox421).gradient k).lo.natAbs ((computed denominator ibox421).gradient k).hi.natAbs : Int)*((ibox421 k).hi-(ibox421 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox421
    (computed denominator ibox421) (computed denominator (FixedTape.midBox ibox421))
    (by decide +kernel)
private theorem midpoint_even_421 : ∀ k, 2 ∣ (ibox421 k).lo+(ibox421 k).hi := by decide +kernel
private theorem accepted_421 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox421) tree421 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox421 midpoint_even_421
  simp only [tree421,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox421,candidate_valid h (FixedTape.midBox ibox421),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox421 212 (FixedTape.rowsAux denominator ibox421 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox421) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_421
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
private noncomputable def tree419 : TapeTree := .split 1 (((179302162992159061606526061304018527930286080000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree420 tree421
attribute [irreducible] tree419
private theorem accepted_419 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox419) tree419 = true := by
  simp only [tree419,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox419 1 (179302162992159061606526061304018527930286080000000000000000000 : Int) false,decode_split denominator ibox419 1 (179302162992159061606526061304018527930286080000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_420 h,accepted_421 h⟩
private noncomputable def tree418 : TapeTree := .split 0 (((291487417368451082808567601639704703765001011200000000000000 : Int) : ℚ)/(denominator : ℚ)) tree419 tree422
attribute [irreducible] tree418
private theorem accepted_418 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox418) tree418 = true := by
  simp only [tree418,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox418 0 (291487417368451082808567601639704703765001011200000000000000 : Int) false,decode_split denominator ibox418 0 (291487417368451082808567601639704703765001011200000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_419 h,accepted_422 h⟩
private noncomputable def tree417 : TapeTree := .face 3 false (candidateRows ibox417) tree418
attribute [irreducible] tree417
private theorem sign_417 : ((computed denominator ibox417).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_417 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox417) tree417 = true := by
  simp only [tree417,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox417,?_,accepted_418 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox417)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox417).gradient 3).hi) denominator_positive).1 sign_417
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
private noncomputable def tree415 : TapeTree := .face 1 false (candidateRows ibox415) tree416
attribute [irreducible] tree415
private theorem sign_415 : ((computed denominator ibox415).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_415 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox415) tree415 = true := by
  simp only [tree415,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox415,?_,accepted_416 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox415)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox415).gradient 1).hi) denominator_positive).1 sign_415
private noncomputable def tree414 : TapeTree := .centered (candidateRows ibox414) (candidateRows (FixedTape.midBox ibox414))
attribute [irreducible] tree414
private theorem sign_414 : 2*denominator*(computed denominator (FixedTape.midBox ibox414)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox414).gradient k).lo.natAbs ((computed denominator ibox414).gradient k).hi.natAbs : Int)*((ibox414 k).hi-(ibox414 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox414
    (computed denominator ibox414) (computed denominator (FixedTape.midBox ibox414))
    (by decide +kernel)
private theorem midpoint_even_414 : ∀ k, 2 ∣ (ibox414 k).lo+(ibox414 k).hi := by decide +kernel
private theorem accepted_414 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox414) tree414 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox414 midpoint_even_414
  simp only [tree414,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox414,candidate_valid h (FixedTape.midBox ibox414),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox414 212 (FixedTape.rowsAux denominator ibox414 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox414) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_414
private noncomputable def tree413 : TapeTree := .face 1 false (candidateRows ibox413) tree414
attribute [irreducible] tree413
private theorem sign_413 : ((computed denominator ibox413).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_413 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox413) tree413 = true := by
  simp only [tree413,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox413,?_,accepted_414 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox413)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox413).gradient 1).hi) denominator_positive).1 sign_413
private noncomputable def tree412 : TapeTree := .split 0 (((291487417368451082808567601639704703765001011200000000000000 : Int) : ℚ)/(denominator : ℚ)) tree413 tree415
attribute [irreducible] tree412
private theorem accepted_412 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox412) tree412 = true := by
  simp only [tree412,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox412 0 (291487417368451082808567601639704703765001011200000000000000 : Int) false,decode_split denominator ibox412 0 (291487417368451082808567601639704703765001011200000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_413 h,accepted_415 h⟩
private noncomputable def tree411 : TapeTree := .centered (candidateRows ibox411) (candidateRows (FixedTape.midBox ibox411))
attribute [irreducible] tree411
private theorem sign_411 : 2*denominator*(computed denominator (FixedTape.midBox ibox411)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox411).gradient k).lo.natAbs ((computed denominator ibox411).gradient k).hi.natAbs : Int)*((ibox411 k).hi-(ibox411 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox411
    (computed denominator ibox411) (computed denominator (FixedTape.midBox ibox411))
    (by decide +kernel)
private theorem midpoint_even_411 : ∀ k, 2 ∣ (ibox411 k).lo+(ibox411 k).hi := by decide +kernel
private theorem accepted_411 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox411) tree411 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox411 midpoint_even_411
  simp only [tree411,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox411,candidate_valid h (FixedTape.midBox ibox411),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox411 212 (FixedTape.rowsAux denominator ibox411 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox411) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_411
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
private noncomputable def tree409 : TapeTree := .split 3 (((119534775328106041071017374202679018620190720000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree410 tree411
attribute [irreducible] tree409
private theorem accepted_409 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox409) tree409 = true := by
  simp only [tree409,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox409 3 (119534775328106041071017374202679018620190720000000000000000000 : Int) false,decode_split denominator ibox409 3 (119534775328106041071017374202679018620190720000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_410 h,accepted_411 h⟩
private noncomputable def tree408 : TapeTree := .face 1 false (candidateRows ibox408) tree409
attribute [irreducible] tree408
private theorem sign_408 : ((computed denominator ibox408).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_408 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox408) tree408 = true := by
  simp only [tree408,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox408,?_,accepted_409 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox408)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox408).gradient 1).hi) denominator_positive).1 sign_408
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
private noncomputable def tree406 : TapeTree := .centered (candidateRows ibox406) (candidateRows (FixedTape.midBox ibox406))
attribute [irreducible] tree406
private theorem sign_406 : 2*denominator*(computed denominator (FixedTape.midBox ibox406)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox406).gradient k).lo.natAbs ((computed denominator ibox406).gradient k).hi.natAbs : Int)*((ibox406 k).hi-(ibox406 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox406
    (computed denominator ibox406) (computed denominator (FixedTape.midBox ibox406))
    (by decide +kernel)
private theorem midpoint_even_406 : ∀ k, 2 ∣ (ibox406 k).lo+(ibox406 k).hi := by decide +kernel
private theorem accepted_406 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox406) tree406 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox406 midpoint_even_406
  simp only [tree406,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox406,candidate_valid h (FixedTape.midBox ibox406),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox406 212 (FixedTape.rowsAux denominator ibox406 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox406) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_406
private noncomputable def tree405 : TapeTree := .split 3 (((119534775328106041071017374202679018620190720000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree406 tree407
attribute [irreducible] tree405
private theorem accepted_405 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox405) tree405 = true := by
  simp only [tree405,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox405 3 (119534775328106041071017374202679018620190720000000000000000000 : Int) false,decode_split denominator ibox405 3 (119534775328106041071017374202679018620190720000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_406 h,accepted_407 h⟩
private noncomputable def tree404 : TapeTree := .face 1 false (candidateRows ibox404) tree405
attribute [irreducible] tree404
private theorem sign_404 : ((computed denominator ibox404).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_404 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox404) tree404 = true := by
  simp only [tree404,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox404,?_,accepted_405 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox404)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox404).gradient 1).hi) denominator_positive).1 sign_404
private noncomputable def tree403 : TapeTree := .split 0 (((291487417368451082808567601639704703765001011200000000000000 : Int) : ℚ)/(denominator : ℚ)) tree404 tree408
attribute [irreducible] tree403
private theorem accepted_403 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox403) tree403 = true := by
  simp only [tree403,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox403 0 (291487417368451082808567601639704703765001011200000000000000 : Int) false,decode_split denominator ibox403 0 (291487417368451082808567601639704703765001011200000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_404 h,accepted_408 h⟩
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
private noncomputable def tree400 : TapeTree := .split 3 (((224127703740198827008157576630023159912857600000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree401 tree402
attribute [irreducible] tree400
private theorem accepted_400 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox400) tree400 = true := by
  simp only [tree400,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox400 3 (224127703740198827008157576630023159912857600000000000000000000 : Int) false,decode_split denominator ibox400 3 (224127703740198827008157576630023159912857600000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_401 h,accepted_402 h⟩
private noncomputable def tree399 : TapeTree := .centered (candidateRows ibox399) (candidateRows (FixedTape.midBox ibox399))
attribute [irreducible] tree399
private theorem sign_399 : 2*denominator*(computed denominator (FixedTape.midBox ibox399)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox399).gradient k).lo.natAbs ((computed denominator ibox399).gradient k).hi.natAbs : Int)*((ibox399 k).hi-(ibox399 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox399
    (computed denominator ibox399) (computed denominator (FixedTape.midBox ibox399))
    (by decide +kernel)
private theorem midpoint_even_399 : ∀ k, 2 ∣ (ibox399 k).lo+(ibox399 k).hi := by decide +kernel
private theorem accepted_399 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox399) tree399 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox399 midpoint_even_399
  simp only [tree399,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox399,candidate_valid h (FixedTape.midBox ibox399),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox399 212 (FixedTape.rowsAux denominator ibox399 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox399) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_399
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
private noncomputable def tree397 : TapeTree := .split 3 (((224127703740198827008157576630023159912857600000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree398 tree399
attribute [irreducible] tree397
private theorem accepted_397 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox397) tree397 = true := by
  simp only [tree397,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox397 3 (224127703740198827008157576630023159912857600000000000000000000 : Int) false,decode_split denominator ibox397 3 (224127703740198827008157576630023159912857600000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_398 h,accepted_399 h⟩
private noncomputable def tree396 : TapeTree := .split 0 (((302698471882622278301204817087385653909808742400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree397 tree400
attribute [irreducible] tree396
private theorem accepted_396 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox396) tree396 = true := by
  simp only [tree396,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox396 0 (302698471882622278301204817087385653909808742400000000000000 : Int) false,decode_split denominator ibox396 0 (302698471882622278301204817087385653909808742400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_397 h,accepted_400 h⟩
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
private noncomputable def tree393 : TapeTree := .split 0 (((308303999139707876047523424811226128982212608000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree394 tree395
attribute [irreducible] tree393
private theorem accepted_393 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox393) tree393 = true := by
  simp only [tree393,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox393 0 (308303999139707876047523424811226128982212608000000000000000 : Int) false,decode_split denominator ibox393 0 (308303999139707876047523424811226128982212608000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_394 h,accepted_395 h⟩
private noncomputable def tree392 : TapeTree := .centered (candidateRows ibox392) (candidateRows (FixedTape.midBox ibox392))
attribute [irreducible] tree392
private theorem sign_392 : 2*denominator*(computed denominator (FixedTape.midBox ibox392)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox392).gradient k).lo.natAbs ((computed denominator ibox392).gradient k).hi.natAbs : Int)*((ibox392 k).hi-(ibox392 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox392
    (computed denominator ibox392) (computed denominator (FixedTape.midBox ibox392))
    (by decide +kernel)
private theorem midpoint_even_392 : ∀ k, 2 ∣ (ibox392 k).lo+(ibox392 k).hi := by decide +kernel
private theorem accepted_392 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox392) tree392 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox392 midpoint_even_392
  simp only [tree392,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox392,candidate_valid h (FixedTape.midBox ibox392),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox392 212 (FixedTape.rowsAux denominator ibox392 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox392) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_392
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
private noncomputable def tree390 : TapeTree := .split 0 (((297092944625536680554886209363545178837404876800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree391 tree392
attribute [irreducible] tree390
private theorem accepted_390 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox390) tree390 = true := by
  simp only [tree390,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox390 0 (297092944625536680554886209363545178837404876800000000000000 : Int) false,decode_split denominator ibox390 0 (297092944625536680554886209363545178837404876800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_391 h,accepted_392 h⟩
private noncomputable def tree389 : TapeTree := .split 0 (((302698471882622278301204817087385653909808742400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree390 tree393
attribute [irreducible] tree389
private theorem accepted_389 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox389) tree389 = true := by
  simp only [tree389,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox389 0 (302698471882622278301204817087385653909808742400000000000000 : Int) false,decode_split denominator ibox389 0 (302698471882622278301204817087385653909808742400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_390 h,accepted_393 h⟩
private noncomputable def tree388 : TapeTree := .split 3 (((209185856824185571874280404854688282585333760000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree389 tree396
attribute [irreducible] tree388
private theorem accepted_388 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox388) tree388 = true := by
  simp only [tree388,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox388 3 (209185856824185571874280404854688282585333760000000000000000000 : Int) false,decode_split denominator ibox388 3 (209185856824185571874280404854688282585333760000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_389 h,accepted_396 h⟩
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
private noncomputable def tree385 : TapeTree := .split 0 (((308303999139707876047523424811226128982212608000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree386 tree387
attribute [irreducible] tree385
private theorem accepted_385 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox385) tree385 = true := by
  simp only [tree385,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox385 0 (308303999139707876047523424811226128982212608000000000000000 : Int) false,decode_split denominator ibox385 0 (308303999139707876047523424811226128982212608000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_386 h,accepted_387 h⟩
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
private noncomputable def tree382 : TapeTree := .split 0 (((308303999139707876047523424811226128982212608000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree383 tree384
attribute [irreducible] tree382
private theorem accepted_382 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox382) tree382 = true := by
  simp only [tree382,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox382 0 (308303999139707876047523424811226128982212608000000000000000 : Int) false,decode_split denominator ibox382 0 (308303999139707876047523424811226128982212608000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_383 h,accepted_384 h⟩
private noncomputable def tree381 : TapeTree := .split 3 (((149418469160132551338771717753348773275238400000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree382 tree385
attribute [irreducible] tree381
private theorem accepted_381 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox381) tree381 = true := by
  simp only [tree381,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox381 3 (149418469160132551338771717753348773275238400000000000000000000 : Int) false,decode_split denominator ibox381 3 (149418469160132551338771717753348773275238400000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_382 h,accepted_385 h⟩
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
private noncomputable def tree378 : TapeTree := .split 0 (((297092944625536680554886209363545178837404876800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree379 tree380
attribute [irreducible] tree378
private theorem accepted_378 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox378) tree378 = true := by
  simp only [tree378,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox378 0 (297092944625536680554886209363545178837404876800000000000000 : Int) false,decode_split denominator ibox378 0 (297092944625536680554886209363545178837404876800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_379 h,accepted_380 h⟩
private noncomputable def tree377 : TapeTree := .centered (candidateRows ibox377) (candidateRows (FixedTape.midBox ibox377))
attribute [irreducible] tree377
private theorem sign_377 : 2*denominator*(computed denominator (FixedTape.midBox ibox377)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox377).gradient k).lo.natAbs ((computed denominator ibox377).gradient k).hi.natAbs : Int)*((ibox377 k).hi-(ibox377 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox377
    (computed denominator ibox377) (computed denominator (FixedTape.midBox ibox377))
    (by decide +kernel)
private theorem midpoint_even_377 : ∀ k, 2 ∣ (ibox377 k).lo+(ibox377 k).hi := by decide +kernel
private theorem accepted_377 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox377) tree377 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox377 midpoint_even_377
  simp only [tree377,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox377,candidate_valid h (FixedTape.midBox ibox377),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox377 212 (FixedTape.rowsAux denominator ibox377 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox377) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_377
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
private noncomputable def tree375 : TapeTree := .split 0 (((297092944625536680554886209363545178837404876800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree376 tree377
attribute [irreducible] tree375
private theorem accepted_375 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox375) tree375 = true := by
  simp only [tree375,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox375 0 (297092944625536680554886209363545178837404876800000000000000 : Int) false,decode_split denominator ibox375 0 (297092944625536680554886209363545178837404876800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_376 h,accepted_377 h⟩
private noncomputable def tree374 : TapeTree := .split 3 (((149418469160132551338771717753348773275238400000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree375 tree378
attribute [irreducible] tree374
private theorem accepted_374 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox374) tree374 = true := by
  simp only [tree374,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox374 3 (149418469160132551338771717753348773275238400000000000000000000 : Int) false,decode_split denominator ibox374 3 (149418469160132551338771717753348773275238400000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_375 h,accepted_378 h⟩
private noncomputable def tree373 : TapeTree := .split 0 (((302698471882622278301204817087385653909808742400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree374 tree381
attribute [irreducible] tree373
private theorem accepted_373 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox373) tree373 = true := by
  simp only [tree373,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox373 0 (302698471882622278301204817087385653909808742400000000000000 : Int) false,decode_split denominator ibox373 0 (302698471882622278301204817087385653909808742400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_374 h,accepted_381 h⟩
private noncomputable def tree372 : TapeTree := .split 3 (((179302162992159061606526061304018527930286080000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree373 tree388
attribute [irreducible] tree372
private theorem accepted_372 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox372) tree372 = true := by
  simp only [tree372,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox372 3 (179302162992159061606526061304018527930286080000000000000000000 : Int) false,decode_split denominator ibox372 3 (179302162992159061606526061304018527930286080000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_373 h,accepted_388 h⟩
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
private noncomputable def tree369 : TapeTree := .split 0 (((308303999139707876047523424811226128982212608000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree370 tree371
attribute [irreducible] tree369
private theorem accepted_369 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox369) tree369 = true := by
  simp only [tree369,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox369 0 (308303999139707876047523424811226128982212608000000000000000 : Int) false,decode_split denominator ibox369 0 (308303999139707876047523424811226128982212608000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_370 h,accepted_371 h⟩
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
private noncomputable def tree366 : TapeTree := .split 0 (((308303999139707876047523424811226128982212608000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree367 tree368
attribute [irreducible] tree366
private theorem accepted_366 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox366) tree366 = true := by
  simp only [tree366,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox366 0 (308303999139707876047523424811226128982212608000000000000000 : Int) false,decode_split denominator ibox366 0 (308303999139707876047523424811226128982212608000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_367 h,accepted_368 h⟩
private noncomputable def tree365 : TapeTree := .split 3 (((89651081496079530803263030652009263965143040000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree366 tree369
attribute [irreducible] tree365
private theorem accepted_365 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox365) tree365 = true := by
  simp only [tree365,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox365 3 (89651081496079530803263030652009263965143040000000000000000000 : Int) false,decode_split denominator ibox365 3 (89651081496079530803263030652009263965143040000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_366 h,accepted_369 h⟩
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
private noncomputable def tree362 : TapeTree := .split 0 (((297092944625536680554886209363545178837404876800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree363 tree364
attribute [irreducible] tree362
private theorem accepted_362 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox362) tree362 = true := by
  simp only [tree362,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox362 0 (297092944625536680554886209363545178837404876800000000000000 : Int) false,decode_split denominator ibox362 0 (297092944625536680554886209363545178837404876800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_363 h,accepted_364 h⟩
private noncomputable def tree361 : TapeTree := .centered (candidateRows ibox361) (candidateRows (FixedTape.midBox ibox361))
attribute [irreducible] tree361
private theorem sign_361 : 2*denominator*(computed denominator (FixedTape.midBox ibox361)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox361).gradient k).lo.natAbs ((computed denominator ibox361).gradient k).hi.natAbs : Int)*((ibox361 k).hi-(ibox361 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox361
    (computed denominator ibox361) (computed denominator (FixedTape.midBox ibox361))
    (by decide +kernel)
private theorem midpoint_even_361 : ∀ k, 2 ∣ (ibox361 k).lo+(ibox361 k).hi := by decide +kernel
private theorem accepted_361 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox361) tree361 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox361 midpoint_even_361
  simp only [tree361,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox361,candidate_valid h (FixedTape.midBox ibox361),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox361 212 (FixedTape.rowsAux denominator ibox361 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox361) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_361
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
private noncomputable def tree359 : TapeTree := .split 0 (((297092944625536680554886209363545178837404876800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree360 tree361
attribute [irreducible] tree359
private theorem accepted_359 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox359) tree359 = true := by
  simp only [tree359,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox359 0 (297092944625536680554886209363545178837404876800000000000000 : Int) false,decode_split denominator ibox359 0 (297092944625536680554886209363545178837404876800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_360 h,accepted_361 h⟩
private noncomputable def tree358 : TapeTree := .split 3 (((89651081496079530803263030652009263965143040000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree359 tree362
attribute [irreducible] tree358
private theorem accepted_358 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox358) tree358 = true := by
  simp only [tree358,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox358 3 (89651081496079530803263030652009263965143040000000000000000000 : Int) false,decode_split denominator ibox358 3 (89651081496079530803263030652009263965143040000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_359 h,accepted_362 h⟩
private noncomputable def tree357 : TapeTree := .split 0 (((302698471882622278301204817087385653909808742400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree358 tree365
attribute [irreducible] tree357
private theorem accepted_357 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox357) tree357 = true := by
  simp only [tree357,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox357 0 (302698471882622278301204817087385653909808742400000000000000 : Int) false,decode_split denominator ibox357 0 (302698471882622278301204817087385653909808742400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_358 h,accepted_365 h⟩
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
private noncomputable def tree355 : TapeTree := .centered (candidateRows ibox355) (candidateRows (FixedTape.midBox ibox355))
attribute [irreducible] tree355
private theorem sign_355 : 2*denominator*(computed denominator (FixedTape.midBox ibox355)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox355).gradient k).lo.natAbs ((computed denominator ibox355).gradient k).hi.natAbs : Int)*((ibox355 k).hi-(ibox355 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox355
    (computed denominator ibox355) (computed denominator (FixedTape.midBox ibox355))
    (by decide +kernel)
private theorem midpoint_even_355 : ∀ k, 2 ∣ (ibox355 k).lo+(ibox355 k).hi := by decide +kernel
private theorem accepted_355 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox355) tree355 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox355 midpoint_even_355
  simp only [tree355,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox355,candidate_valid h (FixedTape.midBox ibox355),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox355 212 (FixedTape.rowsAux denominator ibox355 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox355) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_355
private noncomputable def tree354 : TapeTree := .split 0 (((308303999139707876047523424811226128982212608000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree355 tree356
attribute [irreducible] tree354
private theorem accepted_354 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox354) tree354 = true := by
  simp only [tree354,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox354 0 (308303999139707876047523424811226128982212608000000000000000 : Int) false,decode_split denominator ibox354 0 (308303999139707876047523424811226128982212608000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_355 h,accepted_356 h⟩
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
private noncomputable def tree351 : TapeTree := .split 0 (((308303999139707876047523424811226128982212608000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree352 tree353
attribute [irreducible] tree351
private theorem accepted_351 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox351) tree351 = true := by
  simp only [tree351,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox351 0 (308303999139707876047523424811226128982212608000000000000000 : Int) false,decode_split denominator ibox351 0 (308303999139707876047523424811226128982212608000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_352 h,accepted_353 h⟩
private noncomputable def tree350 : TapeTree := .split 3 (((29883693832026510267754343550669754655047680000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree351 tree354
attribute [irreducible] tree350
private theorem accepted_350 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox350) tree350 = true := by
  simp only [tree350,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox350 3 (29883693832026510267754343550669754655047680000000000000000000 : Int) false,decode_split denominator ibox350 3 (29883693832026510267754343550669754655047680000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_351 h,accepted_354 h⟩
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
private noncomputable def tree348 : TapeTree := .centered (candidateRows ibox348) (candidateRows (FixedTape.midBox ibox348))
attribute [irreducible] tree348
private theorem sign_348 : 2*denominator*(computed denominator (FixedTape.midBox ibox348)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox348).gradient k).lo.natAbs ((computed denominator ibox348).gradient k).hi.natAbs : Int)*((ibox348 k).hi-(ibox348 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox348
    (computed denominator ibox348) (computed denominator (FixedTape.midBox ibox348))
    (by decide +kernel)
private theorem midpoint_even_348 : ∀ k, 2 ∣ (ibox348 k).lo+(ibox348 k).hi := by decide +kernel
private theorem accepted_348 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox348) tree348 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox348 midpoint_even_348
  simp only [tree348,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox348,candidate_valid h (FixedTape.midBox ibox348),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox348 212 (FixedTape.rowsAux denominator ibox348 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox348) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_348
private noncomputable def tree347 : TapeTree := .split 0 (((297092944625536680554886209363545178837404876800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree348 tree349
attribute [irreducible] tree347
private theorem accepted_347 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox347) tree347 = true := by
  simp only [tree347,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox347 0 (297092944625536680554886209363545178837404876800000000000000 : Int) false,decode_split denominator ibox347 0 (297092944625536680554886209363545178837404876800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_348 h,accepted_349 h⟩
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
private noncomputable def tree344 : TapeTree := .split 0 (((297092944625536680554886209363545178837404876800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree345 tree346
attribute [irreducible] tree344
private theorem accepted_344 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox344) tree344 = true := by
  simp only [tree344,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox344 0 (297092944625536680554886209363545178837404876800000000000000 : Int) false,decode_split denominator ibox344 0 (297092944625536680554886209363545178837404876800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_345 h,accepted_346 h⟩
private noncomputable def tree343 : TapeTree := .split 3 (((29883693832026510267754343550669754655047680000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree344 tree347
attribute [irreducible] tree343
private theorem accepted_343 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox343) tree343 = true := by
  simp only [tree343,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox343 3 (29883693832026510267754343550669754655047680000000000000000000 : Int) false,decode_split denominator ibox343 3 (29883693832026510267754343550669754655047680000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_344 h,accepted_347 h⟩
private noncomputable def tree342 : TapeTree := .split 0 (((302698471882622278301204817087385653909808742400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree343 tree350
attribute [irreducible] tree342
private theorem accepted_342 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox342) tree342 = true := by
  simp only [tree342,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox342 0 (302698471882622278301204817087385653909808742400000000000000 : Int) false,decode_split denominator ibox342 0 (302698471882622278301204817087385653909808742400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_343 h,accepted_350 h⟩
private noncomputable def tree341 : TapeTree := .split 3 (((59767387664053020535508687101339509310095360000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree342 tree357
attribute [irreducible] tree341
private theorem accepted_341 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox341) tree341 = true := by
  simp only [tree341,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox341 3 (59767387664053020535508687101339509310095360000000000000000000 : Int) false,decode_split denominator ibox341 3 (59767387664053020535508687101339509310095360000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_342 h,accepted_357 h⟩
private noncomputable def tree340 : TapeTree := .split 3 (((119534775328106041071017374202679018620190720000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree341 tree372
attribute [irreducible] tree340
private theorem accepted_340 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox340) tree340 = true := by
  simp only [tree340,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox340 3 (119534775328106041071017374202679018620190720000000000000000000 : Int) false,decode_split denominator ibox340 3 (119534775328106041071017374202679018620190720000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_341 h,accepted_372 h⟩
private noncomputable def tree339 : TapeTree := .face 1 false (candidateRows ibox339) tree340
attribute [irreducible] tree339
private theorem sign_339 : ((computed denominator ibox339).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_339 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox339) tree339 = true := by
  simp only [tree339,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox339,?_,accepted_340 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox339)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox339).gradient 1).hi) denominator_positive).1 sign_339
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
private noncomputable def tree336 : TapeTree := .split 3 (((224127703740198827008157576630023159912857600000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree337 tree338
attribute [irreducible] tree336
private theorem accepted_336 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox336) tree336 = true := by
  simp only [tree336,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox336 3 (224127703740198827008157576630023159912857600000000000000000000 : Int) false,decode_split denominator ibox336 3 (224127703740198827008157576630023159912857600000000000000000000 : Int) true]
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
private noncomputable def tree333 : TapeTree := .split 0 (((274670835597194289569611778468183278547789414400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree334 tree335
attribute [irreducible] tree333
private theorem accepted_333 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox333) tree333 = true := by
  simp only [tree333,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox333 0 (274670835597194289569611778468183278547789414400000000000000 : Int) false,decode_split denominator ibox333 0 (274670835597194289569611778468183278547789414400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_334 h,accepted_335 h⟩
private noncomputable def tree332 : TapeTree := .split 0 (((280276362854279887315930386192023753620193280000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree333 tree336
attribute [irreducible] tree332
private theorem accepted_332 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox332) tree332 = true := by
  simp only [tree332,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox332 0 (280276362854279887315930386192023753620193280000000000000000 : Int) false,decode_split denominator ibox332 0 (280276362854279887315930386192023753620193280000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_333 h,accepted_336 h⟩
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
private noncomputable def tree330 : TapeTree := .centered (candidateRows ibox330) (candidateRows (FixedTape.midBox ibox330))
attribute [irreducible] tree330
private theorem sign_330 : 2*denominator*(computed denominator (FixedTape.midBox ibox330)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox330).gradient k).lo.natAbs ((computed denominator ibox330).gradient k).hi.natAbs : Int)*((ibox330 k).hi-(ibox330 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox330
    (computed denominator ibox330) (computed denominator (FixedTape.midBox ibox330))
    (by decide +kernel)
private theorem midpoint_even_330 : ∀ k, 2 ∣ (ibox330 k).lo+(ibox330 k).hi := by decide +kernel
private theorem accepted_330 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox330) tree330 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox330 midpoint_even_330
  simp only [tree330,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox330,candidate_valid h (FixedTape.midBox ibox330),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox330 212 (FixedTape.rowsAux denominator ibox330 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox330) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_330
private noncomputable def tree329 : TapeTree := .split 0 (((285881890111365485062248993915864228692597145600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree330 tree331
attribute [irreducible] tree329
private theorem accepted_329 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox329) tree329 = true := by
  simp only [tree329,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox329 0 (285881890111365485062248993915864228692597145600000000000000 : Int) false,decode_split denominator ibox329 0 (285881890111365485062248993915864228692597145600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_330 h,accepted_331 h⟩
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
private noncomputable def tree327 : TapeTree := .centered (candidateRows ibox327) (candidateRows (FixedTape.midBox ibox327))
attribute [irreducible] tree327
private theorem sign_327 : 2*denominator*(computed denominator (FixedTape.midBox ibox327)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox327).gradient k).lo.natAbs ((computed denominator ibox327).gradient k).hi.natAbs : Int)*((ibox327 k).hi-(ibox327 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox327
    (computed denominator ibox327) (computed denominator (FixedTape.midBox ibox327))
    (by decide +kernel)
private theorem midpoint_even_327 : ∀ k, 2 ∣ (ibox327 k).lo+(ibox327 k).hi := by decide +kernel
private theorem accepted_327 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox327) tree327 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox327 midpoint_even_327
  simp only [tree327,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox327,candidate_valid h (FixedTape.midBox ibox327),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox327 212 (FixedTape.rowsAux denominator ibox327 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox327) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_327
private noncomputable def tree326 : TapeTree := .split 0 (((274670835597194289569611778468183278547789414400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree327 tree328
attribute [irreducible] tree326
private theorem accepted_326 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox326) tree326 = true := by
  simp only [tree326,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox326 0 (274670835597194289569611778468183278547789414400000000000000 : Int) false,decode_split denominator ibox326 0 (274670835597194289569611778468183278547789414400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_327 h,accepted_328 h⟩
private noncomputable def tree325 : TapeTree := .split 0 (((280276362854279887315930386192023753620193280000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree326 tree329
attribute [irreducible] tree325
private theorem accepted_325 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox325) tree325 = true := by
  simp only [tree325,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox325 0 (280276362854279887315930386192023753620193280000000000000000 : Int) false,decode_split denominator ibox325 0 (280276362854279887315930386192023753620193280000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_326 h,accepted_329 h⟩
private noncomputable def tree324 : TapeTree := .split 3 (((209185856824185571874280404854688282585333760000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree325 tree332
attribute [irreducible] tree324
private theorem accepted_324 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox324) tree324 = true := by
  simp only [tree324,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox324 3 (209185856824185571874280404854688282585333760000000000000000000 : Int) false,decode_split denominator ibox324 3 (209185856824185571874280404854688282585333760000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_325 h,accepted_332 h⟩
private noncomputable def tree323 : TapeTree := .centered (candidateRows ibox323) (candidateRows (FixedTape.midBox ibox323))
attribute [irreducible] tree323
private theorem sign_323 : 2*denominator*(computed denominator (FixedTape.midBox ibox323)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox323).gradient k).lo.natAbs ((computed denominator ibox323).gradient k).hi.natAbs : Int)*((ibox323 k).hi-(ibox323 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox323
    (computed denominator ibox323) (computed denominator (FixedTape.midBox ibox323))
    (by decide +kernel)
private theorem midpoint_even_323 : ∀ k, 2 ∣ (ibox323 k).lo+(ibox323 k).hi := by decide +kernel
private theorem accepted_323 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox323) tree323 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox323 midpoint_even_323
  simp only [tree323,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox323,candidate_valid h (FixedTape.midBox ibox323),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox323 212 (FixedTape.rowsAux denominator ibox323 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox323) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_323
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
private noncomputable def tree321 : TapeTree := .split 0 (((285881890111365485062248993915864228692597145600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree322 tree323
attribute [irreducible] tree321
private theorem accepted_321 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox321) tree321 = true := by
  simp only [tree321,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox321 0 (285881890111365485062248993915864228692597145600000000000000 : Int) false,decode_split denominator ibox321 0 (285881890111365485062248993915864228692597145600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_322 h,accepted_323 h⟩
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
private noncomputable def tree318 : TapeTree := .split 0 (((285881890111365485062248993915864228692597145600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree319 tree320
attribute [irreducible] tree318
private theorem accepted_318 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox318) tree318 = true := by
  simp only [tree318,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox318 0 (285881890111365485062248993915864228692597145600000000000000 : Int) false,decode_split denominator ibox318 0 (285881890111365485062248993915864228692597145600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_319 h,accepted_320 h⟩
private noncomputable def tree317 : TapeTree := .split 3 (((149418469160132551338771717753348773275238400000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree318 tree321
attribute [irreducible] tree317
private theorem accepted_317 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox317) tree317 = true := by
  simp only [tree317,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox317 3 (149418469160132551338771717753348773275238400000000000000000000 : Int) false,decode_split denominator ibox317 3 (149418469160132551338771717753348773275238400000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_318 h,accepted_321 h⟩
private noncomputable def tree316 : TapeTree := .centered (candidateRows ibox316) (candidateRows (FixedTape.midBox ibox316))
attribute [irreducible] tree316
private theorem sign_316 : 2*denominator*(computed denominator (FixedTape.midBox ibox316)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox316).gradient k).lo.natAbs ((computed denominator ibox316).gradient k).hi.natAbs : Int)*((ibox316 k).hi-(ibox316 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox316
    (computed denominator ibox316) (computed denominator (FixedTape.midBox ibox316))
    (by decide +kernel)
private theorem midpoint_even_316 : ∀ k, 2 ∣ (ibox316 k).lo+(ibox316 k).hi := by decide +kernel
private theorem accepted_316 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox316) tree316 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox316 midpoint_even_316
  simp only [tree316,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox316,candidate_valid h (FixedTape.midBox ibox316),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox316 212 (FixedTape.rowsAux denominator ibox316 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox316) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_316
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
private noncomputable def tree314 : TapeTree := .split 0 (((274670835597194289569611778468183278547789414400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree315 tree316
attribute [irreducible] tree314
private theorem accepted_314 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox314) tree314 = true := by
  simp only [tree314,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox314 0 (274670835597194289569611778468183278547789414400000000000000 : Int) false,decode_split denominator ibox314 0 (274670835597194289569611778468183278547789414400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_315 h,accepted_316 h⟩
private noncomputable def tree313 : TapeTree := .centered (candidateRows ibox313) (candidateRows (FixedTape.midBox ibox313))
attribute [irreducible] tree313
private theorem sign_313 : 2*denominator*(computed denominator (FixedTape.midBox ibox313)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox313).gradient k).lo.natAbs ((computed denominator ibox313).gradient k).hi.natAbs : Int)*((ibox313 k).hi-(ibox313 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox313
    (computed denominator ibox313) (computed denominator (FixedTape.midBox ibox313))
    (by decide +kernel)
private theorem midpoint_even_313 : ∀ k, 2 ∣ (ibox313 k).lo+(ibox313 k).hi := by decide +kernel
private theorem accepted_313 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox313) tree313 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox313 midpoint_even_313
  simp only [tree313,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox313,candidate_valid h (FixedTape.midBox ibox313),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox313 212 (FixedTape.rowsAux denominator ibox313 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox313) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_313
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
private noncomputable def tree311 : TapeTree := .split 0 (((274670835597194289569611778468183278547789414400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree312 tree313
attribute [irreducible] tree311
private theorem accepted_311 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox311) tree311 = true := by
  simp only [tree311,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox311 0 (274670835597194289569611778468183278547789414400000000000000 : Int) false,decode_split denominator ibox311 0 (274670835597194289569611778468183278547789414400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_312 h,accepted_313 h⟩
private noncomputable def tree310 : TapeTree := .split 3 (((149418469160132551338771717753348773275238400000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree311 tree314
attribute [irreducible] tree310
private theorem accepted_310 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox310) tree310 = true := by
  simp only [tree310,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox310 3 (149418469160132551338771717753348773275238400000000000000000000 : Int) false,decode_split denominator ibox310 3 (149418469160132551338771717753348773275238400000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_311 h,accepted_314 h⟩
private noncomputable def tree309 : TapeTree := .split 0 (((280276362854279887315930386192023753620193280000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree310 tree317
attribute [irreducible] tree309
private theorem accepted_309 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox309) tree309 = true := by
  simp only [tree309,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox309 0 (280276362854279887315930386192023753620193280000000000000000 : Int) false,decode_split denominator ibox309 0 (280276362854279887315930386192023753620193280000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_310 h,accepted_317 h⟩
private noncomputable def tree308 : TapeTree := .split 3 (((179302162992159061606526061304018527930286080000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree309 tree324
attribute [irreducible] tree308
private theorem accepted_308 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox308) tree308 = true := by
  simp only [tree308,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox308 3 (179302162992159061606526061304018527930286080000000000000000000 : Int) false,decode_split denominator ibox308 3 (179302162992159061606526061304018527930286080000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_309 h,accepted_324 h⟩
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
private noncomputable def tree305 : TapeTree := .split 0 (((285881890111365485062248993915864228692597145600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree306 tree307
attribute [irreducible] tree305
private theorem accepted_305 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox305) tree305 = true := by
  simp only [tree305,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox305 0 (285881890111365485062248993915864228692597145600000000000000 : Int) false,decode_split denominator ibox305 0 (285881890111365485062248993915864228692597145600000000000000 : Int) true]
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
private noncomputable def tree302 : TapeTree := .split 0 (((285881890111365485062248993915864228692597145600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree303 tree304
attribute [irreducible] tree302
private theorem accepted_302 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox302) tree302 = true := by
  simp only [tree302,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox302 0 (285881890111365485062248993915864228692597145600000000000000 : Int) false,decode_split denominator ibox302 0 (285881890111365485062248993915864228692597145600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_303 h,accepted_304 h⟩
private noncomputable def tree301 : TapeTree := .split 3 (((89651081496079530803263030652009263965143040000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree302 tree305
attribute [irreducible] tree301
private theorem accepted_301 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox301) tree301 = true := by
  simp only [tree301,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox301 3 (89651081496079530803263030652009263965143040000000000000000000 : Int) false,decode_split denominator ibox301 3 (89651081496079530803263030652009263965143040000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_302 h,accepted_305 h⟩
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
private noncomputable def tree298 : TapeTree := .split 0 (((274670835597194289569611778468183278547789414400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree299 tree300
attribute [irreducible] tree298
private theorem accepted_298 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox298) tree298 = true := by
  simp only [tree298,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox298 0 (274670835597194289569611778468183278547789414400000000000000 : Int) false,decode_split denominator ibox298 0 (274670835597194289569611778468183278547789414400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_299 h,accepted_300 h⟩
private noncomputable def tree297 : TapeTree := .centered (candidateRows ibox297) (candidateRows (FixedTape.midBox ibox297))
attribute [irreducible] tree297
private theorem sign_297 : 2*denominator*(computed denominator (FixedTape.midBox ibox297)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox297).gradient k).lo.natAbs ((computed denominator ibox297).gradient k).hi.natAbs : Int)*((ibox297 k).hi-(ibox297 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox297
    (computed denominator ibox297) (computed denominator (FixedTape.midBox ibox297))
    (by decide +kernel)
private theorem midpoint_even_297 : ∀ k, 2 ∣ (ibox297 k).lo+(ibox297 k).hi := by decide +kernel
private theorem accepted_297 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox297) tree297 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox297 midpoint_even_297
  simp only [tree297,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox297,candidate_valid h (FixedTape.midBox ibox297),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox297 212 (FixedTape.rowsAux denominator ibox297 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox297) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_297
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
private noncomputable def tree295 : TapeTree := .split 0 (((274670835597194289569611778468183278547789414400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree296 tree297
attribute [irreducible] tree295
private theorem accepted_295 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox295) tree295 = true := by
  simp only [tree295,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox295 0 (274670835597194289569611778468183278547789414400000000000000 : Int) false,decode_split denominator ibox295 0 (274670835597194289569611778468183278547789414400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_296 h,accepted_297 h⟩
private noncomputable def tree294 : TapeTree := .split 3 (((89651081496079530803263030652009263965143040000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree295 tree298
attribute [irreducible] tree294
private theorem accepted_294 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox294) tree294 = true := by
  simp only [tree294,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox294 3 (89651081496079530803263030652009263965143040000000000000000000 : Int) false,decode_split denominator ibox294 3 (89651081496079530803263030652009263965143040000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_295 h,accepted_298 h⟩
private noncomputable def tree293 : TapeTree := .split 0 (((280276362854279887315930386192023753620193280000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree294 tree301
attribute [irreducible] tree293
private theorem accepted_293 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox293) tree293 = true := by
  simp only [tree293,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox293 0 (280276362854279887315930386192023753620193280000000000000000 : Int) false,decode_split denominator ibox293 0 (280276362854279887315930386192023753620193280000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_294 h,accepted_301 h⟩
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
private noncomputable def tree291 : TapeTree := .centered (candidateRows ibox291) (candidateRows (FixedTape.midBox ibox291))
attribute [irreducible] tree291
private theorem sign_291 : 2*denominator*(computed denominator (FixedTape.midBox ibox291)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox291).gradient k).lo.natAbs ((computed denominator ibox291).gradient k).hi.natAbs : Int)*((ibox291 k).hi-(ibox291 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox291
    (computed denominator ibox291) (computed denominator (FixedTape.midBox ibox291))
    (by decide +kernel)
private theorem midpoint_even_291 : ∀ k, 2 ∣ (ibox291 k).lo+(ibox291 k).hi := by decide +kernel
private theorem accepted_291 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox291) tree291 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox291 midpoint_even_291
  simp only [tree291,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox291,candidate_valid h (FixedTape.midBox ibox291),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox291 212 (FixedTape.rowsAux denominator ibox291 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox291) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_291
private noncomputable def tree290 : TapeTree := .split 0 (((285881890111365485062248993915864228692597145600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree291 tree292
attribute [irreducible] tree290
private theorem accepted_290 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox290) tree290 = true := by
  simp only [tree290,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox290 0 (285881890111365485062248993915864228692597145600000000000000 : Int) false,decode_split denominator ibox290 0 (285881890111365485062248993915864228692597145600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_291 h,accepted_292 h⟩
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
private noncomputable def tree287 : TapeTree := .split 0 (((285881890111365485062248993915864228692597145600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree288 tree289
attribute [irreducible] tree287
private theorem accepted_287 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox287) tree287 = true := by
  simp only [tree287,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox287 0 (285881890111365485062248993915864228692597145600000000000000 : Int) false,decode_split denominator ibox287 0 (285881890111365485062248993915864228692597145600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_288 h,accepted_289 h⟩
private noncomputable def tree286 : TapeTree := .split 3 (((29883693832026510267754343550669754655047680000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree287 tree290
attribute [irreducible] tree286
private theorem accepted_286 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox286) tree286 = true := by
  simp only [tree286,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox286 3 (29883693832026510267754343550669754655047680000000000000000000 : Int) false,decode_split denominator ibox286 3 (29883693832026510267754343550669754655047680000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_287 h,accepted_290 h⟩
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
private noncomputable def tree284 : TapeTree := .centered (candidateRows ibox284) (candidateRows (FixedTape.midBox ibox284))
attribute [irreducible] tree284
private theorem sign_284 : 2*denominator*(computed denominator (FixedTape.midBox ibox284)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox284).gradient k).lo.natAbs ((computed denominator ibox284).gradient k).hi.natAbs : Int)*((ibox284 k).hi-(ibox284 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox284
    (computed denominator ibox284) (computed denominator (FixedTape.midBox ibox284))
    (by decide +kernel)
private theorem midpoint_even_284 : ∀ k, 2 ∣ (ibox284 k).lo+(ibox284 k).hi := by decide +kernel
private theorem accepted_284 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox284) tree284 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox284 midpoint_even_284
  simp only [tree284,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox284,candidate_valid h (FixedTape.midBox ibox284),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox284 212 (FixedTape.rowsAux denominator ibox284 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox284) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_284
private noncomputable def tree283 : TapeTree := .split 0 (((274670835597194289569611778468183278547789414400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree284 tree285
attribute [irreducible] tree283
private theorem accepted_283 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox283) tree283 = true := by
  simp only [tree283,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox283 0 (274670835597194289569611778468183278547789414400000000000000 : Int) false,decode_split denominator ibox283 0 (274670835597194289569611778468183278547789414400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_284 h,accepted_285 h⟩
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
private noncomputable def tree281 : TapeTree := .centered (candidateRows ibox281) (candidateRows (FixedTape.midBox ibox281))
attribute [irreducible] tree281
private theorem sign_281 : 2*denominator*(computed denominator (FixedTape.midBox ibox281)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox281).gradient k).lo.natAbs ((computed denominator ibox281).gradient k).hi.natAbs : Int)*((ibox281 k).hi-(ibox281 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox281
    (computed denominator ibox281) (computed denominator (FixedTape.midBox ibox281))
    (by decide +kernel)
private theorem midpoint_even_281 : ∀ k, 2 ∣ (ibox281 k).lo+(ibox281 k).hi := by decide +kernel
private theorem accepted_281 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox281) tree281 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox281 midpoint_even_281
  simp only [tree281,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox281,candidate_valid h (FixedTape.midBox ibox281),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox281 212 (FixedTape.rowsAux denominator ibox281 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox281) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_281
private noncomputable def tree280 : TapeTree := .split 0 (((274670835597194289569611778468183278547789414400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree281 tree282
attribute [irreducible] tree280
private theorem accepted_280 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox280) tree280 = true := by
  simp only [tree280,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox280 0 (274670835597194289569611778468183278547789414400000000000000 : Int) false,decode_split denominator ibox280 0 (274670835597194289569611778468183278547789414400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_281 h,accepted_282 h⟩
private noncomputable def tree279 : TapeTree := .split 3 (((29883693832026510267754343550669754655047680000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree280 tree283
attribute [irreducible] tree279
private theorem accepted_279 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox279) tree279 = true := by
  simp only [tree279,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox279 3 (29883693832026510267754343550669754655047680000000000000000000 : Int) false,decode_split denominator ibox279 3 (29883693832026510267754343550669754655047680000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_280 h,accepted_283 h⟩
private noncomputable def tree278 : TapeTree := .split 0 (((280276362854279887315930386192023753620193280000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree279 tree286
attribute [irreducible] tree278
private theorem accepted_278 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox278) tree278 = true := by
  simp only [tree278,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox278 0 (280276362854279887315930386192023753620193280000000000000000 : Int) false,decode_split denominator ibox278 0 (280276362854279887315930386192023753620193280000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_279 h,accepted_286 h⟩
private noncomputable def tree277 : TapeTree := .split 3 (((59767387664053020535508687101339509310095360000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree278 tree293
attribute [irreducible] tree277
private theorem accepted_277 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox277) tree277 = true := by
  simp only [tree277,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox277 3 (59767387664053020535508687101339509310095360000000000000000000 : Int) false,decode_split denominator ibox277 3 (59767387664053020535508687101339509310095360000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_278 h,accepted_293 h⟩
private noncomputable def tree276 : TapeTree := .split 3 (((119534775328106041071017374202679018620190720000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree277 tree308
attribute [irreducible] tree276
private theorem accepted_276 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox276) tree276 = true := by
  simp only [tree276,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox276 3 (119534775328106041071017374202679018620190720000000000000000000 : Int) false,decode_split denominator ibox276 3 (119534775328106041071017374202679018620190720000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_277 h,accepted_308 h⟩
private noncomputable def tree275 : TapeTree := .face 1 false (candidateRows ibox275) tree276
attribute [irreducible] tree275
private theorem sign_275 : ((computed denominator ibox275).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_275 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox275) tree275 = true := by
  simp only [tree275,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox275,?_,accepted_276 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox275)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox275).gradient 1).hi) denominator_positive).1 sign_275
private noncomputable def tree274 : TapeTree := .split 0 (((291487417368451082808567601639704703765001011200000000000000 : Int) : ℚ)/(denominator : ℚ)) tree275 tree339
attribute [irreducible] tree274
private theorem accepted_274 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox274) tree274 = true := by
  simp only [tree274,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox274 0 (291487417368451082808567601639704703765001011200000000000000 : Int) false,decode_split denominator ibox274 0 (291487417368451082808567601639704703765001011200000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_275 h,accepted_339 h⟩
private noncomputable def tree273 : TapeTree := .split 1 (((29883693832026510267754343550669754655047680000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree274 tree403
attribute [irreducible] tree273
private theorem accepted_273 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox273) tree273 = true := by
  simp only [tree273,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox273 1 (29883693832026510267754343550669754655047680000000000000000000 : Int) false,decode_split denominator ibox273 1 (29883693832026510267754343550669754655047680000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_274 h,accepted_403 h⟩
private noncomputable def tree272 : TapeTree := .split 1 (((59767387664053020535508687101339509310095360000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree273 tree412
attribute [irreducible] tree272
private theorem accepted_272 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox272) tree272 = true := by
  simp only [tree272,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox272 1 (59767387664053020535508687101339509310095360000000000000000000 : Int) false,decode_split denominator ibox272 1 (59767387664053020535508687101339509310095360000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_273 h,accepted_412 h⟩
private noncomputable def tree271 : TapeTree := .face 2 true (candidateRows ibox271) tree272
attribute [irreducible] tree271
private theorem sign_271 : 0 ≤ ((computed denominator ibox271).gradient 2).lo := by decide +kernel
private theorem accepted_271 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox271) tree271 = true := by
  simp only [tree271,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox271,?_,accepted_272 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox271)).gradient 2).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox271).gradient 2).lo) denominator_positive).2 sign_271
private noncomputable def tree270 : TapeTree := .split 1 (((119534775328106041071017374202679018620190720000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree271 tree417
attribute [irreducible] tree270
private theorem accepted_270 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox270) tree270 = true := by
  simp only [tree270,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox270 1 (119534775328106041071017374202679018620190720000000000000000000 : Int) false,decode_split denominator ibox270 1 (119534775328106041071017374202679018620190720000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_271 h,accepted_417 h⟩
private noncomputable def tree269 : TapeTree := .centered (candidateRows ibox269) (candidateRows (FixedTape.midBox ibox269))
attribute [irreducible] tree269
private theorem sign_269 : 2*denominator*(computed denominator (FixedTape.midBox ibox269)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox269).gradient k).lo.natAbs ((computed denominator ibox269).gradient k).hi.natAbs : Int)*((ibox269 k).hi-(ibox269 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox269
    (computed denominator ibox269) (computed denominator (FixedTape.midBox ibox269))
    (by decide +kernel)
private theorem midpoint_even_269 : ∀ k, 2 ∣ (ibox269 k).lo+(ibox269 k).hi := by decide +kernel
private theorem accepted_269 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox269) tree269 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox269 midpoint_even_269
  simp only [tree269,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox269,candidate_valid h (FixedTape.midBox ibox269),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox269 212 (FixedTape.rowsAux denominator ibox269 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox269) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_269
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
private noncomputable def tree267 : TapeTree := .split 1 (((119534775328106041071017374202679018620190720000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree268 tree269
attribute [irreducible] tree267
private theorem accepted_267 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox267) tree267 = true := by
  simp only [tree267,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox267 1 (119534775328106041071017374202679018620190720000000000000000000 : Int) false,decode_split denominator ibox267 1 (119534775328106041071017374202679018620190720000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_268 h,accepted_269 h⟩
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
private noncomputable def tree264 : TapeTree := .split 1 (((119534775328106041071017374202679018620190720000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree265 tree266
attribute [irreducible] tree264
private theorem accepted_264 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox264) tree264 = true := by
  simp only [tree264,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox264 1 (119534775328106041071017374202679018620190720000000000000000000 : Int) false,decode_split denominator ibox264 1 (119534775328106041071017374202679018620190720000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_265 h,accepted_266 h⟩
private noncomputable def tree263 : TapeTree := .split 0 (((291487417368451082808567601639704703765001011200000000000000 : Int) : ℚ)/(denominator : ℚ)) tree264 tree267
attribute [irreducible] tree263
private theorem accepted_263 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox263) tree263 = true := by
  simp only [tree263,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox263 0 (291487417368451082808567601639704703765001011200000000000000 : Int) false,decode_split denominator ibox263 0 (291487417368451082808567601639704703765001011200000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_264 h,accepted_267 h⟩
private noncomputable def tree262 : TapeTree := .face 3 false (candidateRows ibox262) tree263
attribute [irreducible] tree262
private theorem sign_262 : ((computed denominator ibox262).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_262 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox262) tree262 = true := by
  simp only [tree262,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox262,?_,accepted_263 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox262)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox262).gradient 3).hi) denominator_positive).1 sign_262
private noncomputable def tree261 : TapeTree := .split 2 (((179302162992159061606526061304018527930286080000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree262 tree270
attribute [irreducible] tree261
private theorem accepted_261 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox261) tree261 = true := by
  simp only [tree261,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox261 2 (179302162992159061606526061304018527930286080000000000000000000 : Int) false,decode_split denominator ibox261 2 (179302162992159061606526061304018527930286080000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_262 h,accepted_270 h⟩
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
private noncomputable def tree258 : TapeTree := .split 1 (((179302162992159061606526061304018527930286080000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree259 tree260
attribute [irreducible] tree258
private theorem accepted_258 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox258) tree258 = true := by
  simp only [tree258,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox258 1 (179302162992159061606526061304018527930286080000000000000000000 : Int) false,decode_split denominator ibox258 1 (179302162992159061606526061304018527930286080000000000000000000 : Int) true]
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
private noncomputable def tree255 : TapeTree := .split 1 (((179302162992159061606526061304018527930286080000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree256 tree257
attribute [irreducible] tree255
private theorem accepted_255 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox255) tree255 = true := by
  simp only [tree255,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox255 1 (179302162992159061606526061304018527930286080000000000000000000 : Int) false,decode_split denominator ibox255 1 (179302162992159061606526061304018527930286080000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_256 h,accepted_257 h⟩
private noncomputable def tree254 : TapeTree := .split 0 (((246643199311766300838018739848980903185770086400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree255 tree258
attribute [irreducible] tree254
private theorem accepted_254 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox254) tree254 = true := by
  simp only [tree254,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox254 0 (246643199311766300838018739848980903185770086400000000000000 : Int) false,decode_split denominator ibox254 0 (246643199311766300838018739848980903185770086400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_255 h,accepted_258 h⟩
private noncomputable def tree253 : TapeTree := .face 3 false (candidateRows ibox253) tree254
attribute [irreducible] tree253
private theorem sign_253 : ((computed denominator ibox253).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_253 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox253) tree253 = true := by
  simp only [tree253,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox253,?_,accepted_254 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox253)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox253).gradient 3).hi) denominator_positive).1 sign_253
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
private noncomputable def tree251 : TapeTree := .face 1 false (candidateRows ibox251) tree252
attribute [irreducible] tree251
private theorem sign_251 : ((computed denominator ibox251).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_251 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox251) tree251 = true := by
  simp only [tree251,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox251,?_,accepted_252 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox251)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox251).gradient 1).hi) denominator_positive).1 sign_251
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
private noncomputable def tree249 : TapeTree := .face 1 false (candidateRows ibox249) tree250
attribute [irreducible] tree249
private theorem sign_249 : ((computed denominator ibox249).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_249 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox249) tree249 = true := by
  simp only [tree249,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox249,?_,accepted_250 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox249)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox249).gradient 1).hi) denominator_positive).1 sign_249
private noncomputable def tree248 : TapeTree := .split 0 (((246643199311766300838018739848980903185770086400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree249 tree251
attribute [irreducible] tree248
private theorem accepted_248 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox248) tree248 = true := by
  simp only [tree248,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox248 0 (246643199311766300838018739848980903185770086400000000000000 : Int) false,decode_split denominator ibox248 0 (246643199311766300838018739848980903185770086400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_249 h,accepted_251 h⟩
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
private noncomputable def tree246 : TapeTree := .centered (candidateRows ibox246) (candidateRows (FixedTape.midBox ibox246))
attribute [irreducible] tree246
private theorem sign_246 : 2*denominator*(computed denominator (FixedTape.midBox ibox246)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox246).gradient k).lo.natAbs ((computed denominator ibox246).gradient k).hi.natAbs : Int)*((ibox246 k).hi-(ibox246 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox246
    (computed denominator ibox246) (computed denominator (FixedTape.midBox ibox246))
    (by decide +kernel)
private theorem midpoint_even_246 : ∀ k, 2 ∣ (ibox246 k).lo+(ibox246 k).hi := by decide +kernel
private theorem accepted_246 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox246) tree246 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox246 midpoint_even_246
  simp only [tree246,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox246,candidate_valid h (FixedTape.midBox ibox246),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox246 212 (FixedTape.rowsAux denominator ibox246 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox246) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_246
private noncomputable def tree245 : TapeTree := .split 3 (((119534775328106041071017374202679018620190720000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree246 tree247
attribute [irreducible] tree245
private theorem accepted_245 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox245) tree245 = true := by
  simp only [tree245,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox245 3 (119534775328106041071017374202679018620190720000000000000000000 : Int) false,decode_split denominator ibox245 3 (119534775328106041071017374202679018620190720000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_246 h,accepted_247 h⟩
private noncomputable def tree244 : TapeTree := .face 1 false (candidateRows ibox244) tree245
attribute [irreducible] tree244
private theorem sign_244 : ((computed denominator ibox244).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_244 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox244) tree244 = true := by
  simp only [tree244,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox244,?_,accepted_245 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox244)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox244).gradient 1).hi) denominator_positive).1 sign_244
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
private noncomputable def tree242 : TapeTree := .centered (candidateRows ibox242) (candidateRows (FixedTape.midBox ibox242))
attribute [irreducible] tree242
private theorem sign_242 : 2*denominator*(computed denominator (FixedTape.midBox ibox242)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox242).gradient k).lo.natAbs ((computed denominator ibox242).gradient k).hi.natAbs : Int)*((ibox242 k).hi-(ibox242 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox242
    (computed denominator ibox242) (computed denominator (FixedTape.midBox ibox242))
    (by decide +kernel)
private theorem midpoint_even_242 : ∀ k, 2 ∣ (ibox242 k).lo+(ibox242 k).hi := by decide +kernel
private theorem accepted_242 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox242) tree242 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox242 midpoint_even_242
  simp only [tree242,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox242,candidate_valid h (FixedTape.midBox ibox242),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox242 212 (FixedTape.rowsAux denominator ibox242 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox242) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_242
private noncomputable def tree241 : TapeTree := .split 3 (((119534775328106041071017374202679018620190720000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree242 tree243
attribute [irreducible] tree241
private theorem accepted_241 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox241) tree241 = true := by
  simp only [tree241,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox241 3 (119534775328106041071017374202679018620190720000000000000000000 : Int) false,decode_split denominator ibox241 3 (119534775328106041071017374202679018620190720000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_242 h,accepted_243 h⟩
private noncomputable def tree240 : TapeTree := .face 1 false (candidateRows ibox240) tree241
attribute [irreducible] tree240
private theorem sign_240 : ((computed denominator ibox240).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_240 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox240) tree240 = true := by
  simp only [tree240,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox240,?_,accepted_241 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox240)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox240).gradient 1).hi) denominator_positive).1 sign_240
private noncomputable def tree239 : TapeTree := .split 0 (((246643199311766300838018739848980903185770086400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree240 tree244
attribute [irreducible] tree239
private theorem accepted_239 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox239) tree239 = true := by
  simp only [tree239,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox239 0 (246643199311766300838018739848980903185770086400000000000000 : Int) false,decode_split denominator ibox239 0 (246643199311766300838018739848980903185770086400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_240 h,accepted_244 h⟩
private noncomputable def tree238 : TapeTree := .centered (candidateRows ibox238) (candidateRows (FixedTape.midBox ibox238))
attribute [irreducible] tree238
private theorem sign_238 : 2*denominator*(computed denominator (FixedTape.midBox ibox238)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox238).gradient k).lo.natAbs ((computed denominator ibox238).gradient k).hi.natAbs : Int)*((ibox238 k).hi-(ibox238 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox238
    (computed denominator ibox238) (computed denominator (FixedTape.midBox ibox238))
    (by decide +kernel)
private theorem midpoint_even_238 : ∀ k, 2 ∣ (ibox238 k).lo+(ibox238 k).hi := by decide +kernel
private theorem accepted_238 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox238) tree238 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox238 midpoint_even_238
  simp only [tree238,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox238,candidate_valid h (FixedTape.midBox ibox238),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox238 212 (FixedTape.rowsAux denominator ibox238 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox238) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_238
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
private noncomputable def tree236 : TapeTree := .split 0 (((263459781083023094076974563020502328402981683200000000000000 : Int) : ℚ)/(denominator : ℚ)) tree237 tree238
attribute [irreducible] tree236
private theorem accepted_236 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox236) tree236 = true := by
  simp only [tree236,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox236 0 (263459781083023094076974563020502328402981683200000000000000 : Int) false,decode_split denominator ibox236 0 (263459781083023094076974563020502328402981683200000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_237 h,accepted_238 h⟩
private noncomputable def tree235 : TapeTree := .centered (candidateRows ibox235) (candidateRows (FixedTape.midBox ibox235))
attribute [irreducible] tree235
private theorem sign_235 : 2*denominator*(computed denominator (FixedTape.midBox ibox235)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox235).gradient k).lo.natAbs ((computed denominator ibox235).gradient k).hi.natAbs : Int)*((ibox235 k).hi-(ibox235 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox235
    (computed denominator ibox235) (computed denominator (FixedTape.midBox ibox235))
    (by decide +kernel)
private theorem midpoint_even_235 : ∀ k, 2 ∣ (ibox235 k).lo+(ibox235 k).hi := by decide +kernel
private theorem accepted_235 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox235) tree235 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox235 midpoint_even_235
  simp only [tree235,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox235,candidate_valid h (FixedTape.midBox ibox235),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox235 212 (FixedTape.rowsAux denominator ibox235 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox235) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_235
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
private noncomputable def tree233 : TapeTree := .split 0 (((252248726568851898584337347572821378258173952000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree234 tree235
attribute [irreducible] tree233
private theorem accepted_233 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox233) tree233 = true := by
  simp only [tree233,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox233 0 (252248726568851898584337347572821378258173952000000000000000 : Int) false,decode_split denominator ibox233 0 (252248726568851898584337347572821378258173952000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_234 h,accepted_235 h⟩
private noncomputable def tree232 : TapeTree := .split 0 (((257854253825937496330655955296661853330577817600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree233 tree236
attribute [irreducible] tree232
private theorem accepted_232 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox232) tree232 = true := by
  simp only [tree232,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox232 0 (257854253825937496330655955296661853330577817600000000000000 : Int) false,decode_split denominator ibox232 0 (257854253825937496330655955296661853330577817600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_233 h,accepted_236 h⟩
private noncomputable def tree231 : TapeTree := .centered (candidateRows ibox231) (candidateRows (FixedTape.midBox ibox231))
attribute [irreducible] tree231
private theorem sign_231 : 2*denominator*(computed denominator (FixedTape.midBox ibox231)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox231).gradient k).lo.natAbs ((computed denominator ibox231).gradient k).hi.natAbs : Int)*((ibox231 k).hi-(ibox231 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox231
    (computed denominator ibox231) (computed denominator (FixedTape.midBox ibox231))
    (by decide +kernel)
private theorem midpoint_even_231 : ∀ k, 2 ∣ (ibox231 k).lo+(ibox231 k).hi := by decide +kernel
private theorem accepted_231 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox231) tree231 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox231 midpoint_even_231
  simp only [tree231,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox231,candidate_valid h (FixedTape.midBox ibox231),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox231 212 (FixedTape.rowsAux denominator ibox231 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox231) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_231
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
private noncomputable def tree229 : TapeTree := .split 0 (((263459781083023094076974563020502328402981683200000000000000 : Int) : ℚ)/(denominator : ℚ)) tree230 tree231
attribute [irreducible] tree229
private theorem accepted_229 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox229) tree229 = true := by
  simp only [tree229,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox229 0 (263459781083023094076974563020502328402981683200000000000000 : Int) false,decode_split denominator ibox229 0 (263459781083023094076974563020502328402981683200000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_230 h,accepted_231 h⟩
private noncomputable def tree228 : TapeTree := .centered (candidateRows ibox228) (candidateRows (FixedTape.midBox ibox228))
attribute [irreducible] tree228
private theorem sign_228 : 2*denominator*(computed denominator (FixedTape.midBox ibox228)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox228).gradient k).lo.natAbs ((computed denominator ibox228).gradient k).hi.natAbs : Int)*((ibox228 k).hi-(ibox228 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox228
    (computed denominator ibox228) (computed denominator (FixedTape.midBox ibox228))
    (by decide +kernel)
private theorem midpoint_even_228 : ∀ k, 2 ∣ (ibox228 k).lo+(ibox228 k).hi := by decide +kernel
private theorem accepted_228 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox228) tree228 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox228 midpoint_even_228
  simp only [tree228,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox228,candidate_valid h (FixedTape.midBox ibox228),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox228 212 (FixedTape.rowsAux denominator ibox228 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox228) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_228
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
private noncomputable def tree226 : TapeTree := .split 0 (((252248726568851898584337347572821378258173952000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree227 tree228
attribute [irreducible] tree226
private theorem accepted_226 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox226) tree226 = true := by
  simp only [tree226,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox226 0 (252248726568851898584337347572821378258173952000000000000000 : Int) false,decode_split denominator ibox226 0 (252248726568851898584337347572821378258173952000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_227 h,accepted_228 h⟩
private noncomputable def tree225 : TapeTree := .split 0 (((257854253825937496330655955296661853330577817600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree226 tree229
attribute [irreducible] tree225
private theorem accepted_225 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox225) tree225 = true := by
  simp only [tree225,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox225 0 (257854253825937496330655955296661853330577817600000000000000 : Int) false,decode_split denominator ibox225 0 (257854253825937496330655955296661853330577817600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_226 h,accepted_229 h⟩
private noncomputable def tree224 : TapeTree := .split 3 (((209185856824185571874280404854688282585333760000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree225 tree232
attribute [irreducible] tree224
private theorem accepted_224 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox224) tree224 = true := by
  simp only [tree224,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox224 3 (209185856824185571874280404854688282585333760000000000000000000 : Int) false,decode_split denominator ibox224 3 (209185856824185571874280404854688282585333760000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_225 h,accepted_232 h⟩
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
private noncomputable def tree221 : TapeTree := .split 0 (((263459781083023094076974563020502328402981683200000000000000 : Int) : ℚ)/(denominator : ℚ)) tree222 tree223
attribute [irreducible] tree221
private theorem accepted_221 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox221) tree221 = true := by
  simp only [tree221,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox221 0 (263459781083023094076974563020502328402981683200000000000000 : Int) false,decode_split denominator ibox221 0 (263459781083023094076974563020502328402981683200000000000000 : Int) true]
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
private noncomputable def tree218 : TapeTree := .split 0 (((263459781083023094076974563020502328402981683200000000000000 : Int) : ℚ)/(denominator : ℚ)) tree219 tree220
attribute [irreducible] tree218
private theorem accepted_218 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox218) tree218 = true := by
  simp only [tree218,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox218 0 (263459781083023094076974563020502328402981683200000000000000 : Int) false,decode_split denominator ibox218 0 (263459781083023094076974563020502328402981683200000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_219 h,accepted_220 h⟩
private noncomputable def tree217 : TapeTree := .split 3 (((149418469160132551338771717753348773275238400000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree218 tree221
attribute [irreducible] tree217
private theorem accepted_217 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox217) tree217 = true := by
  simp only [tree217,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox217 3 (149418469160132551338771717753348773275238400000000000000000000 : Int) false,decode_split denominator ibox217 3 (149418469160132551338771717753348773275238400000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_218 h,accepted_221 h⟩
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
private noncomputable def tree215 : TapeTree := .centered (candidateRows ibox215) (candidateRows (FixedTape.midBox ibox215))
attribute [irreducible] tree215
private theorem sign_215 : 2*denominator*(computed denominator (FixedTape.midBox ibox215)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox215).gradient k).lo.natAbs ((computed denominator ibox215).gradient k).hi.natAbs : Int)*((ibox215 k).hi-(ibox215 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox215
    (computed denominator ibox215) (computed denominator (FixedTape.midBox ibox215))
    (by decide +kernel)
private theorem midpoint_even_215 : ∀ k, 2 ∣ (ibox215 k).lo+(ibox215 k).hi := by decide +kernel
private theorem accepted_215 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox215) tree215 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox215 midpoint_even_215
  simp only [tree215,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox215,candidate_valid h (FixedTape.midBox ibox215),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox215 212 (FixedTape.rowsAux denominator ibox215 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox215) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_215
private noncomputable def tree214 : TapeTree := .split 0 (((252248726568851898584337347572821378258173952000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree215 tree216
attribute [irreducible] tree214
private theorem accepted_214 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox214) tree214 = true := by
  simp only [tree214,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox214 0 (252248726568851898584337347572821378258173952000000000000000 : Int) false,decode_split denominator ibox214 0 (252248726568851898584337347572821378258173952000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_215 h,accepted_216 h⟩
private noncomputable def tree213 : TapeTree := .centered (candidateRows ibox213) (candidateRows (FixedTape.midBox ibox213))
attribute [irreducible] tree213
private theorem sign_213 : 2*denominator*(computed denominator (FixedTape.midBox ibox213)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox213).gradient k).lo.natAbs ((computed denominator ibox213).gradient k).hi.natAbs : Int)*((ibox213 k).hi-(ibox213 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox213
    (computed denominator ibox213) (computed denominator (FixedTape.midBox ibox213))
    (by decide +kernel)
private theorem midpoint_even_213 : ∀ k, 2 ∣ (ibox213 k).lo+(ibox213 k).hi := by decide +kernel
private theorem accepted_213 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox213) tree213 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox213 midpoint_even_213
  simp only [tree213,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox213,candidate_valid h (FixedTape.midBox ibox213),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox213 212 (FixedTape.rowsAux denominator ibox213 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox213) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_213
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
private noncomputable def tree210 : TapeTree := .split 3 (((134476622244119296204894545978013895947714560000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree211 tree212
attribute [irreducible] tree210
private theorem accepted_210 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox210) tree210 = true := by
  simp only [tree210,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox210 3 (134476622244119296204894545978013895947714560000000000000000000 : Int) false,decode_split denominator ibox210 3 (134476622244119296204894545978013895947714560000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_211 h,accepted_212 h⟩
private noncomputable def tree209 : TapeTree := .split 0 (((252248726568851898584337347572821378258173952000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree210 tree213
attribute [irreducible] tree209
private theorem accepted_209 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox209) tree209 = true := by
  simp only [tree209,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox209 0 (252248726568851898584337347572821378258173952000000000000000 : Int) false,decode_split denominator ibox209 0 (252248726568851898584337347572821378258173952000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_210 h,accepted_213 h⟩
private noncomputable def tree208 : TapeTree := .split 3 (((149418469160132551338771717753348773275238400000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree209 tree214
attribute [irreducible] tree208
private theorem accepted_208 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox208) tree208 = true := by
  simp only [tree208,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox208 3 (149418469160132551338771717753348773275238400000000000000000000 : Int) false,decode_split denominator ibox208 3 (149418469160132551338771717753348773275238400000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_209 h,accepted_214 h⟩
private noncomputable def tree207 : TapeTree := .split 0 (((257854253825937496330655955296661853330577817600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree208 tree217
attribute [irreducible] tree207
private theorem accepted_207 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox207) tree207 = true := by
  simp only [tree207,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox207 0 (257854253825937496330655955296661853330577817600000000000000 : Int) false,decode_split denominator ibox207 0 (257854253825937496330655955296661853330577817600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_208 h,accepted_217 h⟩
private noncomputable def tree206 : TapeTree := .split 3 (((179302162992159061606526061304018527930286080000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree207 tree224
attribute [irreducible] tree206
private theorem accepted_206 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox206) tree206 = true := by
  simp only [tree206,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox206 3 (179302162992159061606526061304018527930286080000000000000000000 : Int) false,decode_split denominator ibox206 3 (179302162992159061606526061304018527930286080000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_207 h,accepted_224 h⟩
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
private noncomputable def tree203 : TapeTree := .split 0 (((263459781083023094076974563020502328402981683200000000000000 : Int) : ℚ)/(denominator : ℚ)) tree204 tree205
attribute [irreducible] tree203
private theorem accepted_203 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox203) tree203 = true := by
  simp only [tree203,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox203 0 (263459781083023094076974563020502328402981683200000000000000 : Int) false,decode_split denominator ibox203 0 (263459781083023094076974563020502328402981683200000000000000 : Int) true]
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
private noncomputable def tree200 : TapeTree := .split 0 (((263459781083023094076974563020502328402981683200000000000000 : Int) : ℚ)/(denominator : ℚ)) tree201 tree202
attribute [irreducible] tree200
private theorem accepted_200 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox200) tree200 = true := by
  simp only [tree200,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox200 0 (263459781083023094076974563020502328402981683200000000000000 : Int) false,decode_split denominator ibox200 0 (263459781083023094076974563020502328402981683200000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_201 h,accepted_202 h⟩
private noncomputable def tree199 : TapeTree := .split 3 (((89651081496079530803263030652009263965143040000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree200 tree203
attribute [irreducible] tree199
private theorem accepted_199 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox199) tree199 = true := by
  simp only [tree199,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox199 3 (89651081496079530803263030652009263965143040000000000000000000 : Int) false,decode_split denominator ibox199 3 (89651081496079530803263030652009263965143040000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_200 h,accepted_203 h⟩
private noncomputable def tree198 : TapeTree := .centered (candidateRows ibox198) (candidateRows (FixedTape.midBox ibox198))
attribute [irreducible] tree198
private theorem sign_198 : 2*denominator*(computed denominator (FixedTape.midBox ibox198)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox198).gradient k).lo.natAbs ((computed denominator ibox198).gradient k).hi.natAbs : Int)*((ibox198 k).hi-(ibox198 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox198
    (computed denominator ibox198) (computed denominator (FixedTape.midBox ibox198))
    (by decide +kernel)
private theorem midpoint_even_198 : ∀ k, 2 ∣ (ibox198 k).lo+(ibox198 k).hi := by decide +kernel
private theorem accepted_198 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox198) tree198 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox198 midpoint_even_198
  simp only [tree198,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox198,candidate_valid h (FixedTape.midBox ibox198),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox198 212 (FixedTape.rowsAux denominator ibox198 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox198) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_198
private noncomputable def tree197 : TapeTree := .centered (candidateRows ibox197) (candidateRows (FixedTape.midBox ibox197))
attribute [irreducible] tree197
private theorem sign_197 : 2*denominator*(computed denominator (FixedTape.midBox ibox197)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox197).gradient k).lo.natAbs ((computed denominator ibox197).gradient k).hi.natAbs : Int)*((ibox197 k).hi-(ibox197 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox197
    (computed denominator ibox197) (computed denominator (FixedTape.midBox ibox197))
    (by decide +kernel)
private theorem midpoint_even_197 : ∀ k, 2 ∣ (ibox197 k).lo+(ibox197 k).hi := by decide +kernel
private theorem accepted_197 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox197) tree197 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox197 midpoint_even_197
  simp only [tree197,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox197,candidate_valid h (FixedTape.midBox ibox197),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox197 212 (FixedTape.rowsAux denominator ibox197 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox197) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_197
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
private noncomputable def tree195 : TapeTree := .split 3 (((104592928412092785937140202427344141292666880000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree196 tree197
attribute [irreducible] tree195
private theorem accepted_195 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox195) tree195 = true := by
  simp only [tree195,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox195 3 (104592928412092785937140202427344141292666880000000000000000000 : Int) false,decode_split denominator ibox195 3 (104592928412092785937140202427344141292666880000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_196 h,accepted_197 h⟩
private noncomputable def tree194 : TapeTree := .split 0 (((252248726568851898584337347572821378258173952000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree195 tree198
attribute [irreducible] tree194
private theorem accepted_194 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox194) tree194 = true := by
  simp only [tree194,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox194 0 (252248726568851898584337347572821378258173952000000000000000 : Int) false,decode_split denominator ibox194 0 (252248726568851898584337347572821378258173952000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_195 h,accepted_198 h⟩
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
private noncomputable def tree191 : TapeTree := .centered (candidateRows ibox191) (candidateRows (FixedTape.midBox ibox191))
attribute [irreducible] tree191
private theorem sign_191 : 2*denominator*(computed denominator (FixedTape.midBox ibox191)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox191).gradient k).lo.natAbs ((computed denominator ibox191).gradient k).hi.natAbs : Int)*((ibox191 k).hi-(ibox191 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox191
    (computed denominator ibox191) (computed denominator (FixedTape.midBox ibox191))
    (by decide +kernel)
private theorem midpoint_even_191 : ∀ k, 2 ∣ (ibox191 k).lo+(ibox191 k).hi := by decide +kernel
private theorem accepted_191 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox191) tree191 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox191 midpoint_even_191
  simp only [tree191,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox191,candidate_valid h (FixedTape.midBox ibox191),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox191 212 (FixedTape.rowsAux denominator ibox191 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox191) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_191
private noncomputable def tree190 : TapeTree := .split 3 (((74709234580066275669385858876674386637619200000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree191 tree192
attribute [irreducible] tree190
private theorem accepted_190 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox190) tree190 = true := by
  simp only [tree190,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox190 3 (74709234580066275669385858876674386637619200000000000000000000 : Int) false,decode_split denominator ibox190 3 (74709234580066275669385858876674386637619200000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_191 h,accepted_192 h⟩
private noncomputable def tree189 : TapeTree := .split 0 (((252248726568851898584337347572821378258173952000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree190 tree193
attribute [irreducible] tree189
private theorem accepted_189 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox189) tree189 = true := by
  simp only [tree189,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox189 0 (252248726568851898584337347572821378258173952000000000000000 : Int) false,decode_split denominator ibox189 0 (252248726568851898584337347572821378258173952000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_190 h,accepted_193 h⟩
private noncomputable def tree188 : TapeTree := .split 3 (((89651081496079530803263030652009263965143040000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree189 tree194
attribute [irreducible] tree188
private theorem accepted_188 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox188) tree188 = true := by
  simp only [tree188,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox188 3 (89651081496079530803263030652009263965143040000000000000000000 : Int) false,decode_split denominator ibox188 3 (89651081496079530803263030652009263965143040000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_189 h,accepted_194 h⟩
private noncomputable def tree187 : TapeTree := .split 0 (((257854253825937496330655955296661853330577817600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree188 tree199
attribute [irreducible] tree187
private theorem accepted_187 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox187) tree187 = true := by
  simp only [tree187,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox187 0 (257854253825937496330655955296661853330577817600000000000000 : Int) false,decode_split denominator ibox187 0 (257854253825937496330655955296661853330577817600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_188 h,accepted_199 h⟩
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
private noncomputable def tree184 : TapeTree := .split 0 (((263459781083023094076974563020502328402981683200000000000000 : Int) : ℚ)/(denominator : ℚ)) tree185 tree186
attribute [irreducible] tree184
private theorem accepted_184 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox184) tree184 = true := by
  simp only [tree184,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox184 0 (263459781083023094076974563020502328402981683200000000000000 : Int) false,decode_split denominator ibox184 0 (263459781083023094076974563020502328402981683200000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_185 h,accepted_186 h⟩
private noncomputable def tree183 : TapeTree := .centered (candidateRows ibox183) (candidateRows (FixedTape.midBox ibox183))
attribute [irreducible] tree183
private theorem sign_183 : 2*denominator*(computed denominator (FixedTape.midBox ibox183)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox183).gradient k).lo.natAbs ((computed denominator ibox183).gradient k).hi.natAbs : Int)*((ibox183 k).hi-(ibox183 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox183
    (computed denominator ibox183) (computed denominator (FixedTape.midBox ibox183))
    (by decide +kernel)
private theorem midpoint_even_183 : ∀ k, 2 ∣ (ibox183 k).lo+(ibox183 k).hi := by decide +kernel
private theorem accepted_183 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox183) tree183 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox183 midpoint_even_183
  simp only [tree183,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox183,candidate_valid h (FixedTape.midBox ibox183),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox183 212 (FixedTape.rowsAux denominator ibox183 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox183) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_183
private noncomputable def tree182 : TapeTree := .centered (candidateRows ibox182) (candidateRows (FixedTape.midBox ibox182))
attribute [irreducible] tree182
private theorem sign_182 : 2*denominator*(computed denominator (FixedTape.midBox ibox182)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox182).gradient k).lo.natAbs ((computed denominator ibox182).gradient k).hi.natAbs : Int)*((ibox182 k).hi-(ibox182 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox182
    (computed denominator ibox182) (computed denominator (FixedTape.midBox ibox182))
    (by decide +kernel)
private theorem midpoint_even_182 : ∀ k, 2 ∣ (ibox182 k).lo+(ibox182 k).hi := by decide +kernel
private theorem accepted_182 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox182) tree182 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox182 midpoint_even_182
  simp only [tree182,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox182,candidate_valid h (FixedTape.midBox ibox182),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox182 212 (FixedTape.rowsAux denominator ibox182 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox182) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_182
private noncomputable def tree181 : TapeTree := .split 0 (((263459781083023094076974563020502328402981683200000000000000 : Int) : ℚ)/(denominator : ℚ)) tree182 tree183
attribute [irreducible] tree181
private theorem accepted_181 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox181) tree181 = true := by
  simp only [tree181,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox181 0 (263459781083023094076974563020502328402981683200000000000000 : Int) false,decode_split denominator ibox181 0 (263459781083023094076974563020502328402981683200000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_182 h,accepted_183 h⟩
private noncomputable def tree180 : TapeTree := .split 3 (((29883693832026510267754343550669754655047680000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree181 tree184
attribute [irreducible] tree180
private theorem accepted_180 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox180) tree180 = true := by
  simp only [tree180,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox180 3 (29883693832026510267754343550669754655047680000000000000000000 : Int) false,decode_split denominator ibox180 3 (29883693832026510267754343550669754655047680000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_181 h,accepted_184 h⟩
private noncomputable def tree179 : TapeTree := .centered (candidateRows ibox179) (candidateRows (FixedTape.midBox ibox179))
attribute [irreducible] tree179
private theorem sign_179 : 2*denominator*(computed denominator (FixedTape.midBox ibox179)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox179).gradient k).lo.natAbs ((computed denominator ibox179).gradient k).hi.natAbs : Int)*((ibox179 k).hi-(ibox179 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox179
    (computed denominator ibox179) (computed denominator (FixedTape.midBox ibox179))
    (by decide +kernel)
private theorem midpoint_even_179 : ∀ k, 2 ∣ (ibox179 k).lo+(ibox179 k).hi := by decide +kernel
private theorem accepted_179 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox179) tree179 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox179 midpoint_even_179
  simp only [tree179,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox179,candidate_valid h (FixedTape.midBox ibox179),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox179 212 (FixedTape.rowsAux denominator ibox179 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox179) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_179
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
private noncomputable def tree176 : TapeTree := .split 0 (((249445962940309099711178043710901140721972019200000000000000 : Int) : ℚ)/(denominator : ℚ)) tree177 tree178
attribute [irreducible] tree176
private theorem accepted_176 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox176) tree176 = true := by
  simp only [tree176,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox176 0 (249445962940309099711178043710901140721972019200000000000000 : Int) false,decode_split denominator ibox176 0 (249445962940309099711178043710901140721972019200000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_177 h,accepted_178 h⟩
private noncomputable def tree175 : TapeTree := .split 0 (((252248726568851898584337347572821378258173952000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree176 tree179
attribute [irreducible] tree175
private theorem accepted_175 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox175) tree175 = true := by
  simp only [tree175,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox175 0 (252248726568851898584337347572821378258173952000000000000000 : Int) false,decode_split denominator ibox175 0 (252248726568851898584337347572821378258173952000000000000000 : Int) true]
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
private noncomputable def tree172 : TapeTree := .split 0 (((255051490197394697457496651434741615794375884800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree173 tree174
attribute [irreducible] tree172
private theorem accepted_172 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox172) tree172 = true := by
  simp only [tree172,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox172 0 (255051490197394697457496651434741615794375884800000000000000 : Int) false,decode_split denominator ibox172 0 (255051490197394697457496651434741615794375884800000000000000 : Int) true]
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
private noncomputable def tree169 : TapeTree := .split 0 (((249445962940309099711178043710901140721972019200000000000000 : Int) : ℚ)/(denominator : ℚ)) tree170 tree171
attribute [irreducible] tree169
private theorem accepted_169 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox169) tree169 = true := by
  simp only [tree169,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox169 0 (249445962940309099711178043710901140721972019200000000000000 : Int) false,decode_split denominator ibox169 0 (249445962940309099711178043710901140721972019200000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_170 h,accepted_171 h⟩
private noncomputable def tree168 : TapeTree := .split 0 (((252248726568851898584337347572821378258173952000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree169 tree172
attribute [irreducible] tree168
private theorem accepted_168 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox168) tree168 = true := by
  simp only [tree168,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox168 0 (252248726568851898584337347572821378258173952000000000000000 : Int) false,decode_split denominator ibox168 0 (252248726568851898584337347572821378258173952000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_169 h,accepted_172 h⟩
private noncomputable def tree167 : TapeTree := .split 3 (((29883693832026510267754343550669754655047680000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree168 tree175
attribute [irreducible] tree167
private theorem accepted_167 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox167) tree167 = true := by
  simp only [tree167,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox167 3 (29883693832026510267754343550669754655047680000000000000000000 : Int) false,decode_split denominator ibox167 3 (29883693832026510267754343550669754655047680000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_168 h,accepted_175 h⟩
private noncomputable def tree166 : TapeTree := .split 0 (((257854253825937496330655955296661853330577817600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree167 tree180
attribute [irreducible] tree166
private theorem accepted_166 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox166) tree166 = true := by
  simp only [tree166,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox166 0 (257854253825937496330655955296661853330577817600000000000000 : Int) false,decode_split denominator ibox166 0 (257854253825937496330655955296661853330577817600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_167 h,accepted_180 h⟩
private noncomputable def tree165 : TapeTree := .split 3 (((59767387664053020535508687101339509310095360000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree166 tree187
attribute [irreducible] tree165
private theorem accepted_165 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox165) tree165 = true := by
  simp only [tree165,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox165 3 (59767387664053020535508687101339509310095360000000000000000000 : Int) false,decode_split denominator ibox165 3 (59767387664053020535508687101339509310095360000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_166 h,accepted_187 h⟩
private noncomputable def tree164 : TapeTree := .split 3 (((119534775328106041071017374202679018620190720000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree165 tree206
attribute [irreducible] tree164
private theorem accepted_164 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox164) tree164 = true := by
  simp only [tree164,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox164 3 (119534775328106041071017374202679018620190720000000000000000000 : Int) false,decode_split denominator ibox164 3 (119534775328106041071017374202679018620190720000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_165 h,accepted_206 h⟩
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
private noncomputable def tree160 : TapeTree := .split 3 (((224127703740198827008157576630023159912857600000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree161 tree162
attribute [irreducible] tree160
private theorem accepted_160 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox160) tree160 = true := by
  simp only [tree160,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox160 3 (224127703740198827008157576630023159912857600000000000000000000 : Int) false,decode_split denominator ibox160 3 (224127703740198827008157576630023159912857600000000000000000000 : Int) true]
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
private noncomputable def tree157 : TapeTree := .split 3 (((224127703740198827008157576630023159912857600000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree158 tree159
attribute [irreducible] tree157
private theorem accepted_157 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox157) tree157 = true := by
  simp only [tree157,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox157 3 (224127703740198827008157576630023159912857600000000000000000000 : Int) false,decode_split denominator ibox157 3 (224127703740198827008157576630023159912857600000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_158 h,accepted_159 h⟩
private noncomputable def tree156 : TapeTree := .split 0 (((241037672054680703091700132125140428113366220800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree157 tree160
attribute [irreducible] tree156
private theorem accepted_156 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox156) tree156 = true := by
  simp only [tree156,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox156 0 (241037672054680703091700132125140428113366220800000000000000 : Int) false,decode_split denominator ibox156 0 (241037672054680703091700132125140428113366220800000000000000 : Int) true]
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
private noncomputable def tree153 : TapeTree := .split 3 (((224127703740198827008157576630023159912857600000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree154 tree155
attribute [irreducible] tree153
private theorem accepted_153 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox153) tree153 = true := by
  simp only [tree153,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox153 3 (224127703740198827008157576630023159912857600000000000000000000 : Int) false,decode_split denominator ibox153 3 (224127703740198827008157576630023159912857600000000000000000000 : Int) true]
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
private noncomputable def tree150 : TapeTree := .split 3 (((224127703740198827008157576630023159912857600000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree151 tree152
attribute [irreducible] tree150
private theorem accepted_150 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox150) tree150 = true := by
  simp only [tree150,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox150 3 (224127703740198827008157576630023159912857600000000000000000000 : Int) false,decode_split denominator ibox150 3 (224127703740198827008157576630023159912857600000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_151 h,accepted_152 h⟩
private noncomputable def tree149 : TapeTree := .split 0 (((229826617540509507599062916677459477968558489600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree150 tree153
attribute [irreducible] tree149
private theorem accepted_149 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox149) tree149 = true := by
  simp only [tree149,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox149 0 (229826617540509507599062916677459477968558489600000000000000 : Int) false,decode_split denominator ibox149 0 (229826617540509507599062916677459477968558489600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_150 h,accepted_153 h⟩
private noncomputable def tree148 : TapeTree := .split 0 (((235432144797595105345381524401299953040962355200000000000000 : Int) : ℚ)/(denominator : ℚ)) tree149 tree156
attribute [irreducible] tree148
private theorem accepted_148 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox148) tree148 = true := by
  simp only [tree148,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox148 0 (235432144797595105345381524401299953040962355200000000000000 : Int) false,decode_split denominator ibox148 0 (235432144797595105345381524401299953040962355200000000000000 : Int) true]
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
private noncomputable def tree145 : TapeTree := .split 3 (((194244009908172316740403233079353405257809920000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree146 tree147
attribute [irreducible] tree145
private theorem accepted_145 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox145) tree145 = true := by
  simp only [tree145,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox145 3 (194244009908172316740403233079353405257809920000000000000000000 : Int) false,decode_split denominator ibox145 3 (194244009908172316740403233079353405257809920000000000000000000 : Int) true]
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
private noncomputable def tree142 : TapeTree := .split 3 (((194244009908172316740403233079353405257809920000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree143 tree144
attribute [irreducible] tree142
private theorem accepted_142 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox142) tree142 = true := by
  simp only [tree142,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox142 3 (194244009908172316740403233079353405257809920000000000000000000 : Int) false,decode_split denominator ibox142 3 (194244009908172316740403233079353405257809920000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_143 h,accepted_144 h⟩
private noncomputable def tree141 : TapeTree := .split 0 (((241037672054680703091700132125140428113366220800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree142 tree145
attribute [irreducible] tree141
private theorem accepted_141 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox141) tree141 = true := by
  simp only [tree141,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox141 0 (241037672054680703091700132125140428113366220800000000000000 : Int) false,decode_split denominator ibox141 0 (241037672054680703091700132125140428113366220800000000000000 : Int) true]
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
private noncomputable def tree138 : TapeTree := .split 3 (((194244009908172316740403233079353405257809920000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree139 tree140
attribute [irreducible] tree138
private theorem accepted_138 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox138) tree138 = true := by
  simp only [tree138,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox138 3 (194244009908172316740403233079353405257809920000000000000000000 : Int) false,decode_split denominator ibox138 3 (194244009908172316740403233079353405257809920000000000000000000 : Int) true]
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
private noncomputable def tree135 : TapeTree := .split 3 (((194244009908172316740403233079353405257809920000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree136 tree137
attribute [irreducible] tree135
private theorem accepted_135 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox135) tree135 = true := by
  simp only [tree135,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox135 3 (194244009908172316740403233079353405257809920000000000000000000 : Int) false,decode_split denominator ibox135 3 (194244009908172316740403233079353405257809920000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_136 h,accepted_137 h⟩
private noncomputable def tree134 : TapeTree := .split 0 (((229826617540509507599062916677459477968558489600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree135 tree138
attribute [irreducible] tree134
private theorem accepted_134 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox134) tree134 = true := by
  simp only [tree134,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox134 0 (229826617540509507599062916677459477968558489600000000000000 : Int) false,decode_split denominator ibox134 0 (229826617540509507599062916677459477968558489600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_135 h,accepted_138 h⟩
private noncomputable def tree133 : TapeTree := .split 0 (((235432144797595105345381524401299953040962355200000000000000 : Int) : ℚ)/(denominator : ℚ)) tree134 tree141
attribute [irreducible] tree133
private theorem accepted_133 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox133) tree133 = true := by
  simp only [tree133,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox133 0 (235432144797595105345381524401299953040962355200000000000000 : Int) false,decode_split denominator ibox133 0 (235432144797595105345381524401299953040962355200000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_134 h,accepted_141 h⟩
private noncomputable def tree132 : TapeTree := .split 3 (((209185856824185571874280404854688282585333760000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree133 tree148
attribute [irreducible] tree132
private theorem accepted_132 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox132) tree132 = true := by
  simp only [tree132,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox132 3 (209185856824185571874280404854688282585333760000000000000000000 : Int) false,decode_split denominator ibox132 3 (209185856824185571874280404854688282585333760000000000000000000 : Int) true]
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
private noncomputable def tree129 : TapeTree := .split 3 (((164360316076145806472648889528683650602762240000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree130 tree131
attribute [irreducible] tree129
private theorem accepted_129 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox129) tree129 = true := by
  simp only [tree129,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox129 3 (164360316076145806472648889528683650602762240000000000000000000 : Int) false,decode_split denominator ibox129 3 (164360316076145806472648889528683650602762240000000000000000000 : Int) true]
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
private noncomputable def tree126 : TapeTree := .split 3 (((164360316076145806472648889528683650602762240000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree127 tree128
attribute [irreducible] tree126
private theorem accepted_126 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox126) tree126 = true := by
  simp only [tree126,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox126 3 (164360316076145806472648889528683650602762240000000000000000000 : Int) false,decode_split denominator ibox126 3 (164360316076145806472648889528683650602762240000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_127 h,accepted_128 h⟩
private noncomputable def tree125 : TapeTree := .split 0 (((241037672054680703091700132125140428113366220800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree126 tree129
attribute [irreducible] tree125
private theorem accepted_125 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox125) tree125 = true := by
  simp only [tree125,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox125 0 (241037672054680703091700132125140428113366220800000000000000 : Int) false,decode_split denominator ibox125 0 (241037672054680703091700132125140428113366220800000000000000 : Int) true]
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
private noncomputable def tree122 : TapeTree := .split 3 (((134476622244119296204894545978013895947714560000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree123 tree124
attribute [irreducible] tree122
private theorem accepted_122 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox122) tree122 = true := by
  simp only [tree122,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox122 3 (134476622244119296204894545978013895947714560000000000000000000 : Int) false,decode_split denominator ibox122 3 (134476622244119296204894545978013895947714560000000000000000000 : Int) true]
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
private noncomputable def tree119 : TapeTree := .split 3 (((134476622244119296204894545978013895947714560000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree120 tree121
attribute [irreducible] tree119
private theorem accepted_119 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox119) tree119 = true := by
  simp only [tree119,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox119 3 (134476622244119296204894545978013895947714560000000000000000000 : Int) false,decode_split denominator ibox119 3 (134476622244119296204894545978013895947714560000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_120 h,accepted_121 h⟩
private noncomputable def tree118 : TapeTree := .split 0 (((241037672054680703091700132125140428113366220800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree119 tree122
attribute [irreducible] tree118
private theorem accepted_118 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox118) tree118 = true := by
  simp only [tree118,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox118 0 (241037672054680703091700132125140428113366220800000000000000 : Int) false,decode_split denominator ibox118 0 (241037672054680703091700132125140428113366220800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_119 h,accepted_122 h⟩
private noncomputable def tree117 : TapeTree := .split 3 (((149418469160132551338771717753348773275238400000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree118 tree125
attribute [irreducible] tree117
private theorem accepted_117 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox117) tree117 = true := by
  simp only [tree117,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox117 3 (149418469160132551338771717753348773275238400000000000000000000 : Int) false,decode_split denominator ibox117 3 (149418469160132551338771717753348773275238400000000000000000000 : Int) true]
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
private noncomputable def tree114 : TapeTree := .split 3 (((164360316076145806472648889528683650602762240000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree115 tree116
attribute [irreducible] tree114
private theorem accepted_114 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox114) tree114 = true := by
  simp only [tree114,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox114 3 (164360316076145806472648889528683650602762240000000000000000000 : Int) false,decode_split denominator ibox114 3 (164360316076145806472648889528683650602762240000000000000000000 : Int) true]
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
private noncomputable def tree111 : TapeTree := .split 3 (((164360316076145806472648889528683650602762240000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree112 tree113
attribute [irreducible] tree111
private theorem accepted_111 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox111) tree111 = true := by
  simp only [tree111,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox111 3 (164360316076145806472648889528683650602762240000000000000000000 : Int) false,decode_split denominator ibox111 3 (164360316076145806472648889528683650602762240000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_112 h,accepted_113 h⟩
private noncomputable def tree110 : TapeTree := .split 0 (((229826617540509507599062916677459477968558489600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree111 tree114
attribute [irreducible] tree110
private theorem accepted_110 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox110) tree110 = true := by
  simp only [tree110,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox110 0 (229826617540509507599062916677459477968558489600000000000000 : Int) false,decode_split denominator ibox110 0 (229826617540509507599062916677459477968558489600000000000000 : Int) true]
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
private noncomputable def tree107 : TapeTree := .split 3 (((134476622244119296204894545978013895947714560000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree108 tree109
attribute [irreducible] tree107
private theorem accepted_107 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox107) tree107 = true := by
  simp only [tree107,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox107 3 (134476622244119296204894545978013895947714560000000000000000000 : Int) false,decode_split denominator ibox107 3 (134476622244119296204894545978013895947714560000000000000000000 : Int) true]
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
private noncomputable def tree104 : TapeTree := .split 3 (((134476622244119296204894545978013895947714560000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree105 tree106
attribute [irreducible] tree104
private theorem accepted_104 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox104) tree104 = true := by
  simp only [tree104,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox104 3 (134476622244119296204894545978013895947714560000000000000000000 : Int) false,decode_split denominator ibox104 3 (134476622244119296204894545978013895947714560000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_105 h,accepted_106 h⟩
private noncomputable def tree103 : TapeTree := .split 0 (((229826617540509507599062916677459477968558489600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree104 tree107
attribute [irreducible] tree103
private theorem accepted_103 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox103) tree103 = true := by
  simp only [tree103,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox103 0 (229826617540509507599062916677459477968558489600000000000000 : Int) false,decode_split denominator ibox103 0 (229826617540509507599062916677459477968558489600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_104 h,accepted_107 h⟩
private noncomputable def tree102 : TapeTree := .split 3 (((149418469160132551338771717753348773275238400000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree103 tree110
attribute [irreducible] tree102
private theorem accepted_102 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox102) tree102 = true := by
  simp only [tree102,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox102 3 (149418469160132551338771717753348773275238400000000000000000000 : Int) false,decode_split denominator ibox102 3 (149418469160132551338771717753348773275238400000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_103 h,accepted_110 h⟩
private noncomputable def tree101 : TapeTree := .split 0 (((235432144797595105345381524401299953040962355200000000000000 : Int) : ℚ)/(denominator : ℚ)) tree102 tree117
attribute [irreducible] tree101
private theorem accepted_101 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox101) tree101 = true := by
  simp only [tree101,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox101 0 (235432144797595105345381524401299953040962355200000000000000 : Int) false,decode_split denominator ibox101 0 (235432144797595105345381524401299953040962355200000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_102 h,accepted_117 h⟩
private noncomputable def tree100 : TapeTree := .split 3 (((179302162992159061606526061304018527930286080000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree101 tree132
attribute [irreducible] tree100
private theorem accepted_100 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox100) tree100 = true := by
  simp only [tree100,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox100 3 (179302162992159061606526061304018527930286080000000000000000000 : Int) false,decode_split denominator ibox100 3 (179302162992159061606526061304018527930286080000000000000000000 : Int) true]
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
private noncomputable def tree97 : TapeTree := .split 3 (((104592928412092785937140202427344141292666880000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree98 tree99
attribute [irreducible] tree97
private theorem accepted_97 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox97) tree97 = true := by
  simp only [tree97,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox97 3 (104592928412092785937140202427344141292666880000000000000000000 : Int) false,decode_split denominator ibox97 3 (104592928412092785937140202427344141292666880000000000000000000 : Int) true]
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
private noncomputable def tree94 : TapeTree := .split 3 (((104592928412092785937140202427344141292666880000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree95 tree96
attribute [irreducible] tree94
private theorem accepted_94 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox94) tree94 = true := by
  simp only [tree94,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox94 3 (104592928412092785937140202427344141292666880000000000000000000 : Int) false,decode_split denominator ibox94 3 (104592928412092785937140202427344141292666880000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_95 h,accepted_96 h⟩
private noncomputable def tree93 : TapeTree := .split 0 (((241037672054680703091700132125140428113366220800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree94 tree97
attribute [irreducible] tree93
private theorem accepted_93 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox93) tree93 = true := by
  simp only [tree93,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox93 0 (241037672054680703091700132125140428113366220800000000000000 : Int) false,decode_split denominator ibox93 0 (241037672054680703091700132125140428113366220800000000000000 : Int) true]
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
private noncomputable def tree90 : TapeTree := .split 3 (((74709234580066275669385858876674386637619200000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree91 tree92
attribute [irreducible] tree90
private theorem accepted_90 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox90) tree90 = true := by
  simp only [tree90,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox90 3 (74709234580066275669385858876674386637619200000000000000000000 : Int) false,decode_split denominator ibox90 3 (74709234580066275669385858876674386637619200000000000000000000 : Int) true]
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
private noncomputable def tree87 : TapeTree := .split 0 (((238234908426137904218540828263220190577164288000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree88 tree89
attribute [irreducible] tree87
private theorem accepted_87 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox87) tree87 = true := by
  simp only [tree87,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox87 0 (238234908426137904218540828263220190577164288000000000000000 : Int) false,decode_split denominator ibox87 0 (238234908426137904218540828263220190577164288000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_88 h,accepted_89 h⟩
private noncomputable def tree86 : TapeTree := .split 0 (((241037672054680703091700132125140428113366220800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree87 tree90
attribute [irreducible] tree86
private theorem accepted_86 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox86) tree86 = true := by
  simp only [tree86,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox86 0 (241037672054680703091700132125140428113366220800000000000000 : Int) false,decode_split denominator ibox86 0 (241037672054680703091700132125140428113366220800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_87 h,accepted_90 h⟩
private noncomputable def tree85 : TapeTree := .split 3 (((89651081496079530803263030652009263965143040000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree86 tree93
attribute [irreducible] tree85
private theorem accepted_85 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox85) tree85 = true := by
  simp only [tree85,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox85 3 (89651081496079530803263030652009263965143040000000000000000000 : Int) false,decode_split denominator ibox85 3 (89651081496079530803263030652009263965143040000000000000000000 : Int) true]
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
private noncomputable def tree82 : TapeTree := .split 3 (((104592928412092785937140202427344141292666880000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree83 tree84
attribute [irreducible] tree82
private theorem accepted_82 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox82) tree82 = true := by
  simp only [tree82,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox82 3 (104592928412092785937140202427344141292666880000000000000000000 : Int) false,decode_split denominator ibox82 3 (104592928412092785937140202427344141292666880000000000000000000 : Int) true]
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
private noncomputable def tree79 : TapeTree := .split 3 (((104592928412092785937140202427344141292666880000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree80 tree81
attribute [irreducible] tree79
private theorem accepted_79 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox79) tree79 = true := by
  simp only [tree79,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox79 3 (104592928412092785937140202427344141292666880000000000000000000 : Int) false,decode_split denominator ibox79 3 (104592928412092785937140202427344141292666880000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_80 h,accepted_81 h⟩
private noncomputable def tree78 : TapeTree := .split 0 (((229826617540509507599062916677459477968558489600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree79 tree82
attribute [irreducible] tree78
private theorem accepted_78 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox78) tree78 = true := by
  simp only [tree78,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox78 0 (229826617540509507599062916677459477968558489600000000000000 : Int) false,decode_split denominator ibox78 0 (229826617540509507599062916677459477968558489600000000000000 : Int) true]
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
private noncomputable def tree75 : TapeTree := .split 0 (((232629381169052306472222220539379715504760422400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree76 tree77
attribute [irreducible] tree75
private theorem accepted_75 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox75) tree75 = true := by
  simp only [tree75,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox75 0 (232629381169052306472222220539379715504760422400000000000000 : Int) false,decode_split denominator ibox75 0 (232629381169052306472222220539379715504760422400000000000000 : Int) true]
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
private noncomputable def tree72 : TapeTree := .split 0 (((227023853911966708725903612815539240432356556800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree73 tree74
attribute [irreducible] tree72
private theorem accepted_72 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox72) tree72 = true := by
  simp only [tree72,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox72 0 (227023853911966708725903612815539240432356556800000000000000 : Int) false,decode_split denominator ibox72 0 (227023853911966708725903612815539240432356556800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_73 h,accepted_74 h⟩
private noncomputable def tree71 : TapeTree := .split 0 (((229826617540509507599062916677459477968558489600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree72 tree75
attribute [irreducible] tree71
private theorem accepted_71 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox71) tree71 = true := by
  simp only [tree71,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox71 0 (229826617540509507599062916677459477968558489600000000000000 : Int) false,decode_split denominator ibox71 0 (229826617540509507599062916677459477968558489600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_72 h,accepted_75 h⟩
private noncomputable def tree70 : TapeTree := .split 3 (((89651081496079530803263030652009263965143040000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree71 tree78
attribute [irreducible] tree70
private theorem accepted_70 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox70) tree70 = true := by
  simp only [tree70,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox70 3 (89651081496079530803263030652009263965143040000000000000000000 : Int) false,decode_split denominator ibox70 3 (89651081496079530803263030652009263965143040000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_71 h,accepted_78 h⟩
private noncomputable def tree69 : TapeTree := .split 0 (((235432144797595105345381524401299953040962355200000000000000 : Int) : ℚ)/(denominator : ℚ)) tree70 tree85
attribute [irreducible] tree69
private theorem accepted_69 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox69) tree69 = true := by
  simp only [tree69,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox69 0 (235432144797595105345381524401299953040962355200000000000000 : Int) false,decode_split denominator ibox69 0 (235432144797595105345381524401299953040962355200000000000000 : Int) true]
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
private noncomputable def tree66 : TapeTree := .split 0 (((243840435683223501964859435987060665649568153600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree67 tree68
attribute [irreducible] tree66
private theorem accepted_66 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox66) tree66 = true := by
  simp only [tree66,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox66 0 (243840435683223501964859435987060665649568153600000000000000 : Int) false,decode_split denominator ibox66 0 (243840435683223501964859435987060665649568153600000000000000 : Int) true]
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
private noncomputable def tree63 : TapeTree := .split 0 (((243840435683223501964859435987060665649568153600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree64 tree65
attribute [irreducible] tree63
private theorem accepted_63 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox63) tree63 = true := by
  simp only [tree63,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox63 0 (243840435683223501964859435987060665649568153600000000000000 : Int) false,decode_split denominator ibox63 0 (243840435683223501964859435987060665649568153600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_64 h,accepted_65 h⟩
private noncomputable def tree62 : TapeTree := .split 3 (((29883693832026510267754343550669754655047680000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree63 tree66
attribute [irreducible] tree62
private theorem accepted_62 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox62) tree62 = true := by
  simp only [tree62,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox62 3 (29883693832026510267754343550669754655047680000000000000000000 : Int) false,decode_split denominator ibox62 3 (29883693832026510267754343550669754655047680000000000000000000 : Int) true]
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
private noncomputable def tree59 : TapeTree := .split 0 (((238234908426137904218540828263220190577164288000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree60 tree61
attribute [irreducible] tree59
private theorem accepted_59 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox59) tree59 = true := by
  simp only [tree59,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox59 0 (238234908426137904218540828263220190577164288000000000000000 : Int) false,decode_split denominator ibox59 0 (238234908426137904218540828263220190577164288000000000000000 : Int) true]
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
private noncomputable def tree56 : TapeTree := .split 0 (((238234908426137904218540828263220190577164288000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree57 tree58
attribute [irreducible] tree56
private theorem accepted_56 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox56) tree56 = true := by
  simp only [tree56,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox56 0 (238234908426137904218540828263220190577164288000000000000000 : Int) false,decode_split denominator ibox56 0 (238234908426137904218540828263220190577164288000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_57 h,accepted_58 h⟩
private noncomputable def tree55 : TapeTree := .split 3 (((29883693832026510267754343550669754655047680000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree56 tree59
attribute [irreducible] tree55
private theorem accepted_55 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox55) tree55 = true := by
  simp only [tree55,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox55 3 (29883693832026510267754343550669754655047680000000000000000000 : Int) false,decode_split denominator ibox55 3 (29883693832026510267754343550669754655047680000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_56 h,accepted_59 h⟩
private noncomputable def tree54 : TapeTree := .split 0 (((241037672054680703091700132125140428113366220800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree55 tree62
attribute [irreducible] tree54
private theorem accepted_54 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox54) tree54 = true := by
  simp only [tree54,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox54 0 (241037672054680703091700132125140428113366220800000000000000 : Int) false,decode_split denominator ibox54 0 (241037672054680703091700132125140428113366220800000000000000 : Int) true]
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
private noncomputable def tree51 : TapeTree := .split 0 (((232629381169052306472222220539379715504760422400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree52 tree53
attribute [irreducible] tree51
private theorem accepted_51 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox51) tree51 = true := by
  simp only [tree51,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox51 0 (232629381169052306472222220539379715504760422400000000000000 : Int) false,decode_split denominator ibox51 0 (232629381169052306472222220539379715504760422400000000000000 : Int) true]
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
private noncomputable def tree48 : TapeTree := .split 0 (((232629381169052306472222220539379715504760422400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree49 tree50
attribute [irreducible] tree48
private theorem accepted_48 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox48) tree48 = true := by
  simp only [tree48,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox48 0 (232629381169052306472222220539379715504760422400000000000000 : Int) false,decode_split denominator ibox48 0 (232629381169052306472222220539379715504760422400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_49 h,accepted_50 h⟩
private noncomputable def tree47 : TapeTree := .split 3 (((29883693832026510267754343550669754655047680000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree48 tree51
attribute [irreducible] tree47
private theorem accepted_47 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox47) tree47 = true := by
  simp only [tree47,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox47 3 (29883693832026510267754343550669754655047680000000000000000000 : Int) false,decode_split denominator ibox47 3 (29883693832026510267754343550669754655047680000000000000000000 : Int) true]
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
private noncomputable def tree44 : TapeTree := .split 0 (((227023853911966708725903612815539240432356556800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree45 tree46
attribute [irreducible] tree44
private theorem accepted_44 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox44) tree44 = true := by
  simp only [tree44,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox44 0 (227023853911966708725903612815539240432356556800000000000000 : Int) false,decode_split denominator ibox44 0 (227023853911966708725903612815539240432356556800000000000000 : Int) true]
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
private noncomputable def tree41 : TapeTree := .split 0 (((227023853911966708725903612815539240432356556800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree42 tree43
attribute [irreducible] tree41
private theorem accepted_41 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox41) tree41 = true := by
  simp only [tree41,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox41 0 (227023853911966708725903612815539240432356556800000000000000 : Int) false,decode_split denominator ibox41 0 (227023853911966708725903612815539240432356556800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_42 h,accepted_43 h⟩
private noncomputable def tree40 : TapeTree := .split 3 (((29883693832026510267754343550669754655047680000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree41 tree44
attribute [irreducible] tree40
private theorem accepted_40 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox40) tree40 = true := by
  simp only [tree40,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox40 3 (29883693832026510267754343550669754655047680000000000000000000 : Int) false,decode_split denominator ibox40 3 (29883693832026510267754343550669754655047680000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_41 h,accepted_44 h⟩
private noncomputable def tree39 : TapeTree := .split 0 (((229826617540509507599062916677459477968558489600000000000000 : Int) : ℚ)/(denominator : ℚ)) tree40 tree47
attribute [irreducible] tree39
private theorem accepted_39 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox39) tree39 = true := by
  simp only [tree39,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox39 0 (229826617540509507599062916677459477968558489600000000000000 : Int) false,decode_split denominator ibox39 0 (229826617540509507599062916677459477968558489600000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_40 h,accepted_47 h⟩
private noncomputable def tree38 : TapeTree := .split 0 (((235432144797595105345381524401299953040962355200000000000000 : Int) : ℚ)/(denominator : ℚ)) tree39 tree54
attribute [irreducible] tree38
private theorem accepted_38 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox38) tree38 = true := by
  simp only [tree38,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox38 0 (235432144797595105345381524401299953040962355200000000000000 : Int) false,decode_split denominator ibox38 0 (235432144797595105345381524401299953040962355200000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_39 h,accepted_54 h⟩
private noncomputable def tree37 : TapeTree := .split 3 (((59767387664053020535508687101339509310095360000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree38 tree69
attribute [irreducible] tree37
private theorem accepted_37 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox37) tree37 = true := by
  simp only [tree37,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox37 3 (59767387664053020535508687101339509310095360000000000000000000 : Int) false,decode_split denominator ibox37 3 (59767387664053020535508687101339509310095360000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_38 h,accepted_69 h⟩
private noncomputable def tree36 : TapeTree := .split 3 (((119534775328106041071017374202679018620190720000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree37 tree100
attribute [irreducible] tree36
private theorem accepted_36 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox36) tree36 = true := by
  simp only [tree36,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox36 3 (119534775328106041071017374202679018620190720000000000000000000 : Int) false,decode_split denominator ibox36 3 (119534775328106041071017374202679018620190720000000000000000000 : Int) true]
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
private noncomputable def tree34 : TapeTree := .split 0 (((246643199311766300838018739848980903185770086400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree35 tree163
attribute [irreducible] tree34
private theorem accepted_34 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox34) tree34 = true := by
  simp only [tree34,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox34 0 (246643199311766300838018739848980903185770086400000000000000 : Int) false,decode_split denominator ibox34 0 (246643199311766300838018739848980903185770086400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_35 h,accepted_163 h⟩
private noncomputable def tree33 : TapeTree := .split 1 (((29883693832026510267754343550669754655047680000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree34 tree239
attribute [irreducible] tree33
private theorem accepted_33 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox33) tree33 = true := by
  simp only [tree33,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox33 1 (29883693832026510267754343550669754655047680000000000000000000 : Int) false,decode_split denominator ibox33 1 (29883693832026510267754343550669754655047680000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_34 h,accepted_239 h⟩
private noncomputable def tree32 : TapeTree := .split 1 (((59767387664053020535508687101339509310095360000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree33 tree248
attribute [irreducible] tree32
private theorem accepted_32 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox32) tree32 = true := by
  simp only [tree32,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox32 1 (59767387664053020535508687101339509310095360000000000000000000 : Int) false,decode_split denominator ibox32 1 (59767387664053020535508687101339509310095360000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_33 h,accepted_248 h⟩
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
private noncomputable def tree30 : TapeTree := .split 1 (((119534775328106041071017374202679018620190720000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree31 tree253
attribute [irreducible] tree30
private theorem accepted_30 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox30) tree30 = true := by
  simp only [tree30,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox30 1 (119534775328106041071017374202679018620190720000000000000000000 : Int) false,decode_split denominator ibox30 1 (119534775328106041071017374202679018620190720000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_31 h,accepted_253 h⟩
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
private noncomputable def tree27 : TapeTree := .split 1 (((119534775328106041071017374202679018620190720000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree28 tree29
attribute [irreducible] tree27
private theorem accepted_27 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox27) tree27 = true := by
  simp only [tree27,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox27 1 (119534775328106041071017374202679018620190720000000000000000000 : Int) false,decode_split denominator ibox27 1 (119534775328106041071017374202679018620190720000000000000000000 : Int) true]
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
private noncomputable def tree23 : TapeTree := .split 1 (((119534775328106041071017374202679018620190720000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree24 tree25
attribute [irreducible] tree23
private theorem accepted_23 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox23) tree23 = true := by
  simp only [tree23,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox23 1 (119534775328106041071017374202679018620190720000000000000000000 : Int) false,decode_split denominator ibox23 1 (119534775328106041071017374202679018620190720000000000000000000 : Int) true]
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
private noncomputable def tree21 : TapeTree := .split 0 (((246643199311766300838018739848980903185770086400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree22 tree26
attribute [irreducible] tree21
private theorem accepted_21 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox21) tree21 = true := by
  simp only [tree21,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox21 0 (246643199311766300838018739848980903185770086400000000000000 : Int) false,decode_split denominator ibox21 0 (246643199311766300838018739848980903185770086400000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_22 h,accepted_26 h⟩
private noncomputable def tree20 : TapeTree := .split 2 (((179302162992159061606526061304018527930286080000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree21 tree30
attribute [irreducible] tree20
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox20 2 (179302162992159061606526061304018527930286080000000000000000000 : Int) false,decode_split denominator ibox20 2 (179302162992159061606526061304018527930286080000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_21 h,accepted_30 h⟩
private noncomputable def tree19 : TapeTree := .split 0 (((269065308340108691823293170744342803475385548800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree20 tree261
attribute [irreducible] tree19
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox19 0 (269065308340108691823293170744342803475385548800000000000000 : Int) false,decode_split denominator ibox19 0 (269065308340108691823293170744342803475385548800000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_20 h,accepted_261 h⟩
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
private noncomputable def tree16 : TapeTree := .split 0 (((291487417368451082808567601639704703765001011200000000000000 : Int) : ℚ)/(denominator : ℚ)) tree17 tree18
attribute [irreducible] tree16
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox16 0 (291487417368451082808567601639704703765001011200000000000000 : Int) false,decode_split denominator ibox16 0 (291487417368451082808567601639704703765001011200000000000000 : Int) true]
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
private noncomputable def tree14 : TapeTree := .split 1 (((179302162992159061606526061304018527930286080000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree15 tree16
attribute [irreducible] tree14
private theorem accepted_14 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox14) tree14 = true := by
  simp only [tree14,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox14 1 (179302162992159061606526061304018527930286080000000000000000000 : Int) false,decode_split denominator ibox14 1 (179302162992159061606526061304018527930286080000000000000000000 : Int) true]
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
private noncomputable def tree11 : TapeTree := .split 1 (((119534775328106041071017374202679018620190720000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree12 tree14
attribute [irreducible] tree11
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox11 1 (119534775328106041071017374202679018620190720000000000000000000 : Int) false,decode_split denominator ibox11 1 (119534775328106041071017374202679018620190720000000000000000000 : Int) true]
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
private noncomputable def tree6 : TapeTree := .split 0 (((246643199311766300838018739848980903185770086400000000000000 : Int) : ℚ)/(denominator : ℚ)) tree7 tree9
attribute [irreducible] tree6
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox6 0 (246643199311766300838018739848980903185770086400000000000000 : Int) false,decode_split denominator ibox6 0 (246643199311766300838018739848980903185770086400000000000000 : Int) true]
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
private noncomputable def tree3 : TapeTree := .split 1 (((119534775328106041071017374202679018620190720000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree6
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 1 (119534775328106041071017374202679018620190720000000000000000000 : Int) false,decode_split denominator ibox3 1 (119534775328106041071017374202679018620190720000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_6 h⟩
private noncomputable def tree2 : TapeTree := .split 0 (((269065308340108691823293170744342803475385548800000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree11
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 0 (269065308340108691823293170744342803475385548800000000000000 : Int) false,decode_split denominator ibox2 0 (269065308340108691823293170744342803475385548800000000000000 : Int) true]
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
private noncomputable def tree0 : TapeTree := .split 2 (((119534775328106041071017374202679018620190720000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree1 tree19
attribute [irreducible] tree0
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox0 2 (119534775328106041071017374202679018620190720000000000000000000 : Int) false,decode_split denominator ibox0 2 (119534775328106041071017374202679018620190720000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_1 h,accepted_19 h⟩
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (2401/2560000 : ℚ) (16807/12800000 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 212 = e219 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (2401/2560000 : ℚ) (16807/12800000 : ℚ)) x → eval e219 x ≤ 0 := by
  have hb := h.child_4 tape 212 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell5_low_internal

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell5_low_internal
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((2401/2560000 : ℚ) : ℝ) < p ∧ p ≤ ((16807/12800000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 5 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 5 p)
    (hk0 : ((16807/12800000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((2401/2560000 : ℚ) : ℝ))
    (hk1 : ((16807/12800000 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((2401/2560000 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r), internalResidual (0 : Fin 9) a p A r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell5_low_internal.cell_bound h.child_8 h.child_9 (Cell5_low_internal.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell5_low_internal
