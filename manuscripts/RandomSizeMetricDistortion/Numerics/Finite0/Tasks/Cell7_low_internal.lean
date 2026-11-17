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
namespace Cell7_low_internal
private noncomputable def qValues : Fin 2 → ℚ := ![(14098610571353791/512000000000000000000 : ℚ),(11589681623189/2000000000000 : ℚ)]
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
    priceLambda 7 p = ((14098610571353791/512000000000000000000 : ℝ)+(11589681623189/2000000000000 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell7,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 7 p = (((145513/100000 : ℝ)+(145513/25000 : ℝ)*p)-(145513/100000 : ℝ)*(1/1 : ℝ))/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell7,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e219 x = (x 0*(1-x 0))*(aPoint x+priceLambda 7 (x 0)*(HStar (yPoint x)-HStar (aPoint x)-HStar (capPoint x))+priceTau 7 (x 0)*psiStar (rPoint x)+(0)-(0)) := by
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
    (hL : lambdaStar (x 0) = priceLambda 7 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 7 (x 0)) :
    (1)*eval e219 x = (x 0*(1-x 0))*(internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,if_pos hA,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (117649/64000000 : ℚ) (823543/320000000 : ℚ)) x → eval e219 x ≤ 0)
    (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((117649/64000000 : ℚ) : ℝ) < p ∧ p ≤ ((823543/320000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 7 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 7 p)
    (hk0 : ((823543/320000000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((117649/64000000 : ℚ) : ℝ))
    (hk1 : ((823543/320000000 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((117649/64000000 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r) :
    internalResidual (0 : Fin 9) a p A r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxA,hxr⟩ := h3 (117649/64000000 : ℚ) (823543/320000000 : ℚ) ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ) p a A r hpcell hk0 hk1 hr ha hap hpA hAr
  have hcut : ((823543/320000000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) := by norm_num [bStar]
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxa
  have hAx : capPoint x = A := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxA
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 7 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 7 (x 0) := by simpa only [hxp] using hT
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
.const (14098610571353791/512000000000000000000 : ℚ),
.const (11589681623189/2000000000000 : ℚ),
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
private noncomputable def ssaQVals : Fin 16 → ℚ := ![(1/1 : ℚ),(49/100 : ℚ),(390189/5000000 : ℚ),(1085/4818 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(4818/3733 : ℚ),(14098610571353791/512000000000000000000 : ℚ),(11589681623189/2000000000000 : ℚ),(145513/100000 : ℚ),(145513/25000 : ℚ),(-145513/100000 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ)]
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
private noncomputable def denominator : Int := 1867730864501656891734646471916859665940480000000000000000000000000
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
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨3433385444964928619620147230852290981847367680000000000000000000,4806739622950900067468206123193207374586314752000000000000000000⟩,⟨0,1867730864501656891734646471916859665940480000000000000000000000000⟩,⟨0,1867730864501656891734646471916859665940480000000000000000000000000⟩,⟨0,1867730864501656891734646471916859665940480000000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := splitI ibox0 2 933865432250828445867323235958429832970240000000000000000000000000 false
private noncomputable def ibox2 : Fin 4 → FixedTape.I := faceI ibox1 3 false
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 0 4120062533957914343544176677022749178216841216000000000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 1 933865432250828445867323235958429832970240000000000000000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := faceI ibox4 2 true
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox3 1 933865432250828445867323235958429832970240000000000000000000000000 true
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox6 0 3776723989461421481582161953937520080032104448000000000000000000 false
private noncomputable def ibox8 : Fin 4 → FixedTape.I := faceI ibox7 1 true
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox6 0 3776723989461421481582161953937520080032104448000000000000000000 true
private noncomputable def ibox10 : Fin 4 → FixedTape.I := faceI ibox9 1 true
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox2 0 4120062533957914343544176677022749178216841216000000000000000000 true
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox11 1 933865432250828445867323235958429832970240000000000000000000000000 false
private noncomputable def ibox13 : Fin 4 → FixedTape.I := faceI ibox12 2 true
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox11 1 933865432250828445867323235958429832970240000000000000000000000000 true
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox14 1 1400798148376242668800984853937644749455360000000000000000000000000 false
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox14 1 1400798148376242668800984853937644749455360000000000000000000000000 true
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox16 0 4463401078454407205506191400107978276401577984000000000000000000 false
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox16 0 4463401078454407205506191400107978276401577984000000000000000000 true
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox0 2 933865432250828445867323235958429832970240000000000000000000000000 true
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox19 0 4120062533957914343544176677022749178216841216000000000000000000 false
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox20 2 1400798148376242668800984853937644749455360000000000000000000000000 false
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox21 0 3776723989461421481582161953937520080032104448000000000000000000 false
private noncomputable def ibox23 : Fin 4 → FixedTape.I := faceI ibox22 3 false
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox23 1 933865432250828445867323235958429832970240000000000000000000000000 false
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox23 1 933865432250828445867323235958429832970240000000000000000000000000 true
private noncomputable def ibox26 : Fin 4 → FixedTape.I := splitI ibox21 0 3776723989461421481582161953937520080032104448000000000000000000 true
private noncomputable def ibox27 : Fin 4 → FixedTape.I := faceI ibox26 3 false
private noncomputable def ibox28 : Fin 4 → FixedTape.I := splitI ibox27 1 933865432250828445867323235958429832970240000000000000000000000000 false
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox27 1 933865432250828445867323235958429832970240000000000000000000000000 true
private noncomputable def ibox30 : Fin 4 → FixedTape.I := splitI ibox20 2 1400798148376242668800984853937644749455360000000000000000000000000 true
private noncomputable def ibox31 : Fin 4 → FixedTape.I := splitI ibox30 1 933865432250828445867323235958429832970240000000000000000000000000 false
private noncomputable def ibox32 : Fin 4 → FixedTape.I := faceI ibox31 2 true
private noncomputable def ibox33 : Fin 4 → FixedTape.I := splitI ibox32 1 466932716125414222933661617979214916485120000000000000000000000000 false
private noncomputable def ibox34 : Fin 4 → FixedTape.I := splitI ibox33 1 233466358062707111466830808989607458242560000000000000000000000000 false
private noncomputable def ibox35 : Fin 4 → FixedTape.I := splitI ibox34 0 3776723989461421481582161953937520080032104448000000000000000000 false
private noncomputable def ibox36 : Fin 4 → FixedTape.I := faceI ibox35 1 false
private noncomputable def ibox37 : Fin 4 → FixedTape.I := splitI ibox36 3 933865432250828445867323235958429832970240000000000000000000000000 false
private noncomputable def ibox38 : Fin 4 → FixedTape.I := splitI ibox37 3 466932716125414222933661617979214916485120000000000000000000000000 false
private noncomputable def ibox39 : Fin 4 → FixedTape.I := splitI ibox38 0 3605054717213175050601154592394905530939736064000000000000000000 false
private noncomputable def ibox40 : Fin 4 → FixedTape.I := splitI ibox39 0 3519220081089051835110650911623598256393551872000000000000000000 false
private noncomputable def ibox41 : Fin 4 → FixedTape.I := splitI ibox40 3 233466358062707111466830808989607458242560000000000000000000000000 false
private noncomputable def ibox42 : Fin 4 → FixedTape.I := splitI ibox40 3 233466358062707111466830808989607458242560000000000000000000000000 true
private noncomputable def ibox43 : Fin 4 → FixedTape.I := splitI ibox39 0 3519220081089051835110650911623598256393551872000000000000000000 true
private noncomputable def ibox44 : Fin 4 → FixedTape.I := splitI ibox43 3 233466358062707111466830808989607458242560000000000000000000000000 false
private noncomputable def ibox45 : Fin 4 → FixedTape.I := splitI ibox43 3 233466358062707111466830808989607458242560000000000000000000000000 true
private noncomputable def ibox46 : Fin 4 → FixedTape.I := splitI ibox38 0 3605054717213175050601154592394905530939736064000000000000000000 true
private noncomputable def ibox47 : Fin 4 → FixedTape.I := splitI ibox46 0 3690889353337298266091658273166212805485920256000000000000000000 false
private noncomputable def ibox48 : Fin 4 → FixedTape.I := splitI ibox47 3 233466358062707111466830808989607458242560000000000000000000000000 false
private noncomputable def ibox49 : Fin 4 → FixedTape.I := splitI ibox47 3 233466358062707111466830808989607458242560000000000000000000000000 true
private noncomputable def ibox50 : Fin 4 → FixedTape.I := splitI ibox46 0 3690889353337298266091658273166212805485920256000000000000000000 true
private noncomputable def ibox51 : Fin 4 → FixedTape.I := splitI ibox50 3 233466358062707111466830808989607458242560000000000000000000000000 false
private noncomputable def ibox52 : Fin 4 → FixedTape.I := splitI ibox50 3 233466358062707111466830808989607458242560000000000000000000000000 true
private noncomputable def ibox53 : Fin 4 → FixedTape.I := splitI ibox37 3 466932716125414222933661617979214916485120000000000000000000000000 true
private noncomputable def ibox54 : Fin 4 → FixedTape.I := splitI ibox53 0 3605054717213175050601154592394905530939736064000000000000000000 false
private noncomputable def ibox55 : Fin 4 → FixedTape.I := splitI ibox54 0 3519220081089051835110650911623598256393551872000000000000000000 false
private noncomputable def ibox56 : Fin 4 → FixedTape.I := splitI ibox55 3 700399074188121334400492426968822374727680000000000000000000000000 false
private noncomputable def ibox57 : Fin 4 → FixedTape.I := splitI ibox55 3 700399074188121334400492426968822374727680000000000000000000000000 true
private noncomputable def ibox58 : Fin 4 → FixedTape.I := splitI ibox54 0 3519220081089051835110650911623598256393551872000000000000000000 true
private noncomputable def ibox59 : Fin 4 → FixedTape.I := splitI ibox58 3 700399074188121334400492426968822374727680000000000000000000000000 false
private noncomputable def ibox60 : Fin 4 → FixedTape.I := splitI ibox58 3 700399074188121334400492426968822374727680000000000000000000000000 true
private noncomputable def ibox61 : Fin 4 → FixedTape.I := splitI ibox53 0 3605054717213175050601154592394905530939736064000000000000000000 true
private noncomputable def ibox62 : Fin 4 → FixedTape.I := splitI ibox61 3 700399074188121334400492426968822374727680000000000000000000000000 false
private noncomputable def ibox63 : Fin 4 → FixedTape.I := splitI ibox62 0 3690889353337298266091658273166212805485920256000000000000000000 false
private noncomputable def ibox64 : Fin 4 → FixedTape.I := splitI ibox62 0 3690889353337298266091658273166212805485920256000000000000000000 true
private noncomputable def ibox65 : Fin 4 → FixedTape.I := splitI ibox61 3 700399074188121334400492426968822374727680000000000000000000000000 true
private noncomputable def ibox66 : Fin 4 → FixedTape.I := splitI ibox65 0 3690889353337298266091658273166212805485920256000000000000000000 false
private noncomputable def ibox67 : Fin 4 → FixedTape.I := splitI ibox65 0 3690889353337298266091658273166212805485920256000000000000000000 true
private noncomputable def ibox68 : Fin 4 → FixedTape.I := splitI ibox36 3 933865432250828445867323235958429832970240000000000000000000000000 true
private noncomputable def ibox69 : Fin 4 → FixedTape.I := splitI ibox68 3 1400798148376242668800984853937644749455360000000000000000000000000 false
private noncomputable def ibox70 : Fin 4 → FixedTape.I := splitI ibox69 0 3605054717213175050601154592394905530939736064000000000000000000 false
private noncomputable def ibox71 : Fin 4 → FixedTape.I := splitI ibox70 3 1167331790313535557334154044948037291212800000000000000000000000000 false
private noncomputable def ibox72 : Fin 4 → FixedTape.I := splitI ibox71 0 3519220081089051835110650911623598256393551872000000000000000000 false
private noncomputable def ibox73 : Fin 4 → FixedTape.I := splitI ibox71 0 3519220081089051835110650911623598256393551872000000000000000000 true
private noncomputable def ibox74 : Fin 4 → FixedTape.I := splitI ibox70 3 1167331790313535557334154044948037291212800000000000000000000000000 true
private noncomputable def ibox75 : Fin 4 → FixedTape.I := splitI ibox74 0 3519220081089051835110650911623598256393551872000000000000000000 false
private noncomputable def ibox76 : Fin 4 → FixedTape.I := splitI ibox74 0 3519220081089051835110650911623598256393551872000000000000000000 true
private noncomputable def ibox77 : Fin 4 → FixedTape.I := splitI ibox69 0 3605054717213175050601154592394905530939736064000000000000000000 true
private noncomputable def ibox78 : Fin 4 → FixedTape.I := splitI ibox77 3 1167331790313535557334154044948037291212800000000000000000000000000 false
private noncomputable def ibox79 : Fin 4 → FixedTape.I := splitI ibox78 0 3690889353337298266091658273166212805485920256000000000000000000 false
private noncomputable def ibox80 : Fin 4 → FixedTape.I := splitI ibox78 0 3690889353337298266091658273166212805485920256000000000000000000 true
private noncomputable def ibox81 : Fin 4 → FixedTape.I := splitI ibox77 3 1167331790313535557334154044948037291212800000000000000000000000000 true
private noncomputable def ibox82 : Fin 4 → FixedTape.I := splitI ibox81 0 3690889353337298266091658273166212805485920256000000000000000000 false
private noncomputable def ibox83 : Fin 4 → FixedTape.I := splitI ibox81 0 3690889353337298266091658273166212805485920256000000000000000000 true
private noncomputable def ibox84 : Fin 4 → FixedTape.I := splitI ibox68 3 1400798148376242668800984853937644749455360000000000000000000000000 true
private noncomputable def ibox85 : Fin 4 → FixedTape.I := splitI ibox84 0 3605054717213175050601154592394905530939736064000000000000000000 false
private noncomputable def ibox86 : Fin 4 → FixedTape.I := splitI ibox85 3 1634264506438949780267815662927252207697920000000000000000000000000 false
private noncomputable def ibox87 : Fin 4 → FixedTape.I := splitI ibox86 0 3519220081089051835110650911623598256393551872000000000000000000 false
private noncomputable def ibox88 : Fin 4 → FixedTape.I := splitI ibox86 0 3519220081089051835110650911623598256393551872000000000000000000 true
private noncomputable def ibox89 : Fin 4 → FixedTape.I := splitI ibox85 3 1634264506438949780267815662927252207697920000000000000000000000000 true
private noncomputable def ibox90 : Fin 4 → FixedTape.I := splitI ibox89 0 3519220081089051835110650911623598256393551872000000000000000000 false
private noncomputable def ibox91 : Fin 4 → FixedTape.I := splitI ibox89 0 3519220081089051835110650911623598256393551872000000000000000000 true
private noncomputable def ibox92 : Fin 4 → FixedTape.I := splitI ibox84 0 3605054717213175050601154592394905530939736064000000000000000000 true
private noncomputable def ibox93 : Fin 4 → FixedTape.I := splitI ibox92 3 1634264506438949780267815662927252207697920000000000000000000000000 false
private noncomputable def ibox94 : Fin 4 → FixedTape.I := splitI ibox93 0 3690889353337298266091658273166212805485920256000000000000000000 false
private noncomputable def ibox95 : Fin 4 → FixedTape.I := splitI ibox93 0 3690889353337298266091658273166212805485920256000000000000000000 true
private noncomputable def ibox96 : Fin 4 → FixedTape.I := splitI ibox92 3 1634264506438949780267815662927252207697920000000000000000000000000 true
private noncomputable def ibox97 : Fin 4 → FixedTape.I := splitI ibox96 0 3690889353337298266091658273166212805485920256000000000000000000 false
private noncomputable def ibox98 : Fin 4 → FixedTape.I := splitI ibox96 0 3690889353337298266091658273166212805485920256000000000000000000 true
private noncomputable def ibox99 : Fin 4 → FixedTape.I := splitI ibox34 0 3776723989461421481582161953937520080032104448000000000000000000 true
private noncomputable def ibox100 : Fin 4 → FixedTape.I := faceI ibox99 1 false
private noncomputable def ibox101 : Fin 4 → FixedTape.I := splitI ibox100 3 933865432250828445867323235958429832970240000000000000000000000000 false
private noncomputable def ibox102 : Fin 4 → FixedTape.I := splitI ibox101 3 466932716125414222933661617979214916485120000000000000000000000000 false
private noncomputable def ibox103 : Fin 4 → FixedTape.I := splitI ibox102 0 3948393261709667912563169315480134629124472832000000000000000000 false
private noncomputable def ibox104 : Fin 4 → FixedTape.I := splitI ibox103 0 3862558625585544697072665634708827354578288640000000000000000000 false
private noncomputable def ibox105 : Fin 4 → FixedTape.I := splitI ibox104 3 233466358062707111466830808989607458242560000000000000000000000000 false
private noncomputable def ibox106 : Fin 4 → FixedTape.I := splitI ibox104 3 233466358062707111466830808989607458242560000000000000000000000000 true
private noncomputable def ibox107 : Fin 4 → FixedTape.I := splitI ibox103 0 3862558625585544697072665634708827354578288640000000000000000000 true
private noncomputable def ibox108 : Fin 4 → FixedTape.I := splitI ibox107 3 233466358062707111466830808989607458242560000000000000000000000000 false
private noncomputable def ibox109 : Fin 4 → FixedTape.I := splitI ibox107 3 233466358062707111466830808989607458242560000000000000000000000000 true
private noncomputable def ibox110 : Fin 4 → FixedTape.I := splitI ibox102 0 3948393261709667912563169315480134629124472832000000000000000000 true
private noncomputable def ibox111 : Fin 4 → FixedTape.I := splitI ibox110 0 4034227897833791128053672996251441903670657024000000000000000000 false
private noncomputable def ibox112 : Fin 4 → FixedTape.I := splitI ibox111 3 233466358062707111466830808989607458242560000000000000000000000000 false
private noncomputable def ibox113 : Fin 4 → FixedTape.I := splitI ibox111 3 233466358062707111466830808989607458242560000000000000000000000000 true
private noncomputable def ibox114 : Fin 4 → FixedTape.I := splitI ibox110 0 4034227897833791128053672996251441903670657024000000000000000000 true
private noncomputable def ibox115 : Fin 4 → FixedTape.I := splitI ibox101 3 466932716125414222933661617979214916485120000000000000000000000000 true
private noncomputable def ibox116 : Fin 4 → FixedTape.I := splitI ibox115 0 3948393261709667912563169315480134629124472832000000000000000000 false
private noncomputable def ibox117 : Fin 4 → FixedTape.I := splitI ibox116 3 700399074188121334400492426968822374727680000000000000000000000000 false
private noncomputable def ibox118 : Fin 4 → FixedTape.I := splitI ibox117 0 3862558625585544697072665634708827354578288640000000000000000000 false
private noncomputable def ibox119 : Fin 4 → FixedTape.I := splitI ibox117 0 3862558625585544697072665634708827354578288640000000000000000000 true
private noncomputable def ibox120 : Fin 4 → FixedTape.I := splitI ibox116 3 700399074188121334400492426968822374727680000000000000000000000000 true
private noncomputable def ibox121 : Fin 4 → FixedTape.I := splitI ibox120 0 3862558625585544697072665634708827354578288640000000000000000000 false
private noncomputable def ibox122 : Fin 4 → FixedTape.I := splitI ibox120 0 3862558625585544697072665634708827354578288640000000000000000000 true
private noncomputable def ibox123 : Fin 4 → FixedTape.I := splitI ibox115 0 3948393261709667912563169315480134629124472832000000000000000000 true
private noncomputable def ibox124 : Fin 4 → FixedTape.I := splitI ibox123 3 700399074188121334400492426968822374727680000000000000000000000000 false
private noncomputable def ibox125 : Fin 4 → FixedTape.I := splitI ibox123 3 700399074188121334400492426968822374727680000000000000000000000000 true
private noncomputable def ibox126 : Fin 4 → FixedTape.I := splitI ibox100 3 933865432250828445867323235958429832970240000000000000000000000000 true
private noncomputable def ibox127 : Fin 4 → FixedTape.I := splitI ibox126 3 1400798148376242668800984853937644749455360000000000000000000000000 false
private noncomputable def ibox128 : Fin 4 → FixedTape.I := splitI ibox127 0 3948393261709667912563169315480134629124472832000000000000000000 false
private noncomputable def ibox129 : Fin 4 → FixedTape.I := splitI ibox128 3 1167331790313535557334154044948037291212800000000000000000000000000 false
private noncomputable def ibox130 : Fin 4 → FixedTape.I := splitI ibox129 0 3862558625585544697072665634708827354578288640000000000000000000 false
private noncomputable def ibox131 : Fin 4 → FixedTape.I := splitI ibox129 0 3862558625585544697072665634708827354578288640000000000000000000 true
private noncomputable def ibox132 : Fin 4 → FixedTape.I := splitI ibox128 3 1167331790313535557334154044948037291212800000000000000000000000000 true
private noncomputable def ibox133 : Fin 4 → FixedTape.I := splitI ibox132 0 3862558625585544697072665634708827354578288640000000000000000000 false
private noncomputable def ibox134 : Fin 4 → FixedTape.I := splitI ibox132 0 3862558625585544697072665634708827354578288640000000000000000000 true
private noncomputable def ibox135 : Fin 4 → FixedTape.I := splitI ibox127 0 3948393261709667912563169315480134629124472832000000000000000000 true
private noncomputable def ibox136 : Fin 4 → FixedTape.I := splitI ibox135 3 1167331790313535557334154044948037291212800000000000000000000000000 false
private noncomputable def ibox137 : Fin 4 → FixedTape.I := splitI ibox135 3 1167331790313535557334154044948037291212800000000000000000000000000 true
private noncomputable def ibox138 : Fin 4 → FixedTape.I := splitI ibox126 3 1400798148376242668800984853937644749455360000000000000000000000000 true
private noncomputable def ibox139 : Fin 4 → FixedTape.I := splitI ibox138 0 3948393261709667912563169315480134629124472832000000000000000000 false
private noncomputable def ibox140 : Fin 4 → FixedTape.I := splitI ibox139 3 1634264506438949780267815662927252207697920000000000000000000000000 false
private noncomputable def ibox141 : Fin 4 → FixedTape.I := splitI ibox139 3 1634264506438949780267815662927252207697920000000000000000000000000 true
private noncomputable def ibox142 : Fin 4 → FixedTape.I := splitI ibox138 0 3948393261709667912563169315480134629124472832000000000000000000 true
private noncomputable def ibox143 : Fin 4 → FixedTape.I := splitI ibox142 3 1634264506438949780267815662927252207697920000000000000000000000000 false
private noncomputable def ibox144 : Fin 4 → FixedTape.I := splitI ibox142 3 1634264506438949780267815662927252207697920000000000000000000000000 true
private noncomputable def ibox145 : Fin 4 → FixedTape.I := splitI ibox33 1 233466358062707111466830808989607458242560000000000000000000000000 true
private noncomputable def ibox146 : Fin 4 → FixedTape.I := splitI ibox145 0 3776723989461421481582161953937520080032104448000000000000000000 false
private noncomputable def ibox147 : Fin 4 → FixedTape.I := faceI ibox146 1 false
private noncomputable def ibox148 : Fin 4 → FixedTape.I := splitI ibox147 3 933865432250828445867323235958429832970240000000000000000000000000 false
private noncomputable def ibox149 : Fin 4 → FixedTape.I := splitI ibox147 3 933865432250828445867323235958429832970240000000000000000000000000 true
private noncomputable def ibox150 : Fin 4 → FixedTape.I := splitI ibox145 0 3776723989461421481582161953937520080032104448000000000000000000 true
private noncomputable def ibox151 : Fin 4 → FixedTape.I := faceI ibox150 1 false
private noncomputable def ibox152 : Fin 4 → FixedTape.I := splitI ibox151 3 933865432250828445867323235958429832970240000000000000000000000000 false
private noncomputable def ibox153 : Fin 4 → FixedTape.I := splitI ibox151 3 933865432250828445867323235958429832970240000000000000000000000000 true
private noncomputable def ibox154 : Fin 4 → FixedTape.I := splitI ibox32 1 466932716125414222933661617979214916485120000000000000000000000000 true
private noncomputable def ibox155 : Fin 4 → FixedTape.I := splitI ibox154 0 3776723989461421481582161953937520080032104448000000000000000000 false
private noncomputable def ibox156 : Fin 4 → FixedTape.I := faceI ibox155 1 false
private noncomputable def ibox157 : Fin 4 → FixedTape.I := splitI ibox154 0 3776723989461421481582161953937520080032104448000000000000000000 true
private noncomputable def ibox158 : Fin 4 → FixedTape.I := faceI ibox157 1 false
private noncomputable def ibox159 : Fin 4 → FixedTape.I := splitI ibox30 1 933865432250828445867323235958429832970240000000000000000000000000 true
private noncomputable def ibox160 : Fin 4 → FixedTape.I := faceI ibox159 3 false
private noncomputable def ibox161 : Fin 4 → FixedTape.I := splitI ibox160 0 3776723989461421481582161953937520080032104448000000000000000000 false
private noncomputable def ibox162 : Fin 4 → FixedTape.I := splitI ibox161 1 1400798148376242668800984853937644749455360000000000000000000000000 false
private noncomputable def ibox163 : Fin 4 → FixedTape.I := splitI ibox161 1 1400798148376242668800984853937644749455360000000000000000000000000 true
private noncomputable def ibox164 : Fin 4 → FixedTape.I := splitI ibox160 0 3776723989461421481582161953937520080032104448000000000000000000 true
private noncomputable def ibox165 : Fin 4 → FixedTape.I := splitI ibox164 1 1400798148376242668800984853937644749455360000000000000000000000000 false
private noncomputable def ibox166 : Fin 4 → FixedTape.I := splitI ibox164 1 1400798148376242668800984853937644749455360000000000000000000000000 true
private noncomputable def ibox167 : Fin 4 → FixedTape.I := splitI ibox19 0 4120062533957914343544176677022749178216841216000000000000000000 true
private noncomputable def ibox168 : Fin 4 → FixedTape.I := splitI ibox167 2 1400798148376242668800984853937644749455360000000000000000000000000 false
private noncomputable def ibox169 : Fin 4 → FixedTape.I := faceI ibox168 3 false
private noncomputable def ibox170 : Fin 4 → FixedTape.I := splitI ibox169 0 4463401078454407205506191400107978276401577984000000000000000000 false
private noncomputable def ibox171 : Fin 4 → FixedTape.I := splitI ibox170 1 933865432250828445867323235958429832970240000000000000000000000000 false
private noncomputable def ibox172 : Fin 4 → FixedTape.I := splitI ibox170 1 933865432250828445867323235958429832970240000000000000000000000000 true
private noncomputable def ibox173 : Fin 4 → FixedTape.I := splitI ibox169 0 4463401078454407205506191400107978276401577984000000000000000000 true
private noncomputable def ibox174 : Fin 4 → FixedTape.I := splitI ibox173 1 933865432250828445867323235958429832970240000000000000000000000000 false
private noncomputable def ibox175 : Fin 4 → FixedTape.I := splitI ibox173 1 933865432250828445867323235958429832970240000000000000000000000000 true
private noncomputable def ibox176 : Fin 4 → FixedTape.I := splitI ibox167 2 1400798148376242668800984853937644749455360000000000000000000000000 true
private noncomputable def ibox177 : Fin 4 → FixedTape.I := splitI ibox176 1 933865432250828445867323235958429832970240000000000000000000000000 false
private noncomputable def ibox178 : Fin 4 → FixedTape.I := faceI ibox177 2 true
private noncomputable def ibox179 : Fin 4 → FixedTape.I := splitI ibox178 1 466932716125414222933661617979214916485120000000000000000000000000 false
private noncomputable def ibox180 : Fin 4 → FixedTape.I := splitI ibox179 1 233466358062707111466830808989607458242560000000000000000000000000 false
private noncomputable def ibox181 : Fin 4 → FixedTape.I := splitI ibox180 0 4463401078454407205506191400107978276401577984000000000000000000 false
private noncomputable def ibox182 : Fin 4 → FixedTape.I := faceI ibox181 1 false
private noncomputable def ibox183 : Fin 4 → FixedTape.I := splitI ibox182 3 933865432250828445867323235958429832970240000000000000000000000000 false
private noncomputable def ibox184 : Fin 4 → FixedTape.I := splitI ibox183 3 466932716125414222933661617979214916485120000000000000000000000000 false
private noncomputable def ibox185 : Fin 4 → FixedTape.I := splitI ibox184 0 4291731806206160774525184038565363727309209600000000000000000000 false
private noncomputable def ibox186 : Fin 4 → FixedTape.I := splitI ibox185 3 233466358062707111466830808989607458242560000000000000000000000000 false
private noncomputable def ibox187 : Fin 4 → FixedTape.I := splitI ibox185 3 233466358062707111466830808989607458242560000000000000000000000000 true
private noncomputable def ibox188 : Fin 4 → FixedTape.I := splitI ibox184 0 4291731806206160774525184038565363727309209600000000000000000000 true
private noncomputable def ibox189 : Fin 4 → FixedTape.I := splitI ibox188 3 233466358062707111466830808989607458242560000000000000000000000000 false
private noncomputable def ibox190 : Fin 4 → FixedTape.I := splitI ibox188 3 233466358062707111466830808989607458242560000000000000000000000000 true
private noncomputable def ibox191 : Fin 4 → FixedTape.I := splitI ibox183 3 466932716125414222933661617979214916485120000000000000000000000000 true
private noncomputable def ibox192 : Fin 4 → FixedTape.I := splitI ibox191 0 4291731806206160774525184038565363727309209600000000000000000000 false
private noncomputable def ibox193 : Fin 4 → FixedTape.I := splitI ibox192 3 700399074188121334400492426968822374727680000000000000000000000000 false
private noncomputable def ibox194 : Fin 4 → FixedTape.I := splitI ibox192 3 700399074188121334400492426968822374727680000000000000000000000000 true
private noncomputable def ibox195 : Fin 4 → FixedTape.I := splitI ibox191 0 4291731806206160774525184038565363727309209600000000000000000000 true
private noncomputable def ibox196 : Fin 4 → FixedTape.I := splitI ibox195 3 700399074188121334400492426968822374727680000000000000000000000000 false
private noncomputable def ibox197 : Fin 4 → FixedTape.I := splitI ibox195 3 700399074188121334400492426968822374727680000000000000000000000000 true
private noncomputable def ibox198 : Fin 4 → FixedTape.I := splitI ibox182 3 933865432250828445867323235958429832970240000000000000000000000000 true
private noncomputable def ibox199 : Fin 4 → FixedTape.I := splitI ibox198 3 1400798148376242668800984853937644749455360000000000000000000000000 false
private noncomputable def ibox200 : Fin 4 → FixedTape.I := splitI ibox199 0 4291731806206160774525184038565363727309209600000000000000000000 false
private noncomputable def ibox201 : Fin 4 → FixedTape.I := splitI ibox200 3 1167331790313535557334154044948037291212800000000000000000000000000 false
private noncomputable def ibox202 : Fin 4 → FixedTape.I := splitI ibox200 3 1167331790313535557334154044948037291212800000000000000000000000000 true
private noncomputable def ibox203 : Fin 4 → FixedTape.I := splitI ibox199 0 4291731806206160774525184038565363727309209600000000000000000000 true
private noncomputable def ibox204 : Fin 4 → FixedTape.I := splitI ibox203 3 1167331790313535557334154044948037291212800000000000000000000000000 false
private noncomputable def ibox205 : Fin 4 → FixedTape.I := splitI ibox203 3 1167331790313535557334154044948037291212800000000000000000000000000 true
private noncomputable def ibox206 : Fin 4 → FixedTape.I := splitI ibox198 3 1400798148376242668800984853937644749455360000000000000000000000000 true
private noncomputable def ibox207 : Fin 4 → FixedTape.I := splitI ibox206 0 4291731806206160774525184038565363727309209600000000000000000000 false
private noncomputable def ibox208 : Fin 4 → FixedTape.I := splitI ibox207 3 1634264506438949780267815662927252207697920000000000000000000000000 false
private noncomputable def ibox209 : Fin 4 → FixedTape.I := splitI ibox207 3 1634264506438949780267815662927252207697920000000000000000000000000 true
private noncomputable def ibox210 : Fin 4 → FixedTape.I := splitI ibox206 0 4291731806206160774525184038565363727309209600000000000000000000 true
private noncomputable def ibox211 : Fin 4 → FixedTape.I := splitI ibox210 3 1634264506438949780267815662927252207697920000000000000000000000000 false
private noncomputable def ibox212 : Fin 4 → FixedTape.I := splitI ibox210 3 1634264506438949780267815662927252207697920000000000000000000000000 true
private noncomputable def ibox213 : Fin 4 → FixedTape.I := splitI ibox180 0 4463401078454407205506191400107978276401577984000000000000000000 true
private noncomputable def ibox214 : Fin 4 → FixedTape.I := faceI ibox213 1 false
private noncomputable def ibox215 : Fin 4 → FixedTape.I := splitI ibox214 3 933865432250828445867323235958429832970240000000000000000000000000 false
private noncomputable def ibox216 : Fin 4 → FixedTape.I := splitI ibox215 3 466932716125414222933661617979214916485120000000000000000000000000 false
private noncomputable def ibox217 : Fin 4 → FixedTape.I := splitI ibox216 0 4635070350702653636487198761650592825493946368000000000000000000 false
private noncomputable def ibox218 : Fin 4 → FixedTape.I := splitI ibox217 3 233466358062707111466830808989607458242560000000000000000000000000 false
private noncomputable def ibox219 : Fin 4 → FixedTape.I := splitI ibox217 3 233466358062707111466830808989607458242560000000000000000000000000 true
private noncomputable def ibox220 : Fin 4 → FixedTape.I := splitI ibox216 0 4635070350702653636487198761650592825493946368000000000000000000 true
private noncomputable def ibox221 : Fin 4 → FixedTape.I := splitI ibox220 3 233466358062707111466830808989607458242560000000000000000000000000 false
private noncomputable def ibox222 : Fin 4 → FixedTape.I := splitI ibox220 3 233466358062707111466830808989607458242560000000000000000000000000 true
private noncomputable def ibox223 : Fin 4 → FixedTape.I := splitI ibox215 3 466932716125414222933661617979214916485120000000000000000000000000 true
private noncomputable def ibox224 : Fin 4 → FixedTape.I := splitI ibox223 0 4635070350702653636487198761650592825493946368000000000000000000 false
private noncomputable def ibox225 : Fin 4 → FixedTape.I := splitI ibox224 3 700399074188121334400492426968822374727680000000000000000000000000 false
private noncomputable def ibox226 : Fin 4 → FixedTape.I := splitI ibox224 3 700399074188121334400492426968822374727680000000000000000000000000 true
private noncomputable def ibox227 : Fin 4 → FixedTape.I := splitI ibox223 0 4635070350702653636487198761650592825493946368000000000000000000 true
private noncomputable def ibox228 : Fin 4 → FixedTape.I := splitI ibox227 3 700399074188121334400492426968822374727680000000000000000000000000 false
private noncomputable def ibox229 : Fin 4 → FixedTape.I := splitI ibox227 3 700399074188121334400492426968822374727680000000000000000000000000 true
private noncomputable def ibox230 : Fin 4 → FixedTape.I := splitI ibox214 3 933865432250828445867323235958429832970240000000000000000000000000 true
private noncomputable def ibox231 : Fin 4 → FixedTape.I := splitI ibox230 3 1400798148376242668800984853937644749455360000000000000000000000000 false
private noncomputable def ibox232 : Fin 4 → FixedTape.I := splitI ibox231 0 4635070350702653636487198761650592825493946368000000000000000000 false
private noncomputable def ibox233 : Fin 4 → FixedTape.I := splitI ibox232 3 1167331790313535557334154044948037291212800000000000000000000000000 false
private noncomputable def ibox234 : Fin 4 → FixedTape.I := splitI ibox232 3 1167331790313535557334154044948037291212800000000000000000000000000 true
private noncomputable def ibox235 : Fin 4 → FixedTape.I := splitI ibox231 0 4635070350702653636487198761650592825493946368000000000000000000 true
private noncomputable def ibox236 : Fin 4 → FixedTape.I := splitI ibox235 3 1167331790313535557334154044948037291212800000000000000000000000000 false
private noncomputable def ibox237 : Fin 4 → FixedTape.I := splitI ibox235 3 1167331790313535557334154044948037291212800000000000000000000000000 true
private noncomputable def ibox238 : Fin 4 → FixedTape.I := splitI ibox230 3 1400798148376242668800984853937644749455360000000000000000000000000 true
private noncomputable def ibox239 : Fin 4 → FixedTape.I := splitI ibox238 0 4635070350702653636487198761650592825493946368000000000000000000 false
private noncomputable def ibox240 : Fin 4 → FixedTape.I := splitI ibox239 3 1634264506438949780267815662927252207697920000000000000000000000000 false
private noncomputable def ibox241 : Fin 4 → FixedTape.I := splitI ibox239 3 1634264506438949780267815662927252207697920000000000000000000000000 true
private noncomputable def ibox242 : Fin 4 → FixedTape.I := splitI ibox238 0 4635070350702653636487198761650592825493946368000000000000000000 true
private noncomputable def ibox243 : Fin 4 → FixedTape.I := splitI ibox242 3 1634264506438949780267815662927252207697920000000000000000000000000 false
private noncomputable def ibox244 : Fin 4 → FixedTape.I := splitI ibox242 3 1634264506438949780267815662927252207697920000000000000000000000000 true
private noncomputable def ibox245 : Fin 4 → FixedTape.I := splitI ibox179 1 233466358062707111466830808989607458242560000000000000000000000000 true
private noncomputable def ibox246 : Fin 4 → FixedTape.I := splitI ibox245 0 4463401078454407205506191400107978276401577984000000000000000000 false
private noncomputable def ibox247 : Fin 4 → FixedTape.I := faceI ibox246 1 false
private noncomputable def ibox248 : Fin 4 → FixedTape.I := splitI ibox247 3 933865432250828445867323235958429832970240000000000000000000000000 false
private noncomputable def ibox249 : Fin 4 → FixedTape.I := splitI ibox247 3 933865432250828445867323235958429832970240000000000000000000000000 true
private noncomputable def ibox250 : Fin 4 → FixedTape.I := splitI ibox245 0 4463401078454407205506191400107978276401577984000000000000000000 true
private noncomputable def ibox251 : Fin 4 → FixedTape.I := faceI ibox250 1 false
private noncomputable def ibox252 : Fin 4 → FixedTape.I := splitI ibox251 3 933865432250828445867323235958429832970240000000000000000000000000 false
private noncomputable def ibox253 : Fin 4 → FixedTape.I := splitI ibox251 3 933865432250828445867323235958429832970240000000000000000000000000 true
private noncomputable def ibox254 : Fin 4 → FixedTape.I := splitI ibox178 1 466932716125414222933661617979214916485120000000000000000000000000 true
private noncomputable def ibox255 : Fin 4 → FixedTape.I := splitI ibox254 0 4463401078454407205506191400107978276401577984000000000000000000 false
private noncomputable def ibox256 : Fin 4 → FixedTape.I := faceI ibox255 1 false
private noncomputable def ibox257 : Fin 4 → FixedTape.I := splitI ibox254 0 4463401078454407205506191400107978276401577984000000000000000000 true
private noncomputable def ibox258 : Fin 4 → FixedTape.I := faceI ibox257 1 false
private noncomputable def ibox259 : Fin 4 → FixedTape.I := splitI ibox176 1 933865432250828445867323235958429832970240000000000000000000000000 true
private noncomputable def ibox260 : Fin 4 → FixedTape.I := faceI ibox259 3 false
private noncomputable def ibox261 : Fin 4 → FixedTape.I := splitI ibox260 0 4463401078454407205506191400107978276401577984000000000000000000 false
private noncomputable def ibox262 : Fin 4 → FixedTape.I := splitI ibox261 1 1400798148376242668800984853937644749455360000000000000000000000000 false
private noncomputable def ibox263 : Fin 4 → FixedTape.I := splitI ibox261 1 1400798148376242668800984853937644749455360000000000000000000000000 true
private noncomputable def ibox264 : Fin 4 → FixedTape.I := splitI ibox260 0 4463401078454407205506191400107978276401577984000000000000000000 true
private noncomputable def ibox265 : Fin 4 → FixedTape.I := splitI ibox264 1 1400798148376242668800984853937644749455360000000000000000000000000 false
private noncomputable def ibox266 : Fin 4 → FixedTape.I := splitI ibox264 1 1400798148376242668800984853937644749455360000000000000000000000000 true
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
private noncomputable def tree264 : TapeTree := .split 1 (((1400798148376242668800984853937644749455360000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree265 tree266
attribute [irreducible] tree264
private theorem accepted_264 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox264) tree264 = true := by
  simp only [tree264,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox264 1 (1400798148376242668800984853937644749455360000000000000000000000000 : Int) false,decode_split denominator ibox264 1 (1400798148376242668800984853937644749455360000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_265 h,accepted_266 h⟩
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
private noncomputable def tree262 : TapeTree := .centered (candidateRows ibox262) (candidateRows (FixedTape.midBox ibox262))
attribute [irreducible] tree262
private theorem sign_262 : 2*denominator*(computed denominator (FixedTape.midBox ibox262)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox262).gradient k).lo.natAbs ((computed denominator ibox262).gradient k).hi.natAbs : Int)*((ibox262 k).hi-(ibox262 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox262
    (computed denominator ibox262) (computed denominator (FixedTape.midBox ibox262))
    (by decide +kernel)
private theorem midpoint_even_262 : ∀ k, 2 ∣ (ibox262 k).lo+(ibox262 k).hi := by decide +kernel
private theorem accepted_262 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox262) tree262 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox262 midpoint_even_262
  simp only [tree262,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox262,candidate_valid h (FixedTape.midBox ibox262),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox262 212 (FixedTape.rowsAux denominator ibox262 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox262) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_262
private noncomputable def tree261 : TapeTree := .split 1 (((1400798148376242668800984853937644749455360000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree262 tree263
attribute [irreducible] tree261
private theorem accepted_261 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox261) tree261 = true := by
  simp only [tree261,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox261 1 (1400798148376242668800984853937644749455360000000000000000000000000 : Int) false,decode_split denominator ibox261 1 (1400798148376242668800984853937644749455360000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_262 h,accepted_263 h⟩
private noncomputable def tree260 : TapeTree := .split 0 (((4463401078454407205506191400107978276401577984000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree261 tree264
attribute [irreducible] tree260
private theorem accepted_260 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox260) tree260 = true := by
  simp only [tree260,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox260 0 (4463401078454407205506191400107978276401577984000000000000000000 : Int) false,decode_split denominator ibox260 0 (4463401078454407205506191400107978276401577984000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_261 h,accepted_264 h⟩
private noncomputable def tree259 : TapeTree := .face 3 false (candidateRows ibox259) tree260
attribute [irreducible] tree259
private theorem sign_259 : ((computed denominator ibox259).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_259 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox259) tree259 = true := by
  simp only [tree259,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox259,?_,accepted_260 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox259)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox259).gradient 3).hi) denominator_positive).1 sign_259
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
private noncomputable def tree257 : TapeTree := .face 1 false (candidateRows ibox257) tree258
attribute [irreducible] tree257
private theorem sign_257 : ((computed denominator ibox257).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_257 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox257) tree257 = true := by
  simp only [tree257,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox257,?_,accepted_258 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox257)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox257).gradient 1).hi) denominator_positive).1 sign_257
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
private noncomputable def tree255 : TapeTree := .face 1 false (candidateRows ibox255) tree256
attribute [irreducible] tree255
private theorem sign_255 : ((computed denominator ibox255).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_255 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox255) tree255 = true := by
  simp only [tree255,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox255,?_,accepted_256 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox255)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox255).gradient 1).hi) denominator_positive).1 sign_255
private noncomputable def tree254 : TapeTree := .split 0 (((4463401078454407205506191400107978276401577984000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree255 tree257
attribute [irreducible] tree254
private theorem accepted_254 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox254) tree254 = true := by
  simp only [tree254,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox254 0 (4463401078454407205506191400107978276401577984000000000000000000 : Int) false,decode_split denominator ibox254 0 (4463401078454407205506191400107978276401577984000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_255 h,accepted_257 h⟩
private noncomputable def tree253 : TapeTree := .centered (candidateRows ibox253) (candidateRows (FixedTape.midBox ibox253))
attribute [irreducible] tree253
private theorem sign_253 : 2*denominator*(computed denominator (FixedTape.midBox ibox253)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox253).gradient k).lo.natAbs ((computed denominator ibox253).gradient k).hi.natAbs : Int)*((ibox253 k).hi-(ibox253 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox253
    (computed denominator ibox253) (computed denominator (FixedTape.midBox ibox253))
    (by decide +kernel)
private theorem midpoint_even_253 : ∀ k, 2 ∣ (ibox253 k).lo+(ibox253 k).hi := by decide +kernel
private theorem accepted_253 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox253) tree253 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox253 midpoint_even_253
  simp only [tree253,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox253,candidate_valid h (FixedTape.midBox ibox253),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox253 212 (FixedTape.rowsAux denominator ibox253 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox253) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_253
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
private noncomputable def tree251 : TapeTree := .split 3 (((933865432250828445867323235958429832970240000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree252 tree253
attribute [irreducible] tree251
private theorem accepted_251 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox251) tree251 = true := by
  simp only [tree251,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox251 3 (933865432250828445867323235958429832970240000000000000000000000000 : Int) false,decode_split denominator ibox251 3 (933865432250828445867323235958429832970240000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_252 h,accepted_253 h⟩
private noncomputable def tree250 : TapeTree := .face 1 false (candidateRows ibox250) tree251
attribute [irreducible] tree250
private theorem sign_250 : ((computed denominator ibox250).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_250 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox250) tree250 = true := by
  simp only [tree250,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox250,?_,accepted_251 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox250)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox250).gradient 1).hi) denominator_positive).1 sign_250
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
private noncomputable def tree247 : TapeTree := .split 3 (((933865432250828445867323235958429832970240000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree248 tree249
attribute [irreducible] tree247
private theorem accepted_247 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox247) tree247 = true := by
  simp only [tree247,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox247 3 (933865432250828445867323235958429832970240000000000000000000000000 : Int) false,decode_split denominator ibox247 3 (933865432250828445867323235958429832970240000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_248 h,accepted_249 h⟩
private noncomputable def tree246 : TapeTree := .face 1 false (candidateRows ibox246) tree247
attribute [irreducible] tree246
private theorem sign_246 : ((computed denominator ibox246).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_246 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox246) tree246 = true := by
  simp only [tree246,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox246,?_,accepted_247 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox246)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox246).gradient 1).hi) denominator_positive).1 sign_246
private noncomputable def tree245 : TapeTree := .split 0 (((4463401078454407205506191400107978276401577984000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree246 tree250
attribute [irreducible] tree245
private theorem accepted_245 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox245) tree245 = true := by
  simp only [tree245,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox245 0 (4463401078454407205506191400107978276401577984000000000000000000 : Int) false,decode_split denominator ibox245 0 (4463401078454407205506191400107978276401577984000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_246 h,accepted_250 h⟩
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
private noncomputable def tree242 : TapeTree := .split 3 (((1634264506438949780267815662927252207697920000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree243 tree244
attribute [irreducible] tree242
private theorem accepted_242 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox242) tree242 = true := by
  simp only [tree242,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox242 3 (1634264506438949780267815662927252207697920000000000000000000000000 : Int) false,decode_split denominator ibox242 3 (1634264506438949780267815662927252207697920000000000000000000000000 : Int) true]
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
private noncomputable def tree239 : TapeTree := .split 3 (((1634264506438949780267815662927252207697920000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree240 tree241
attribute [irreducible] tree239
private theorem accepted_239 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox239) tree239 = true := by
  simp only [tree239,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox239 3 (1634264506438949780267815662927252207697920000000000000000000000000 : Int) false,decode_split denominator ibox239 3 (1634264506438949780267815662927252207697920000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_240 h,accepted_241 h⟩
private noncomputable def tree238 : TapeTree := .split 0 (((4635070350702653636487198761650592825493946368000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree239 tree242
attribute [irreducible] tree238
private theorem accepted_238 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox238) tree238 = true := by
  simp only [tree238,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox238 0 (4635070350702653636487198761650592825493946368000000000000000000 : Int) false,decode_split denominator ibox238 0 (4635070350702653636487198761650592825493946368000000000000000000 : Int) true]
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
private noncomputable def tree235 : TapeTree := .split 3 (((1167331790313535557334154044948037291212800000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree236 tree237
attribute [irreducible] tree235
private theorem accepted_235 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox235) tree235 = true := by
  simp only [tree235,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox235 3 (1167331790313535557334154044948037291212800000000000000000000000000 : Int) false,decode_split denominator ibox235 3 (1167331790313535557334154044948037291212800000000000000000000000000 : Int) true]
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
private noncomputable def tree232 : TapeTree := .split 3 (((1167331790313535557334154044948037291212800000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree233 tree234
attribute [irreducible] tree232
private theorem accepted_232 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox232) tree232 = true := by
  simp only [tree232,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox232 3 (1167331790313535557334154044948037291212800000000000000000000000000 : Int) false,decode_split denominator ibox232 3 (1167331790313535557334154044948037291212800000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_233 h,accepted_234 h⟩
private noncomputable def tree231 : TapeTree := .split 0 (((4635070350702653636487198761650592825493946368000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree232 tree235
attribute [irreducible] tree231
private theorem accepted_231 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox231) tree231 = true := by
  simp only [tree231,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox231 0 (4635070350702653636487198761650592825493946368000000000000000000 : Int) false,decode_split denominator ibox231 0 (4635070350702653636487198761650592825493946368000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_232 h,accepted_235 h⟩
private noncomputable def tree230 : TapeTree := .split 3 (((1400798148376242668800984853937644749455360000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree231 tree238
attribute [irreducible] tree230
private theorem accepted_230 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox230) tree230 = true := by
  simp only [tree230,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox230 3 (1400798148376242668800984853937644749455360000000000000000000000000 : Int) false,decode_split denominator ibox230 3 (1400798148376242668800984853937644749455360000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_231 h,accepted_238 h⟩
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
private noncomputable def tree227 : TapeTree := .split 3 (((700399074188121334400492426968822374727680000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree228 tree229
attribute [irreducible] tree227
private theorem accepted_227 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox227) tree227 = true := by
  simp only [tree227,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox227 3 (700399074188121334400492426968822374727680000000000000000000000000 : Int) false,decode_split denominator ibox227 3 (700399074188121334400492426968822374727680000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_228 h,accepted_229 h⟩
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
private noncomputable def tree225 : TapeTree := .centered (candidateRows ibox225) (candidateRows (FixedTape.midBox ibox225))
attribute [irreducible] tree225
private theorem sign_225 : 2*denominator*(computed denominator (FixedTape.midBox ibox225)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox225).gradient k).lo.natAbs ((computed denominator ibox225).gradient k).hi.natAbs : Int)*((ibox225 k).hi-(ibox225 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox225
    (computed denominator ibox225) (computed denominator (FixedTape.midBox ibox225))
    (by decide +kernel)
private theorem midpoint_even_225 : ∀ k, 2 ∣ (ibox225 k).lo+(ibox225 k).hi := by decide +kernel
private theorem accepted_225 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox225) tree225 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox225 midpoint_even_225
  simp only [tree225,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox225,candidate_valid h (FixedTape.midBox ibox225),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox225 212 (FixedTape.rowsAux denominator ibox225 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox225) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_225
private noncomputable def tree224 : TapeTree := .split 3 (((700399074188121334400492426968822374727680000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree225 tree226
attribute [irreducible] tree224
private theorem accepted_224 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox224) tree224 = true := by
  simp only [tree224,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox224 3 (700399074188121334400492426968822374727680000000000000000000000000 : Int) false,decode_split denominator ibox224 3 (700399074188121334400492426968822374727680000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_225 h,accepted_226 h⟩
private noncomputable def tree223 : TapeTree := .split 0 (((4635070350702653636487198761650592825493946368000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree224 tree227
attribute [irreducible] tree223
private theorem accepted_223 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox223) tree223 = true := by
  simp only [tree223,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox223 0 (4635070350702653636487198761650592825493946368000000000000000000 : Int) false,decode_split denominator ibox223 0 (4635070350702653636487198761650592825493946368000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_224 h,accepted_227 h⟩
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
private noncomputable def tree221 : TapeTree := .centered (candidateRows ibox221) (candidateRows (FixedTape.midBox ibox221))
attribute [irreducible] tree221
private theorem sign_221 : 2*denominator*(computed denominator (FixedTape.midBox ibox221)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox221).gradient k).lo.natAbs ((computed denominator ibox221).gradient k).hi.natAbs : Int)*((ibox221 k).hi-(ibox221 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox221
    (computed denominator ibox221) (computed denominator (FixedTape.midBox ibox221))
    (by decide +kernel)
private theorem midpoint_even_221 : ∀ k, 2 ∣ (ibox221 k).lo+(ibox221 k).hi := by decide +kernel
private theorem accepted_221 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox221) tree221 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox221 midpoint_even_221
  simp only [tree221,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox221,candidate_valid h (FixedTape.midBox ibox221),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox221 212 (FixedTape.rowsAux denominator ibox221 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox221) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_221
private noncomputable def tree220 : TapeTree := .split 3 (((233466358062707111466830808989607458242560000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree221 tree222
attribute [irreducible] tree220
private theorem accepted_220 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox220) tree220 = true := by
  simp only [tree220,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox220 3 (233466358062707111466830808989607458242560000000000000000000000000 : Int) false,decode_split denominator ibox220 3 (233466358062707111466830808989607458242560000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_221 h,accepted_222 h⟩
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
private noncomputable def tree218 : TapeTree := .centered (candidateRows ibox218) (candidateRows (FixedTape.midBox ibox218))
attribute [irreducible] tree218
private theorem sign_218 : 2*denominator*(computed denominator (FixedTape.midBox ibox218)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox218).gradient k).lo.natAbs ((computed denominator ibox218).gradient k).hi.natAbs : Int)*((ibox218 k).hi-(ibox218 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox218
    (computed denominator ibox218) (computed denominator (FixedTape.midBox ibox218))
    (by decide +kernel)
private theorem midpoint_even_218 : ∀ k, 2 ∣ (ibox218 k).lo+(ibox218 k).hi := by decide +kernel
private theorem accepted_218 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox218) tree218 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox218 midpoint_even_218
  simp only [tree218,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox218,candidate_valid h (FixedTape.midBox ibox218),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox218 212 (FixedTape.rowsAux denominator ibox218 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox218) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_218
private noncomputable def tree217 : TapeTree := .split 3 (((233466358062707111466830808989607458242560000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree218 tree219
attribute [irreducible] tree217
private theorem accepted_217 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox217) tree217 = true := by
  simp only [tree217,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox217 3 (233466358062707111466830808989607458242560000000000000000000000000 : Int) false,decode_split denominator ibox217 3 (233466358062707111466830808989607458242560000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_218 h,accepted_219 h⟩
private noncomputable def tree216 : TapeTree := .split 0 (((4635070350702653636487198761650592825493946368000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree217 tree220
attribute [irreducible] tree216
private theorem accepted_216 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox216) tree216 = true := by
  simp only [tree216,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox216 0 (4635070350702653636487198761650592825493946368000000000000000000 : Int) false,decode_split denominator ibox216 0 (4635070350702653636487198761650592825493946368000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_217 h,accepted_220 h⟩
private noncomputable def tree215 : TapeTree := .split 3 (((466932716125414222933661617979214916485120000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree216 tree223
attribute [irreducible] tree215
private theorem accepted_215 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox215) tree215 = true := by
  simp only [tree215,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox215 3 (466932716125414222933661617979214916485120000000000000000000000000 : Int) false,decode_split denominator ibox215 3 (466932716125414222933661617979214916485120000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_216 h,accepted_223 h⟩
private noncomputable def tree214 : TapeTree := .split 3 (((933865432250828445867323235958429832970240000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree215 tree230
attribute [irreducible] tree214
private theorem accepted_214 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox214) tree214 = true := by
  simp only [tree214,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox214 3 (933865432250828445867323235958429832970240000000000000000000000000 : Int) false,decode_split denominator ibox214 3 (933865432250828445867323235958429832970240000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_215 h,accepted_230 h⟩
private noncomputable def tree213 : TapeTree := .face 1 false (candidateRows ibox213) tree214
attribute [irreducible] tree213
private theorem sign_213 : ((computed denominator ibox213).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_213 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox213) tree213 = true := by
  simp only [tree213,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox213,?_,accepted_214 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox213)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox213).gradient 1).hi) denominator_positive).1 sign_213
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
private noncomputable def tree210 : TapeTree := .split 3 (((1634264506438949780267815662927252207697920000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree211 tree212
attribute [irreducible] tree210
private theorem accepted_210 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox210) tree210 = true := by
  simp only [tree210,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox210 3 (1634264506438949780267815662927252207697920000000000000000000000000 : Int) false,decode_split denominator ibox210 3 (1634264506438949780267815662927252207697920000000000000000000000000 : Int) true]
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
private noncomputable def tree207 : TapeTree := .split 3 (((1634264506438949780267815662927252207697920000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree208 tree209
attribute [irreducible] tree207
private theorem accepted_207 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox207) tree207 = true := by
  simp only [tree207,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox207 3 (1634264506438949780267815662927252207697920000000000000000000000000 : Int) false,decode_split denominator ibox207 3 (1634264506438949780267815662927252207697920000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_208 h,accepted_209 h⟩
private noncomputable def tree206 : TapeTree := .split 0 (((4291731806206160774525184038565363727309209600000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree207 tree210
attribute [irreducible] tree206
private theorem accepted_206 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox206) tree206 = true := by
  simp only [tree206,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox206 0 (4291731806206160774525184038565363727309209600000000000000000000 : Int) false,decode_split denominator ibox206 0 (4291731806206160774525184038565363727309209600000000000000000000 : Int) true]
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
private noncomputable def tree203 : TapeTree := .split 3 (((1167331790313535557334154044948037291212800000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree204 tree205
attribute [irreducible] tree203
private theorem accepted_203 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox203) tree203 = true := by
  simp only [tree203,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox203 3 (1167331790313535557334154044948037291212800000000000000000000000000 : Int) false,decode_split denominator ibox203 3 (1167331790313535557334154044948037291212800000000000000000000000000 : Int) true]
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
private noncomputable def tree200 : TapeTree := .split 3 (((1167331790313535557334154044948037291212800000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree201 tree202
attribute [irreducible] tree200
private theorem accepted_200 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox200) tree200 = true := by
  simp only [tree200,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox200 3 (1167331790313535557334154044948037291212800000000000000000000000000 : Int) false,decode_split denominator ibox200 3 (1167331790313535557334154044948037291212800000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_201 h,accepted_202 h⟩
private noncomputable def tree199 : TapeTree := .split 0 (((4291731806206160774525184038565363727309209600000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree200 tree203
attribute [irreducible] tree199
private theorem accepted_199 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox199) tree199 = true := by
  simp only [tree199,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox199 0 (4291731806206160774525184038565363727309209600000000000000000000 : Int) false,decode_split denominator ibox199 0 (4291731806206160774525184038565363727309209600000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_200 h,accepted_203 h⟩
private noncomputable def tree198 : TapeTree := .split 3 (((1400798148376242668800984853937644749455360000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree199 tree206
attribute [irreducible] tree198
private theorem accepted_198 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox198) tree198 = true := by
  simp only [tree198,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox198 3 (1400798148376242668800984853937644749455360000000000000000000000000 : Int) false,decode_split denominator ibox198 3 (1400798148376242668800984853937644749455360000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_199 h,accepted_206 h⟩
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
private noncomputable def tree195 : TapeTree := .split 3 (((700399074188121334400492426968822374727680000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree196 tree197
attribute [irreducible] tree195
private theorem accepted_195 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox195) tree195 = true := by
  simp only [tree195,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox195 3 (700399074188121334400492426968822374727680000000000000000000000000 : Int) false,decode_split denominator ibox195 3 (700399074188121334400492426968822374727680000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_196 h,accepted_197 h⟩
private noncomputable def tree194 : TapeTree := .centered (candidateRows ibox194) (candidateRows (FixedTape.midBox ibox194))
attribute [irreducible] tree194
private theorem sign_194 : 2*denominator*(computed denominator (FixedTape.midBox ibox194)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox194).gradient k).lo.natAbs ((computed denominator ibox194).gradient k).hi.natAbs : Int)*((ibox194 k).hi-(ibox194 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox194
    (computed denominator ibox194) (computed denominator (FixedTape.midBox ibox194))
    (by decide +kernel)
private theorem midpoint_even_194 : ∀ k, 2 ∣ (ibox194 k).lo+(ibox194 k).hi := by decide +kernel
private theorem accepted_194 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox194) tree194 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox194 midpoint_even_194
  simp only [tree194,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox194,candidate_valid h (FixedTape.midBox ibox194),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox194 212 (FixedTape.rowsAux denominator ibox194 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox194) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_194
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
private noncomputable def tree192 : TapeTree := .split 3 (((700399074188121334400492426968822374727680000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree193 tree194
attribute [irreducible] tree192
private theorem accepted_192 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox192) tree192 = true := by
  simp only [tree192,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox192 3 (700399074188121334400492426968822374727680000000000000000000000000 : Int) false,decode_split denominator ibox192 3 (700399074188121334400492426968822374727680000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_193 h,accepted_194 h⟩
private noncomputable def tree191 : TapeTree := .split 0 (((4291731806206160774525184038565363727309209600000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree192 tree195
attribute [irreducible] tree191
private theorem accepted_191 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox191) tree191 = true := by
  simp only [tree191,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox191 0 (4291731806206160774525184038565363727309209600000000000000000000 : Int) false,decode_split denominator ibox191 0 (4291731806206160774525184038565363727309209600000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_192 h,accepted_195 h⟩
private noncomputable def tree190 : TapeTree := .centered (candidateRows ibox190) (candidateRows (FixedTape.midBox ibox190))
attribute [irreducible] tree190
private theorem sign_190 : 2*denominator*(computed denominator (FixedTape.midBox ibox190)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox190).gradient k).lo.natAbs ((computed denominator ibox190).gradient k).hi.natAbs : Int)*((ibox190 k).hi-(ibox190 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox190
    (computed denominator ibox190) (computed denominator (FixedTape.midBox ibox190))
    (by decide +kernel)
private theorem midpoint_even_190 : ∀ k, 2 ∣ (ibox190 k).lo+(ibox190 k).hi := by decide +kernel
private theorem accepted_190 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox190) tree190 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox190 midpoint_even_190
  simp only [tree190,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox190,candidate_valid h (FixedTape.midBox ibox190),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox190 212 (FixedTape.rowsAux denominator ibox190 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox190) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_190
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
private noncomputable def tree188 : TapeTree := .split 3 (((233466358062707111466830808989607458242560000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree189 tree190
attribute [irreducible] tree188
private theorem accepted_188 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox188) tree188 = true := by
  simp only [tree188,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox188 3 (233466358062707111466830808989607458242560000000000000000000000000 : Int) false,decode_split denominator ibox188 3 (233466358062707111466830808989607458242560000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_189 h,accepted_190 h⟩
private noncomputable def tree187 : TapeTree := .centered (candidateRows ibox187) (candidateRows (FixedTape.midBox ibox187))
attribute [irreducible] tree187
private theorem sign_187 : 2*denominator*(computed denominator (FixedTape.midBox ibox187)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox187).gradient k).lo.natAbs ((computed denominator ibox187).gradient k).hi.natAbs : Int)*((ibox187 k).hi-(ibox187 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox187
    (computed denominator ibox187) (computed denominator (FixedTape.midBox ibox187))
    (by decide +kernel)
private theorem midpoint_even_187 : ∀ k, 2 ∣ (ibox187 k).lo+(ibox187 k).hi := by decide +kernel
private theorem accepted_187 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox187) tree187 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox187 midpoint_even_187
  simp only [tree187,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox187,candidate_valid h (FixedTape.midBox ibox187),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox187 212 (FixedTape.rowsAux denominator ibox187 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox187) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_187
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
private noncomputable def tree185 : TapeTree := .split 3 (((233466358062707111466830808989607458242560000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree186 tree187
attribute [irreducible] tree185
private theorem accepted_185 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox185) tree185 = true := by
  simp only [tree185,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox185 3 (233466358062707111466830808989607458242560000000000000000000000000 : Int) false,decode_split denominator ibox185 3 (233466358062707111466830808989607458242560000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_186 h,accepted_187 h⟩
private noncomputable def tree184 : TapeTree := .split 0 (((4291731806206160774525184038565363727309209600000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree185 tree188
attribute [irreducible] tree184
private theorem accepted_184 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox184) tree184 = true := by
  simp only [tree184,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox184 0 (4291731806206160774525184038565363727309209600000000000000000000 : Int) false,decode_split denominator ibox184 0 (4291731806206160774525184038565363727309209600000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_185 h,accepted_188 h⟩
private noncomputable def tree183 : TapeTree := .split 3 (((466932716125414222933661617979214916485120000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree184 tree191
attribute [irreducible] tree183
private theorem accepted_183 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox183) tree183 = true := by
  simp only [tree183,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox183 3 (466932716125414222933661617979214916485120000000000000000000000000 : Int) false,decode_split denominator ibox183 3 (466932716125414222933661617979214916485120000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_184 h,accepted_191 h⟩
private noncomputable def tree182 : TapeTree := .split 3 (((933865432250828445867323235958429832970240000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree183 tree198
attribute [irreducible] tree182
private theorem accepted_182 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox182) tree182 = true := by
  simp only [tree182,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox182 3 (933865432250828445867323235958429832970240000000000000000000000000 : Int) false,decode_split denominator ibox182 3 (933865432250828445867323235958429832970240000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_183 h,accepted_198 h⟩
private noncomputable def tree181 : TapeTree := .face 1 false (candidateRows ibox181) tree182
attribute [irreducible] tree181
private theorem sign_181 : ((computed denominator ibox181).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_181 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox181) tree181 = true := by
  simp only [tree181,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox181,?_,accepted_182 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox181)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox181).gradient 1).hi) denominator_positive).1 sign_181
private noncomputable def tree180 : TapeTree := .split 0 (((4463401078454407205506191400107978276401577984000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree181 tree213
attribute [irreducible] tree180
private theorem accepted_180 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox180) tree180 = true := by
  simp only [tree180,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox180 0 (4463401078454407205506191400107978276401577984000000000000000000 : Int) false,decode_split denominator ibox180 0 (4463401078454407205506191400107978276401577984000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_181 h,accepted_213 h⟩
private noncomputable def tree179 : TapeTree := .split 1 (((233466358062707111466830808989607458242560000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree180 tree245
attribute [irreducible] tree179
private theorem accepted_179 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox179) tree179 = true := by
  simp only [tree179,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox179 1 (233466358062707111466830808989607458242560000000000000000000000000 : Int) false,decode_split denominator ibox179 1 (233466358062707111466830808989607458242560000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_180 h,accepted_245 h⟩
private noncomputable def tree178 : TapeTree := .split 1 (((466932716125414222933661617979214916485120000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree179 tree254
attribute [irreducible] tree178
private theorem accepted_178 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox178) tree178 = true := by
  simp only [tree178,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox178 1 (466932716125414222933661617979214916485120000000000000000000000000 : Int) false,decode_split denominator ibox178 1 (466932716125414222933661617979214916485120000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_179 h,accepted_254 h⟩
private noncomputable def tree177 : TapeTree := .face 2 true (candidateRows ibox177) tree178
attribute [irreducible] tree177
private theorem sign_177 : 0 ≤ ((computed denominator ibox177).gradient 2).lo := by decide +kernel
private theorem accepted_177 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox177) tree177 = true := by
  simp only [tree177,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox177,?_,accepted_178 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox177)).gradient 2).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox177).gradient 2).lo) denominator_positive).2 sign_177
private noncomputable def tree176 : TapeTree := .split 1 (((933865432250828445867323235958429832970240000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree177 tree259
attribute [irreducible] tree176
private theorem accepted_176 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox176) tree176 = true := by
  simp only [tree176,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox176 1 (933865432250828445867323235958429832970240000000000000000000000000 : Int) false,decode_split denominator ibox176 1 (933865432250828445867323235958429832970240000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_177 h,accepted_259 h⟩
private noncomputable def tree175 : TapeTree := .centered (candidateRows ibox175) (candidateRows (FixedTape.midBox ibox175))
attribute [irreducible] tree175
private theorem sign_175 : 2*denominator*(computed denominator (FixedTape.midBox ibox175)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox175).gradient k).lo.natAbs ((computed denominator ibox175).gradient k).hi.natAbs : Int)*((ibox175 k).hi-(ibox175 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox175
    (computed denominator ibox175) (computed denominator (FixedTape.midBox ibox175))
    (by decide +kernel)
private theorem midpoint_even_175 : ∀ k, 2 ∣ (ibox175 k).lo+(ibox175 k).hi := by decide +kernel
private theorem accepted_175 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox175) tree175 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox175 midpoint_even_175
  simp only [tree175,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox175,candidate_valid h (FixedTape.midBox ibox175),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox175 212 (FixedTape.rowsAux denominator ibox175 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox175) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_175
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
private noncomputable def tree173 : TapeTree := .split 1 (((933865432250828445867323235958429832970240000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree174 tree175
attribute [irreducible] tree173
private theorem accepted_173 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox173) tree173 = true := by
  simp only [tree173,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox173 1 (933865432250828445867323235958429832970240000000000000000000000000 : Int) false,decode_split denominator ibox173 1 (933865432250828445867323235958429832970240000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_174 h,accepted_175 h⟩
private noncomputable def tree172 : TapeTree := .centered (candidateRows ibox172) (candidateRows (FixedTape.midBox ibox172))
attribute [irreducible] tree172
private theorem sign_172 : 2*denominator*(computed denominator (FixedTape.midBox ibox172)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox172).gradient k).lo.natAbs ((computed denominator ibox172).gradient k).hi.natAbs : Int)*((ibox172 k).hi-(ibox172 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox172
    (computed denominator ibox172) (computed denominator (FixedTape.midBox ibox172))
    (by decide +kernel)
private theorem midpoint_even_172 : ∀ k, 2 ∣ (ibox172 k).lo+(ibox172 k).hi := by decide +kernel
private theorem accepted_172 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox172) tree172 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox172 midpoint_even_172
  simp only [tree172,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox172,candidate_valid h (FixedTape.midBox ibox172),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox172 212 (FixedTape.rowsAux denominator ibox172 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox172) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_172
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
private noncomputable def tree170 : TapeTree := .split 1 (((933865432250828445867323235958429832970240000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree171 tree172
attribute [irreducible] tree170
private theorem accepted_170 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox170) tree170 = true := by
  simp only [tree170,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox170 1 (933865432250828445867323235958429832970240000000000000000000000000 : Int) false,decode_split denominator ibox170 1 (933865432250828445867323235958429832970240000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_171 h,accepted_172 h⟩
private noncomputable def tree169 : TapeTree := .split 0 (((4463401078454407205506191400107978276401577984000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree170 tree173
attribute [irreducible] tree169
private theorem accepted_169 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox169) tree169 = true := by
  simp only [tree169,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox169 0 (4463401078454407205506191400107978276401577984000000000000000000 : Int) false,decode_split denominator ibox169 0 (4463401078454407205506191400107978276401577984000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_170 h,accepted_173 h⟩
private noncomputable def tree168 : TapeTree := .face 3 false (candidateRows ibox168) tree169
attribute [irreducible] tree168
private theorem sign_168 : ((computed denominator ibox168).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_168 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox168) tree168 = true := by
  simp only [tree168,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox168,?_,accepted_169 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox168)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox168).gradient 3).hi) denominator_positive).1 sign_168
private noncomputable def tree167 : TapeTree := .split 2 (((1400798148376242668800984853937644749455360000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree168 tree176
attribute [irreducible] tree167
private theorem accepted_167 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox167) tree167 = true := by
  simp only [tree167,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox167 2 (1400798148376242668800984853937644749455360000000000000000000000000 : Int) false,decode_split denominator ibox167 2 (1400798148376242668800984853937644749455360000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_168 h,accepted_176 h⟩
private noncomputable def tree166 : TapeTree := .centered (candidateRows ibox166) (candidateRows (FixedTape.midBox ibox166))
attribute [irreducible] tree166
private theorem sign_166 : 2*denominator*(computed denominator (FixedTape.midBox ibox166)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox166).gradient k).lo.natAbs ((computed denominator ibox166).gradient k).hi.natAbs : Int)*((ibox166 k).hi-(ibox166 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox166
    (computed denominator ibox166) (computed denominator (FixedTape.midBox ibox166))
    (by decide +kernel)
private theorem midpoint_even_166 : ∀ k, 2 ∣ (ibox166 k).lo+(ibox166 k).hi := by decide +kernel
private theorem accepted_166 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox166) tree166 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox166 midpoint_even_166
  simp only [tree166,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox166,candidate_valid h (FixedTape.midBox ibox166),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox166 212 (FixedTape.rowsAux denominator ibox166 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox166) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_166
private noncomputable def tree165 : TapeTree := .centered (candidateRows ibox165) (candidateRows (FixedTape.midBox ibox165))
attribute [irreducible] tree165
private theorem sign_165 : 2*denominator*(computed denominator (FixedTape.midBox ibox165)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox165).gradient k).lo.natAbs ((computed denominator ibox165).gradient k).hi.natAbs : Int)*((ibox165 k).hi-(ibox165 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox165
    (computed denominator ibox165) (computed denominator (FixedTape.midBox ibox165))
    (by decide +kernel)
private theorem midpoint_even_165 : ∀ k, 2 ∣ (ibox165 k).lo+(ibox165 k).hi := by decide +kernel
private theorem accepted_165 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox165) tree165 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox165 midpoint_even_165
  simp only [tree165,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox165,candidate_valid h (FixedTape.midBox ibox165),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox165 212 (FixedTape.rowsAux denominator ibox165 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox165) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_165
private noncomputable def tree164 : TapeTree := .split 1 (((1400798148376242668800984853937644749455360000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree165 tree166
attribute [irreducible] tree164
private theorem accepted_164 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox164) tree164 = true := by
  simp only [tree164,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox164 1 (1400798148376242668800984853937644749455360000000000000000000000000 : Int) false,decode_split denominator ibox164 1 (1400798148376242668800984853937644749455360000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_165 h,accepted_166 h⟩
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
private noncomputable def tree161 : TapeTree := .split 1 (((1400798148376242668800984853937644749455360000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree162 tree163
attribute [irreducible] tree161
private theorem accepted_161 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox161) tree161 = true := by
  simp only [tree161,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox161 1 (1400798148376242668800984853937644749455360000000000000000000000000 : Int) false,decode_split denominator ibox161 1 (1400798148376242668800984853937644749455360000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_162 h,accepted_163 h⟩
private noncomputable def tree160 : TapeTree := .split 0 (((3776723989461421481582161953937520080032104448000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree161 tree164
attribute [irreducible] tree160
private theorem accepted_160 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox160) tree160 = true := by
  simp only [tree160,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox160 0 (3776723989461421481582161953937520080032104448000000000000000000 : Int) false,decode_split denominator ibox160 0 (3776723989461421481582161953937520080032104448000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_161 h,accepted_164 h⟩
private noncomputable def tree159 : TapeTree := .face 3 false (candidateRows ibox159) tree160
attribute [irreducible] tree159
private theorem sign_159 : ((computed denominator ibox159).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_159 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox159) tree159 = true := by
  simp only [tree159,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox159,?_,accepted_160 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox159)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox159).gradient 3).hi) denominator_positive).1 sign_159
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
private noncomputable def tree157 : TapeTree := .face 1 false (candidateRows ibox157) tree158
attribute [irreducible] tree157
private theorem sign_157 : ((computed denominator ibox157).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_157 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox157) tree157 = true := by
  simp only [tree157,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox157,?_,accepted_158 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox157)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox157).gradient 1).hi) denominator_positive).1 sign_157
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
private noncomputable def tree155 : TapeTree := .face 1 false (candidateRows ibox155) tree156
attribute [irreducible] tree155
private theorem sign_155 : ((computed denominator ibox155).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_155 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox155) tree155 = true := by
  simp only [tree155,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox155,?_,accepted_156 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox155)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox155).gradient 1).hi) denominator_positive).1 sign_155
private noncomputable def tree154 : TapeTree := .split 0 (((3776723989461421481582161953937520080032104448000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree155 tree157
attribute [irreducible] tree154
private theorem accepted_154 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox154) tree154 = true := by
  simp only [tree154,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox154 0 (3776723989461421481582161953937520080032104448000000000000000000 : Int) false,decode_split denominator ibox154 0 (3776723989461421481582161953937520080032104448000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_155 h,accepted_157 h⟩
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
private noncomputable def tree151 : TapeTree := .split 3 (((933865432250828445867323235958429832970240000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree152 tree153
attribute [irreducible] tree151
private theorem accepted_151 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox151) tree151 = true := by
  simp only [tree151,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox151 3 (933865432250828445867323235958429832970240000000000000000000000000 : Int) false,decode_split denominator ibox151 3 (933865432250828445867323235958429832970240000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_152 h,accepted_153 h⟩
private noncomputable def tree150 : TapeTree := .face 1 false (candidateRows ibox150) tree151
attribute [irreducible] tree150
private theorem sign_150 : ((computed denominator ibox150).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_150 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox150) tree150 = true := by
  simp only [tree150,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox150,?_,accepted_151 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox150)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox150).gradient 1).hi) denominator_positive).1 sign_150
private noncomputable def tree149 : TapeTree := .centered (candidateRows ibox149) (candidateRows (FixedTape.midBox ibox149))
attribute [irreducible] tree149
private theorem sign_149 : 2*denominator*(computed denominator (FixedTape.midBox ibox149)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox149).gradient k).lo.natAbs ((computed denominator ibox149).gradient k).hi.natAbs : Int)*((ibox149 k).hi-(ibox149 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox149
    (computed denominator ibox149) (computed denominator (FixedTape.midBox ibox149))
    (by decide +kernel)
private theorem midpoint_even_149 : ∀ k, 2 ∣ (ibox149 k).lo+(ibox149 k).hi := by decide +kernel
private theorem accepted_149 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox149) tree149 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox149 midpoint_even_149
  simp only [tree149,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox149,candidate_valid h (FixedTape.midBox ibox149),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox149 212 (FixedTape.rowsAux denominator ibox149 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox149) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_149
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
private noncomputable def tree147 : TapeTree := .split 3 (((933865432250828445867323235958429832970240000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree148 tree149
attribute [irreducible] tree147
private theorem accepted_147 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox147) tree147 = true := by
  simp only [tree147,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox147 3 (933865432250828445867323235958429832970240000000000000000000000000 : Int) false,decode_split denominator ibox147 3 (933865432250828445867323235958429832970240000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_148 h,accepted_149 h⟩
private noncomputable def tree146 : TapeTree := .face 1 false (candidateRows ibox146) tree147
attribute [irreducible] tree146
private theorem sign_146 : ((computed denominator ibox146).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_146 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox146) tree146 = true := by
  simp only [tree146,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox146,?_,accepted_147 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox146)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox146).gradient 1).hi) denominator_positive).1 sign_146
private noncomputable def tree145 : TapeTree := .split 0 (((3776723989461421481582161953937520080032104448000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree146 tree150
attribute [irreducible] tree145
private theorem accepted_145 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox145) tree145 = true := by
  simp only [tree145,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox145 0 (3776723989461421481582161953937520080032104448000000000000000000 : Int) false,decode_split denominator ibox145 0 (3776723989461421481582161953937520080032104448000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_146 h,accepted_150 h⟩
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
private noncomputable def tree142 : TapeTree := .split 3 (((1634264506438949780267815662927252207697920000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree143 tree144
attribute [irreducible] tree142
private theorem accepted_142 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox142) tree142 = true := by
  simp only [tree142,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox142 3 (1634264506438949780267815662927252207697920000000000000000000000000 : Int) false,decode_split denominator ibox142 3 (1634264506438949780267815662927252207697920000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_143 h,accepted_144 h⟩
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
private noncomputable def tree139 : TapeTree := .split 3 (((1634264506438949780267815662927252207697920000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree140 tree141
attribute [irreducible] tree139
private theorem accepted_139 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox139) tree139 = true := by
  simp only [tree139,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox139 3 (1634264506438949780267815662927252207697920000000000000000000000000 : Int) false,decode_split denominator ibox139 3 (1634264506438949780267815662927252207697920000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_140 h,accepted_141 h⟩
private noncomputable def tree138 : TapeTree := .split 0 (((3948393261709667912563169315480134629124472832000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree139 tree142
attribute [irreducible] tree138
private theorem accepted_138 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox138) tree138 = true := by
  simp only [tree138,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox138 0 (3948393261709667912563169315480134629124472832000000000000000000 : Int) false,decode_split denominator ibox138 0 (3948393261709667912563169315480134629124472832000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_139 h,accepted_142 h⟩
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
private noncomputable def tree135 : TapeTree := .split 3 (((1167331790313535557334154044948037291212800000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree136 tree137
attribute [irreducible] tree135
private theorem accepted_135 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox135) tree135 = true := by
  simp only [tree135,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox135 3 (1167331790313535557334154044948037291212800000000000000000000000000 : Int) false,decode_split denominator ibox135 3 (1167331790313535557334154044948037291212800000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_136 h,accepted_137 h⟩
private noncomputable def tree134 : TapeTree := .centered (candidateRows ibox134) (candidateRows (FixedTape.midBox ibox134))
attribute [irreducible] tree134
private theorem sign_134 : 2*denominator*(computed denominator (FixedTape.midBox ibox134)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox134).gradient k).lo.natAbs ((computed denominator ibox134).gradient k).hi.natAbs : Int)*((ibox134 k).hi-(ibox134 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox134
    (computed denominator ibox134) (computed denominator (FixedTape.midBox ibox134))
    (by decide +kernel)
private theorem midpoint_even_134 : ∀ k, 2 ∣ (ibox134 k).lo+(ibox134 k).hi := by decide +kernel
private theorem accepted_134 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox134) tree134 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox134 midpoint_even_134
  simp only [tree134,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox134,candidate_valid h (FixedTape.midBox ibox134),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox134 212 (FixedTape.rowsAux denominator ibox134 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox134) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_134
private noncomputable def tree133 : TapeTree := .centered (candidateRows ibox133) (candidateRows (FixedTape.midBox ibox133))
attribute [irreducible] tree133
private theorem sign_133 : 2*denominator*(computed denominator (FixedTape.midBox ibox133)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox133).gradient k).lo.natAbs ((computed denominator ibox133).gradient k).hi.natAbs : Int)*((ibox133 k).hi-(ibox133 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox133
    (computed denominator ibox133) (computed denominator (FixedTape.midBox ibox133))
    (by decide +kernel)
private theorem midpoint_even_133 : ∀ k, 2 ∣ (ibox133 k).lo+(ibox133 k).hi := by decide +kernel
private theorem accepted_133 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox133) tree133 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox133 midpoint_even_133
  simp only [tree133,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox133,candidate_valid h (FixedTape.midBox ibox133),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox133 212 (FixedTape.rowsAux denominator ibox133 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox133) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_133
private noncomputable def tree132 : TapeTree := .split 0 (((3862558625585544697072665634708827354578288640000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree133 tree134
attribute [irreducible] tree132
private theorem accepted_132 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox132) tree132 = true := by
  simp only [tree132,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox132 0 (3862558625585544697072665634708827354578288640000000000000000000 : Int) false,decode_split denominator ibox132 0 (3862558625585544697072665634708827354578288640000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_133 h,accepted_134 h⟩
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
private noncomputable def tree129 : TapeTree := .split 0 (((3862558625585544697072665634708827354578288640000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree130 tree131
attribute [irreducible] tree129
private theorem accepted_129 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox129) tree129 = true := by
  simp only [tree129,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox129 0 (3862558625585544697072665634708827354578288640000000000000000000 : Int) false,decode_split denominator ibox129 0 (3862558625585544697072665634708827354578288640000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_130 h,accepted_131 h⟩
private noncomputable def tree128 : TapeTree := .split 3 (((1167331790313535557334154044948037291212800000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree129 tree132
attribute [irreducible] tree128
private theorem accepted_128 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox128) tree128 = true := by
  simp only [tree128,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox128 3 (1167331790313535557334154044948037291212800000000000000000000000000 : Int) false,decode_split denominator ibox128 3 (1167331790313535557334154044948037291212800000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_129 h,accepted_132 h⟩
private noncomputable def tree127 : TapeTree := .split 0 (((3948393261709667912563169315480134629124472832000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree128 tree135
attribute [irreducible] tree127
private theorem accepted_127 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox127) tree127 = true := by
  simp only [tree127,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox127 0 (3948393261709667912563169315480134629124472832000000000000000000 : Int) false,decode_split denominator ibox127 0 (3948393261709667912563169315480134629124472832000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_128 h,accepted_135 h⟩
private noncomputable def tree126 : TapeTree := .split 3 (((1400798148376242668800984853937644749455360000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree127 tree138
attribute [irreducible] tree126
private theorem accepted_126 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox126) tree126 = true := by
  simp only [tree126,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox126 3 (1400798148376242668800984853937644749455360000000000000000000000000 : Int) false,decode_split denominator ibox126 3 (1400798148376242668800984853937644749455360000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_127 h,accepted_138 h⟩
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
private noncomputable def tree123 : TapeTree := .split 3 (((700399074188121334400492426968822374727680000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree124 tree125
attribute [irreducible] tree123
private theorem accepted_123 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox123) tree123 = true := by
  simp only [tree123,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox123 3 (700399074188121334400492426968822374727680000000000000000000000000 : Int) false,decode_split denominator ibox123 3 (700399074188121334400492426968822374727680000000000000000000000000 : Int) true]
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
private noncomputable def tree120 : TapeTree := .split 0 (((3862558625585544697072665634708827354578288640000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree121 tree122
attribute [irreducible] tree120
private theorem accepted_120 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox120) tree120 = true := by
  simp only [tree120,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox120 0 (3862558625585544697072665634708827354578288640000000000000000000 : Int) false,decode_split denominator ibox120 0 (3862558625585544697072665634708827354578288640000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_121 h,accepted_122 h⟩
private noncomputable def tree119 : TapeTree := .centered (candidateRows ibox119) (candidateRows (FixedTape.midBox ibox119))
attribute [irreducible] tree119
private theorem sign_119 : 2*denominator*(computed denominator (FixedTape.midBox ibox119)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox119).gradient k).lo.natAbs ((computed denominator ibox119).gradient k).hi.natAbs : Int)*((ibox119 k).hi-(ibox119 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox119
    (computed denominator ibox119) (computed denominator (FixedTape.midBox ibox119))
    (by decide +kernel)
private theorem midpoint_even_119 : ∀ k, 2 ∣ (ibox119 k).lo+(ibox119 k).hi := by decide +kernel
private theorem accepted_119 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox119) tree119 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox119 midpoint_even_119
  simp only [tree119,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox119,candidate_valid h (FixedTape.midBox ibox119),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox119 212 (FixedTape.rowsAux denominator ibox119 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox119) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_119
private noncomputable def tree118 : TapeTree := .centered (candidateRows ibox118) (candidateRows (FixedTape.midBox ibox118))
attribute [irreducible] tree118
private theorem sign_118 : 2*denominator*(computed denominator (FixedTape.midBox ibox118)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox118).gradient k).lo.natAbs ((computed denominator ibox118).gradient k).hi.natAbs : Int)*((ibox118 k).hi-(ibox118 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox118
    (computed denominator ibox118) (computed denominator (FixedTape.midBox ibox118))
    (by decide +kernel)
private theorem midpoint_even_118 : ∀ k, 2 ∣ (ibox118 k).lo+(ibox118 k).hi := by decide +kernel
private theorem accepted_118 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox118) tree118 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox118 midpoint_even_118
  simp only [tree118,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox118,candidate_valid h (FixedTape.midBox ibox118),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox118 212 (FixedTape.rowsAux denominator ibox118 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox118) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_118
private noncomputable def tree117 : TapeTree := .split 0 (((3862558625585544697072665634708827354578288640000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree118 tree119
attribute [irreducible] tree117
private theorem accepted_117 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox117) tree117 = true := by
  simp only [tree117,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox117 0 (3862558625585544697072665634708827354578288640000000000000000000 : Int) false,decode_split denominator ibox117 0 (3862558625585544697072665634708827354578288640000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_118 h,accepted_119 h⟩
private noncomputable def tree116 : TapeTree := .split 3 (((700399074188121334400492426968822374727680000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree117 tree120
attribute [irreducible] tree116
private theorem accepted_116 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox116) tree116 = true := by
  simp only [tree116,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox116 3 (700399074188121334400492426968822374727680000000000000000000000000 : Int) false,decode_split denominator ibox116 3 (700399074188121334400492426968822374727680000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_117 h,accepted_120 h⟩
private noncomputable def tree115 : TapeTree := .split 0 (((3948393261709667912563169315480134629124472832000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree116 tree123
attribute [irreducible] tree115
private theorem accepted_115 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox115) tree115 = true := by
  simp only [tree115,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox115 0 (3948393261709667912563169315480134629124472832000000000000000000 : Int) false,decode_split denominator ibox115 0 (3948393261709667912563169315480134629124472832000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_116 h,accepted_123 h⟩
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
private noncomputable def tree111 : TapeTree := .split 3 (((233466358062707111466830808989607458242560000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree112 tree113
attribute [irreducible] tree111
private theorem accepted_111 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox111) tree111 = true := by
  simp only [tree111,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox111 3 (233466358062707111466830808989607458242560000000000000000000000000 : Int) false,decode_split denominator ibox111 3 (233466358062707111466830808989607458242560000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_112 h,accepted_113 h⟩
private noncomputable def tree110 : TapeTree := .split 0 (((4034227897833791128053672996251441903670657024000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree111 tree114
attribute [irreducible] tree110
private theorem accepted_110 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox110) tree110 = true := by
  simp only [tree110,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox110 0 (4034227897833791128053672996251441903670657024000000000000000000 : Int) false,decode_split denominator ibox110 0 (4034227897833791128053672996251441903670657024000000000000000000 : Int) true]
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
private noncomputable def tree107 : TapeTree := .split 3 (((233466358062707111466830808989607458242560000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree108 tree109
attribute [irreducible] tree107
private theorem accepted_107 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox107) tree107 = true := by
  simp only [tree107,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox107 3 (233466358062707111466830808989607458242560000000000000000000000000 : Int) false,decode_split denominator ibox107 3 (233466358062707111466830808989607458242560000000000000000000000000 : Int) true]
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
private noncomputable def tree104 : TapeTree := .split 3 (((233466358062707111466830808989607458242560000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree105 tree106
attribute [irreducible] tree104
private theorem accepted_104 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox104) tree104 = true := by
  simp only [tree104,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox104 3 (233466358062707111466830808989607458242560000000000000000000000000 : Int) false,decode_split denominator ibox104 3 (233466358062707111466830808989607458242560000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_105 h,accepted_106 h⟩
private noncomputable def tree103 : TapeTree := .split 0 (((3862558625585544697072665634708827354578288640000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree104 tree107
attribute [irreducible] tree103
private theorem accepted_103 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox103) tree103 = true := by
  simp only [tree103,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox103 0 (3862558625585544697072665634708827354578288640000000000000000000 : Int) false,decode_split denominator ibox103 0 (3862558625585544697072665634708827354578288640000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_104 h,accepted_107 h⟩
private noncomputable def tree102 : TapeTree := .split 0 (((3948393261709667912563169315480134629124472832000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree103 tree110
attribute [irreducible] tree102
private theorem accepted_102 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox102) tree102 = true := by
  simp only [tree102,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox102 0 (3948393261709667912563169315480134629124472832000000000000000000 : Int) false,decode_split denominator ibox102 0 (3948393261709667912563169315480134629124472832000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_103 h,accepted_110 h⟩
private noncomputable def tree101 : TapeTree := .split 3 (((466932716125414222933661617979214916485120000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree102 tree115
attribute [irreducible] tree101
private theorem accepted_101 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox101) tree101 = true := by
  simp only [tree101,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox101 3 (466932716125414222933661617979214916485120000000000000000000000000 : Int) false,decode_split denominator ibox101 3 (466932716125414222933661617979214916485120000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_102 h,accepted_115 h⟩
private noncomputable def tree100 : TapeTree := .split 3 (((933865432250828445867323235958429832970240000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree101 tree126
attribute [irreducible] tree100
private theorem accepted_100 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox100) tree100 = true := by
  simp only [tree100,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox100 3 (933865432250828445867323235958429832970240000000000000000000000000 : Int) false,decode_split denominator ibox100 3 (933865432250828445867323235958429832970240000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_101 h,accepted_126 h⟩
private noncomputable def tree99 : TapeTree := .face 1 false (candidateRows ibox99) tree100
attribute [irreducible] tree99
private theorem sign_99 : ((computed denominator ibox99).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_99 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox99) tree99 = true := by
  simp only [tree99,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox99,?_,accepted_100 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox99)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox99).gradient 1).hi) denominator_positive).1 sign_99
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
private noncomputable def tree96 : TapeTree := .split 0 (((3690889353337298266091658273166212805485920256000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree97 tree98
attribute [irreducible] tree96
private theorem accepted_96 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox96) tree96 = true := by
  simp only [tree96,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox96 0 (3690889353337298266091658273166212805485920256000000000000000000 : Int) false,decode_split denominator ibox96 0 (3690889353337298266091658273166212805485920256000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_97 h,accepted_98 h⟩
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
private noncomputable def tree93 : TapeTree := .split 0 (((3690889353337298266091658273166212805485920256000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree94 tree95
attribute [irreducible] tree93
private theorem accepted_93 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox93) tree93 = true := by
  simp only [tree93,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox93 0 (3690889353337298266091658273166212805485920256000000000000000000 : Int) false,decode_split denominator ibox93 0 (3690889353337298266091658273166212805485920256000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_94 h,accepted_95 h⟩
private noncomputable def tree92 : TapeTree := .split 3 (((1634264506438949780267815662927252207697920000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree93 tree96
attribute [irreducible] tree92
private theorem accepted_92 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox92) tree92 = true := by
  simp only [tree92,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox92 3 (1634264506438949780267815662927252207697920000000000000000000000000 : Int) false,decode_split denominator ibox92 3 (1634264506438949780267815662927252207697920000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_93 h,accepted_96 h⟩
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
private noncomputable def tree89 : TapeTree := .split 0 (((3519220081089051835110650911623598256393551872000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree90 tree91
attribute [irreducible] tree89
private theorem accepted_89 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox89) tree89 = true := by
  simp only [tree89,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox89 0 (3519220081089051835110650911623598256393551872000000000000000000 : Int) false,decode_split denominator ibox89 0 (3519220081089051835110650911623598256393551872000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_90 h,accepted_91 h⟩
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
private noncomputable def tree86 : TapeTree := .split 0 (((3519220081089051835110650911623598256393551872000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree87 tree88
attribute [irreducible] tree86
private theorem accepted_86 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox86) tree86 = true := by
  simp only [tree86,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox86 0 (3519220081089051835110650911623598256393551872000000000000000000 : Int) false,decode_split denominator ibox86 0 (3519220081089051835110650911623598256393551872000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_87 h,accepted_88 h⟩
private noncomputable def tree85 : TapeTree := .split 3 (((1634264506438949780267815662927252207697920000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree86 tree89
attribute [irreducible] tree85
private theorem accepted_85 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox85) tree85 = true := by
  simp only [tree85,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox85 3 (1634264506438949780267815662927252207697920000000000000000000000000 : Int) false,decode_split denominator ibox85 3 (1634264506438949780267815662927252207697920000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_86 h,accepted_89 h⟩
private noncomputable def tree84 : TapeTree := .split 0 (((3605054717213175050601154592394905530939736064000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree85 tree92
attribute [irreducible] tree84
private theorem accepted_84 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox84) tree84 = true := by
  simp only [tree84,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox84 0 (3605054717213175050601154592394905530939736064000000000000000000 : Int) false,decode_split denominator ibox84 0 (3605054717213175050601154592394905530939736064000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_85 h,accepted_92 h⟩
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
private noncomputable def tree81 : TapeTree := .split 0 (((3690889353337298266091658273166212805485920256000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree82 tree83
attribute [irreducible] tree81
private theorem accepted_81 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox81) tree81 = true := by
  simp only [tree81,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox81 0 (3690889353337298266091658273166212805485920256000000000000000000 : Int) false,decode_split denominator ibox81 0 (3690889353337298266091658273166212805485920256000000000000000000 : Int) true]
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
private noncomputable def tree78 : TapeTree := .split 0 (((3690889353337298266091658273166212805485920256000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree79 tree80
attribute [irreducible] tree78
private theorem accepted_78 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox78) tree78 = true := by
  simp only [tree78,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox78 0 (3690889353337298266091658273166212805485920256000000000000000000 : Int) false,decode_split denominator ibox78 0 (3690889353337298266091658273166212805485920256000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_79 h,accepted_80 h⟩
private noncomputable def tree77 : TapeTree := .split 3 (((1167331790313535557334154044948037291212800000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree78 tree81
attribute [irreducible] tree77
private theorem accepted_77 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox77) tree77 = true := by
  simp only [tree77,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox77 3 (1167331790313535557334154044948037291212800000000000000000000000000 : Int) false,decode_split denominator ibox77 3 (1167331790313535557334154044948037291212800000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_78 h,accepted_81 h⟩
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
private noncomputable def tree74 : TapeTree := .split 0 (((3519220081089051835110650911623598256393551872000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree75 tree76
attribute [irreducible] tree74
private theorem accepted_74 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox74) tree74 = true := by
  simp only [tree74,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox74 0 (3519220081089051835110650911623598256393551872000000000000000000 : Int) false,decode_split denominator ibox74 0 (3519220081089051835110650911623598256393551872000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_75 h,accepted_76 h⟩
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
private noncomputable def tree72 : TapeTree := .centered (candidateRows ibox72) (candidateRows (FixedTape.midBox ibox72))
attribute [irreducible] tree72
private theorem sign_72 : 2*denominator*(computed denominator (FixedTape.midBox ibox72)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox72).gradient k).lo.natAbs ((computed denominator ibox72).gradient k).hi.natAbs : Int)*((ibox72 k).hi-(ibox72 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox72
    (computed denominator ibox72) (computed denominator (FixedTape.midBox ibox72))
    (by decide +kernel)
private theorem midpoint_even_72 : ∀ k, 2 ∣ (ibox72 k).lo+(ibox72 k).hi := by decide +kernel
private theorem accepted_72 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox72) tree72 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox72 midpoint_even_72
  simp only [tree72,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox72,candidate_valid h (FixedTape.midBox ibox72),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox72 212 (FixedTape.rowsAux denominator ibox72 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox72) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_72
private noncomputable def tree71 : TapeTree := .split 0 (((3519220081089051835110650911623598256393551872000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree72 tree73
attribute [irreducible] tree71
private theorem accepted_71 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox71) tree71 = true := by
  simp only [tree71,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox71 0 (3519220081089051835110650911623598256393551872000000000000000000 : Int) false,decode_split denominator ibox71 0 (3519220081089051835110650911623598256393551872000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_72 h,accepted_73 h⟩
private noncomputable def tree70 : TapeTree := .split 3 (((1167331790313535557334154044948037291212800000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree71 tree74
attribute [irreducible] tree70
private theorem accepted_70 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox70) tree70 = true := by
  simp only [tree70,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox70 3 (1167331790313535557334154044948037291212800000000000000000000000000 : Int) false,decode_split denominator ibox70 3 (1167331790313535557334154044948037291212800000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_71 h,accepted_74 h⟩
private noncomputable def tree69 : TapeTree := .split 0 (((3605054717213175050601154592394905530939736064000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree70 tree77
attribute [irreducible] tree69
private theorem accepted_69 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox69) tree69 = true := by
  simp only [tree69,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox69 0 (3605054717213175050601154592394905530939736064000000000000000000 : Int) false,decode_split denominator ibox69 0 (3605054717213175050601154592394905530939736064000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_70 h,accepted_77 h⟩
private noncomputable def tree68 : TapeTree := .split 3 (((1400798148376242668800984853937644749455360000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree69 tree84
attribute [irreducible] tree68
private theorem accepted_68 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox68) tree68 = true := by
  simp only [tree68,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox68 3 (1400798148376242668800984853937644749455360000000000000000000000000 : Int) false,decode_split denominator ibox68 3 (1400798148376242668800984853937644749455360000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_69 h,accepted_84 h⟩
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
private noncomputable def tree65 : TapeTree := .split 0 (((3690889353337298266091658273166212805485920256000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree66 tree67
attribute [irreducible] tree65
private theorem accepted_65 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox65) tree65 = true := by
  simp only [tree65,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox65 0 (3690889353337298266091658273166212805485920256000000000000000000 : Int) false,decode_split denominator ibox65 0 (3690889353337298266091658273166212805485920256000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_66 h,accepted_67 h⟩
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
private noncomputable def tree63 : TapeTree := .centered (candidateRows ibox63) (candidateRows (FixedTape.midBox ibox63))
attribute [irreducible] tree63
private theorem sign_63 : 2*denominator*(computed denominator (FixedTape.midBox ibox63)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox63).gradient k).lo.natAbs ((computed denominator ibox63).gradient k).hi.natAbs : Int)*((ibox63 k).hi-(ibox63 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox63
    (computed denominator ibox63) (computed denominator (FixedTape.midBox ibox63))
    (by decide +kernel)
private theorem midpoint_even_63 : ∀ k, 2 ∣ (ibox63 k).lo+(ibox63 k).hi := by decide +kernel
private theorem accepted_63 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox63) tree63 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox63 midpoint_even_63
  simp only [tree63,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox63,candidate_valid h (FixedTape.midBox ibox63),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox63 212 (FixedTape.rowsAux denominator ibox63 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox63) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_63
private noncomputable def tree62 : TapeTree := .split 0 (((3690889353337298266091658273166212805485920256000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree63 tree64
attribute [irreducible] tree62
private theorem accepted_62 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox62) tree62 = true := by
  simp only [tree62,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox62 0 (3690889353337298266091658273166212805485920256000000000000000000 : Int) false,decode_split denominator ibox62 0 (3690889353337298266091658273166212805485920256000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_63 h,accepted_64 h⟩
private noncomputable def tree61 : TapeTree := .split 3 (((700399074188121334400492426968822374727680000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree62 tree65
attribute [irreducible] tree61
private theorem accepted_61 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox61) tree61 = true := by
  simp only [tree61,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox61 3 (700399074188121334400492426968822374727680000000000000000000000000 : Int) false,decode_split denominator ibox61 3 (700399074188121334400492426968822374727680000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_62 h,accepted_65 h⟩
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
private noncomputable def tree58 : TapeTree := .split 3 (((700399074188121334400492426968822374727680000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree59 tree60
attribute [irreducible] tree58
private theorem accepted_58 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox58) tree58 = true := by
  simp only [tree58,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox58 3 (700399074188121334400492426968822374727680000000000000000000000000 : Int) false,decode_split denominator ibox58 3 (700399074188121334400492426968822374727680000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_59 h,accepted_60 h⟩
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
private noncomputable def tree56 : TapeTree := .centered (candidateRows ibox56) (candidateRows (FixedTape.midBox ibox56))
attribute [irreducible] tree56
private theorem sign_56 : 2*denominator*(computed denominator (FixedTape.midBox ibox56)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox56).gradient k).lo.natAbs ((computed denominator ibox56).gradient k).hi.natAbs : Int)*((ibox56 k).hi-(ibox56 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox56
    (computed denominator ibox56) (computed denominator (FixedTape.midBox ibox56))
    (by decide +kernel)
private theorem midpoint_even_56 : ∀ k, 2 ∣ (ibox56 k).lo+(ibox56 k).hi := by decide +kernel
private theorem accepted_56 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox56) tree56 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox56 midpoint_even_56
  simp only [tree56,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox56,candidate_valid h (FixedTape.midBox ibox56),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox56 212 (FixedTape.rowsAux denominator ibox56 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox56) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_56
private noncomputable def tree55 : TapeTree := .split 3 (((700399074188121334400492426968822374727680000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree56 tree57
attribute [irreducible] tree55
private theorem accepted_55 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox55) tree55 = true := by
  simp only [tree55,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox55 3 (700399074188121334400492426968822374727680000000000000000000000000 : Int) false,decode_split denominator ibox55 3 (700399074188121334400492426968822374727680000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_56 h,accepted_57 h⟩
private noncomputable def tree54 : TapeTree := .split 0 (((3519220081089051835110650911623598256393551872000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree55 tree58
attribute [irreducible] tree54
private theorem accepted_54 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox54) tree54 = true := by
  simp only [tree54,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox54 0 (3519220081089051835110650911623598256393551872000000000000000000 : Int) false,decode_split denominator ibox54 0 (3519220081089051835110650911623598256393551872000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_55 h,accepted_58 h⟩
private noncomputable def tree53 : TapeTree := .split 0 (((3605054717213175050601154592394905530939736064000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree54 tree61
attribute [irreducible] tree53
private theorem accepted_53 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox53) tree53 = true := by
  simp only [tree53,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox53 0 (3605054717213175050601154592394905530939736064000000000000000000 : Int) false,decode_split denominator ibox53 0 (3605054717213175050601154592394905530939736064000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_54 h,accepted_61 h⟩
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
private noncomputable def tree50 : TapeTree := .split 3 (((233466358062707111466830808989607458242560000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree51 tree52
attribute [irreducible] tree50
private theorem accepted_50 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox50) tree50 = true := by
  simp only [tree50,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox50 3 (233466358062707111466830808989607458242560000000000000000000000000 : Int) false,decode_split denominator ibox50 3 (233466358062707111466830808989607458242560000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_51 h,accepted_52 h⟩
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
private noncomputable def tree48 : TapeTree := .centered (candidateRows ibox48) (candidateRows (FixedTape.midBox ibox48))
attribute [irreducible] tree48
private theorem sign_48 : 2*denominator*(computed denominator (FixedTape.midBox ibox48)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox48).gradient k).lo.natAbs ((computed denominator ibox48).gradient k).hi.natAbs : Int)*((ibox48 k).hi-(ibox48 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox48
    (computed denominator ibox48) (computed denominator (FixedTape.midBox ibox48))
    (by decide +kernel)
private theorem midpoint_even_48 : ∀ k, 2 ∣ (ibox48 k).lo+(ibox48 k).hi := by decide +kernel
private theorem accepted_48 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox48) tree48 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox48 midpoint_even_48
  simp only [tree48,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox48,candidate_valid h (FixedTape.midBox ibox48),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox48 212 (FixedTape.rowsAux denominator ibox48 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox48) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_48
private noncomputable def tree47 : TapeTree := .split 3 (((233466358062707111466830808989607458242560000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree48 tree49
attribute [irreducible] tree47
private theorem accepted_47 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox47) tree47 = true := by
  simp only [tree47,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox47 3 (233466358062707111466830808989607458242560000000000000000000000000 : Int) false,decode_split denominator ibox47 3 (233466358062707111466830808989607458242560000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_48 h,accepted_49 h⟩
private noncomputable def tree46 : TapeTree := .split 0 (((3690889353337298266091658273166212805485920256000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree47 tree50
attribute [irreducible] tree46
private theorem accepted_46 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox46) tree46 = true := by
  simp only [tree46,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox46 0 (3690889353337298266091658273166212805485920256000000000000000000 : Int) false,decode_split denominator ibox46 0 (3690889353337298266091658273166212805485920256000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_47 h,accepted_50 h⟩
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
private noncomputable def tree43 : TapeTree := .split 3 (((233466358062707111466830808989607458242560000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree44 tree45
attribute [irreducible] tree43
private theorem accepted_43 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox43) tree43 = true := by
  simp only [tree43,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox43 3 (233466358062707111466830808989607458242560000000000000000000000000 : Int) false,decode_split denominator ibox43 3 (233466358062707111466830808989607458242560000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_44 h,accepted_45 h⟩
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
private noncomputable def tree40 : TapeTree := .split 3 (((233466358062707111466830808989607458242560000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree41 tree42
attribute [irreducible] tree40
private theorem accepted_40 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox40) tree40 = true := by
  simp only [tree40,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox40 3 (233466358062707111466830808989607458242560000000000000000000000000 : Int) false,decode_split denominator ibox40 3 (233466358062707111466830808989607458242560000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_41 h,accepted_42 h⟩
private noncomputable def tree39 : TapeTree := .split 0 (((3519220081089051835110650911623598256393551872000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree40 tree43
attribute [irreducible] tree39
private theorem accepted_39 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox39) tree39 = true := by
  simp only [tree39,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox39 0 (3519220081089051835110650911623598256393551872000000000000000000 : Int) false,decode_split denominator ibox39 0 (3519220081089051835110650911623598256393551872000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_40 h,accepted_43 h⟩
private noncomputable def tree38 : TapeTree := .split 0 (((3605054717213175050601154592394905530939736064000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree39 tree46
attribute [irreducible] tree38
private theorem accepted_38 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox38) tree38 = true := by
  simp only [tree38,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox38 0 (3605054717213175050601154592394905530939736064000000000000000000 : Int) false,decode_split denominator ibox38 0 (3605054717213175050601154592394905530939736064000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_39 h,accepted_46 h⟩
private noncomputable def tree37 : TapeTree := .split 3 (((466932716125414222933661617979214916485120000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree38 tree53
attribute [irreducible] tree37
private theorem accepted_37 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox37) tree37 = true := by
  simp only [tree37,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox37 3 (466932716125414222933661617979214916485120000000000000000000000000 : Int) false,decode_split denominator ibox37 3 (466932716125414222933661617979214916485120000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_38 h,accepted_53 h⟩
private noncomputable def tree36 : TapeTree := .split 3 (((933865432250828445867323235958429832970240000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree37 tree68
attribute [irreducible] tree36
private theorem accepted_36 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox36) tree36 = true := by
  simp only [tree36,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox36 3 (933865432250828445867323235958429832970240000000000000000000000000 : Int) false,decode_split denominator ibox36 3 (933865432250828445867323235958429832970240000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_37 h,accepted_68 h⟩
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
private noncomputable def tree34 : TapeTree := .split 0 (((3776723989461421481582161953937520080032104448000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree35 tree99
attribute [irreducible] tree34
private theorem accepted_34 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox34) tree34 = true := by
  simp only [tree34,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox34 0 (3776723989461421481582161953937520080032104448000000000000000000 : Int) false,decode_split denominator ibox34 0 (3776723989461421481582161953937520080032104448000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_35 h,accepted_99 h⟩
private noncomputable def tree33 : TapeTree := .split 1 (((233466358062707111466830808989607458242560000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree34 tree145
attribute [irreducible] tree33
private theorem accepted_33 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox33) tree33 = true := by
  simp only [tree33,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox33 1 (233466358062707111466830808989607458242560000000000000000000000000 : Int) false,decode_split denominator ibox33 1 (233466358062707111466830808989607458242560000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_34 h,accepted_145 h⟩
private noncomputable def tree32 : TapeTree := .split 1 (((466932716125414222933661617979214916485120000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree33 tree154
attribute [irreducible] tree32
private theorem accepted_32 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox32) tree32 = true := by
  simp only [tree32,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox32 1 (466932716125414222933661617979214916485120000000000000000000000000 : Int) false,decode_split denominator ibox32 1 (466932716125414222933661617979214916485120000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_33 h,accepted_154 h⟩
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
private noncomputable def tree30 : TapeTree := .split 1 (((933865432250828445867323235958429832970240000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree31 tree159
attribute [irreducible] tree30
private theorem accepted_30 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox30) tree30 = true := by
  simp only [tree30,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox30 1 (933865432250828445867323235958429832970240000000000000000000000000 : Int) false,decode_split denominator ibox30 1 (933865432250828445867323235958429832970240000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_31 h,accepted_159 h⟩
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
private noncomputable def tree27 : TapeTree := .split 1 (((933865432250828445867323235958429832970240000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree28 tree29
attribute [irreducible] tree27
private theorem accepted_27 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox27) tree27 = true := by
  simp only [tree27,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox27 1 (933865432250828445867323235958429832970240000000000000000000000000 : Int) false,decode_split denominator ibox27 1 (933865432250828445867323235958429832970240000000000000000000000000 : Int) true]
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
private noncomputable def tree23 : TapeTree := .split 1 (((933865432250828445867323235958429832970240000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree24 tree25
attribute [irreducible] tree23
private theorem accepted_23 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox23) tree23 = true := by
  simp only [tree23,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox23 1 (933865432250828445867323235958429832970240000000000000000000000000 : Int) false,decode_split denominator ibox23 1 (933865432250828445867323235958429832970240000000000000000000000000 : Int) true]
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
private noncomputable def tree21 : TapeTree := .split 0 (((3776723989461421481582161953937520080032104448000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree22 tree26
attribute [irreducible] tree21
private theorem accepted_21 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox21) tree21 = true := by
  simp only [tree21,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox21 0 (3776723989461421481582161953937520080032104448000000000000000000 : Int) false,decode_split denominator ibox21 0 (3776723989461421481582161953937520080032104448000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_22 h,accepted_26 h⟩
private noncomputable def tree20 : TapeTree := .split 2 (((1400798148376242668800984853937644749455360000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree21 tree30
attribute [irreducible] tree20
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox20 2 (1400798148376242668800984853937644749455360000000000000000000000000 : Int) false,decode_split denominator ibox20 2 (1400798148376242668800984853937644749455360000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_21 h,accepted_30 h⟩
private noncomputable def tree19 : TapeTree := .split 0 (((4120062533957914343544176677022749178216841216000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree20 tree167
attribute [irreducible] tree19
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox19 0 (4120062533957914343544176677022749178216841216000000000000000000 : Int) false,decode_split denominator ibox19 0 (4120062533957914343544176677022749178216841216000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_20 h,accepted_167 h⟩
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
private noncomputable def tree16 : TapeTree := .split 0 (((4463401078454407205506191400107978276401577984000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree17 tree18
attribute [irreducible] tree16
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox16 0 (4463401078454407205506191400107978276401577984000000000000000000 : Int) false,decode_split denominator ibox16 0 (4463401078454407205506191400107978276401577984000000000000000000 : Int) true]
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
private noncomputable def tree14 : TapeTree := .split 1 (((1400798148376242668800984853937644749455360000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree15 tree16
attribute [irreducible] tree14
private theorem accepted_14 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox14) tree14 = true := by
  simp only [tree14,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox14 1 (1400798148376242668800984853937644749455360000000000000000000000000 : Int) false,decode_split denominator ibox14 1 (1400798148376242668800984853937644749455360000000000000000000000000 : Int) true]
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
private noncomputable def tree11 : TapeTree := .split 1 (((933865432250828445867323235958429832970240000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree12 tree14
attribute [irreducible] tree11
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox11 1 (933865432250828445867323235958429832970240000000000000000000000000 : Int) false,decode_split denominator ibox11 1 (933865432250828445867323235958429832970240000000000000000000000000 : Int) true]
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
private noncomputable def tree6 : TapeTree := .split 0 (((3776723989461421481582161953937520080032104448000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree7 tree9
attribute [irreducible] tree6
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox6 0 (3776723989461421481582161953937520080032104448000000000000000000 : Int) false,decode_split denominator ibox6 0 (3776723989461421481582161953937520080032104448000000000000000000 : Int) true]
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
private noncomputable def tree3 : TapeTree := .split 1 (((933865432250828445867323235958429832970240000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree6
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 1 (933865432250828445867323235958429832970240000000000000000000000000 : Int) false,decode_split denominator ibox3 1 (933865432250828445867323235958429832970240000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_6 h⟩
private noncomputable def tree2 : TapeTree := .split 0 (((4120062533957914343544176677022749178216841216000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree11
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 0 (4120062533957914343544176677022749178216841216000000000000000000 : Int) false,decode_split denominator ibox2 0 (4120062533957914343544176677022749178216841216000000000000000000 : Int) true]
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
private noncomputable def tree0 : TapeTree := .split 2 (((933865432250828445867323235958429832970240000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree1 tree19
attribute [irreducible] tree0
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox0 2 (933865432250828445867323235958429832970240000000000000000000000000 : Int) false,decode_split denominator ibox0 2 (933865432250828445867323235958429832970240000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_1 h,accepted_19 h⟩
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (117649/64000000 : ℚ) (823543/320000000 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 212 = e219 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (117649/64000000 : ℚ) (823543/320000000 : ℚ)) x → eval e219 x ≤ 0 := by
  have hb := h.child_4 tape 212 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell7_low_internal

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell7_low_internal
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((117649/64000000 : ℚ) : ℝ) < p ∧ p ≤ ((823543/320000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 7 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 7 p)
    (hk0 : ((823543/320000000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((117649/64000000 : ℚ) : ℝ))
    (hk1 : ((823543/320000000 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((117649/64000000 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r), internalResidual (0 : Fin 9) a p A r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell7_low_internal.cell_bound h.child_8 h.child_9 (Cell7_low_internal.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell7_low_internal
