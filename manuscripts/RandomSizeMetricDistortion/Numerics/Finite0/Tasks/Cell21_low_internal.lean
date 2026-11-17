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
namespace Cell21_low_internal
private noncomputable def qValues : Fin 4 → ℚ := ![(-2520631455420736673911951830159397/1241245782574667063865317090560000 : ℚ),(36799418511893608671875000000/969723267636458643644778977 : ℚ),(-1196385022177226809515965750959/2260079914250000723225572560000 : ℚ),(1061454525841096250000000000/28250998928125009040319657 : ℚ)]
private noncomputable abbrev e2 : PolyExpr := SharedFiniteSemantics11.e2 qValues
private noncomputable abbrev e11 : PolyExpr := SharedFiniteSemantics11.e11 qValues
private noncomputable abbrev e12 : PolyExpr := SharedFiniteSemantics11.e12 qValues
private noncomputable abbrev e16 : PolyExpr := SharedFiniteSemantics11.e16 qValues
private noncomputable abbrev e39 : PolyExpr := SharedFiniteSemantics11.e39 qValues
private noncomputable abbrev e220 : PolyExpr := SharedFiniteSemantics11.e220 qValues
private noncomputable abbrev node_1 := SharedFiniteSemantics11.node_1 qValues
private noncomputable abbrev node_2 := SharedFiniteSemantics11.node_2 qValues
private noncomputable abbrev node_3 := SharedFiniteSemantics11.node_3 qValues
private noncomputable abbrev node_4 := SharedFiniteSemantics11.node_4 qValues
private noncomputable abbrev node_5 := SharedFiniteSemantics11.node_5 qValues
private noncomputable abbrev node_6 := SharedFiniteSemantics11.node_6 qValues
private noncomputable abbrev node_9 := SharedFiniteSemantics11.node_9 qValues
private noncomputable abbrev node_10 := SharedFiniteSemantics11.node_10 qValues
private noncomputable abbrev node_11 := SharedFiniteSemantics11.node_11 qValues
private noncomputable abbrev node_12 := SharedFiniteSemantics11.node_12 qValues
private noncomputable abbrev node_13 := SharedFiniteSemantics11.node_13 qValues
private noncomputable abbrev node_14 := SharedFiniteSemantics11.node_14 qValues
private noncomputable abbrev node_15 := SharedFiniteSemantics11.node_15 qValues
private noncomputable abbrev node_16 := SharedFiniteSemantics11.node_16 qValues
private noncomputable abbrev node_38 := SharedFiniteSemantics11.node_38 qValues
private noncomputable abbrev node_39 := SharedFiniteSemantics11.node_39 qValues
private noncomputable abbrev node_180 := SharedFiniteSemantics11.node_180 qValues
private noncomputable abbrev node_181 := SharedFiniteSemantics11.node_181 qValues
private noncomputable abbrev node_182 := SharedFiniteSemantics11.node_182 qValues
private noncomputable abbrev node_183 := SharedFiniteSemantics11.node_183 qValues
private noncomputable abbrev node_184 := SharedFiniteSemantics11.node_184 qValues
private noncomputable abbrev node_185 := SharedFiniteSemantics11.node_185 qValues
private noncomputable abbrev node_186 := SharedFiniteSemantics11.node_186 qValues
private noncomputable abbrev node_187 := SharedFiniteSemantics11.node_187 qValues
private noncomputable abbrev node_188 := SharedFiniteSemantics11.node_188 qValues
private noncomputable abbrev node_189 := SharedFiniteSemantics11.node_189 qValues
private noncomputable abbrev node_190 := SharedFiniteSemantics11.node_190 qValues
private noncomputable abbrev node_191 := SharedFiniteSemantics11.node_191 qValues
private noncomputable abbrev node_193 := SharedFiniteSemantics11.node_193 qValues
private noncomputable abbrev node_194 := SharedFiniteSemantics11.node_194 qValues
private noncomputable abbrev node_195 := SharedFiniteSemantics11.node_195 qValues
private noncomputable abbrev node_200 := SharedFiniteSemantics11.node_200 qValues
private noncomputable abbrev node_201 := SharedFiniteSemantics11.node_201 qValues
private noncomputable abbrev node_202 := SharedFiniteSemantics11.node_202 qValues
private noncomputable abbrev node_219 := SharedFiniteSemantics11.node_219 qValues
private noncomputable abbrev node_220 := SharedFiniteSemantics11.node_220 qValues
private noncomputable abbrev semantic_H_37 := SharedFiniteSemantics11.semantic_H_37 qValues
private noncomputable abbrev semantic_psi_218 := SharedFiniteSemantics11.semantic_psi_218 qValues
private noncomputable abbrev semantic_Hd_179 := SharedFiniteSemantics11.semantic_Hd_179 qValues
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
    priceLambda 21 p = ((-2520631455420736673911951830159397/1241245782574667063865317090560000 : ℝ)+(36799418511893608671875000000/969723267636458643644778977 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell21,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 21 p = (((-1196385022177226809515965750959/2260079914250000723225572560000 : ℝ)+(1061454525841096250000000000/28250998928125009040319657 : ℝ)*p)-(145513/100000 : ℝ)*(1/1 : ℝ))/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell21,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e220 x = (x 0*(1-x 0))*(aPoint x+priceLambda 21 (x 0)*(HStar (yPoint x)-HStar (aPoint x)-HStar (capPoint x))+priceTau 21 (x 0)*psiStar (rPoint x)+(0)-(0)) := by
  have hp0 : x 0 ≠ 0 := ne_of_gt hp.1
  have hp1 : x 0 ≠ 1 := ne_of_lt hp.2
  have heps : 1-x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  rw [price_lambda_normal _ hp,price_tau_normal _ hp]
  simp only [node_1,node_13,node_180,node_181,node_182,node_183,node_184,node_185,node_186,node_187,node_188,node_189,node_190,node_191,node_193,node_194,node_195,node_200,node_201,node_202,node_219,node_220,semantic_H_37,semantic_psi_218,semantic_Hd_179,point_12,point_11,point_2,point_16,point_39]
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
    (hL : lambdaStar (x 0) = priceLambda 21 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 21 (x 0)) :
    (1)*eval e220 x = (x 0*(1-x 0))*(internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,if_pos hA,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (1/16 : ℚ) (7291666666666667/100000000000000000 : ℚ)) x → eval e220 x ≤ 0)
    (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((1/16 : ℚ) : ℝ) < p ∧ p ≤ ((7291666666666667/100000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 21 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 21 p)
    (hk0 : ((7291666666666667/100000000000000000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((1/16 : ℚ) : ℝ))
    (hk1 : ((7291666666666667/100000000000000000 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((1/16 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r) :
    internalResidual (0 : Fin 9) a p A r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxA,hxr⟩ := h3 (1/16 : ℚ) (7291666666666667/100000000000000000 : ℚ) ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ) p a A r hpcell hk0 hk1 hr ha hap hpA hAr
  have hcut : ((7291666666666667/100000000000000000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) := by norm_num [bStar]
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxa
  have hAx : capPoint x = A := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxA
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 21 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 21 (x 0) := by simpa only [hxp] using hT
  have hrootb : ((2840189/5000000 : ℚ) : ℝ) ≤ bStar := by norm_num [bStar]
  have hAb : A ≤ bStar := hAr.trans (hr.2.trans hrootb)
  have hflag : aPoint x ≤ bStar := by rw [hax]; exact hap.trans (hpA.trans hAb)
  have hflagA : capPoint x ≤ bStar := by simpa only [hAx] using hAb
  have hb := hbound x hx
  have hv : (1 : ℝ)*eval e220 x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 1) hb
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
.const (-2520631455420736673911951830159397/1241245782574667063865317090560000 : ℚ),
.const (36799418511893608671875000000/969723267636458643644778977 : ℚ),
.mul 180 1,
.add 179 181,
.const (-1196385022177226809515965750959/2260079914250000723225572560000 : ℚ),
.const (1061454525841096250000000000/28250998928125009040319657 : ℚ),
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
private noncomputable def ssaQVals : Fin 16 → ℚ := ![(1/1 : ℚ),(49/100 : ℚ),(390189/5000000 : ℚ),(1085/4818 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(4818/3733 : ℚ),(-2520631455420736673911951830159397/1241245782574667063865317090560000 : ℚ),(36799418511893608671875000000/969723267636458643644778977 : ℚ),(-1196385022177226809515965750959/2260079914250000723225572560000 : ℚ),(1061454525841096250000000000/28250998928125009040319657 : ℚ),(-145513/100000 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ)]
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
private noncomputable def denominator : Int := 1598990716115128465157643279046325385965388868505344842108724090770479382528000000000000000000000000
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
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨99936919757195529072352704940395336622836804281584052631795255673154961408000000000000000000000000,116593073050061455914380542814222776585453868482932681288390693303163595338413635901597941760000000⟩,⟨0,1598990716115128465157643279046325385965388868505344842108724090770479382528000000000000000000000000⟩,⟨0,1598990716115128465157643279046325385965388868505344842108724090770479382528000000000000000000000000⟩,⟨0,1598990716115128465157643279046325385965388868505344842108724090770479382528000000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := splitI ibox0 0 108264996403628492493366623877309056604145336382258366960092974488159278373206817950798970880000000 false
private noncomputable def ibox2 : Fin 4 → FixedTape.I := splitI ibox1 2 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 false
private noncomputable def ibox3 : Fin 4 → FixedTape.I := faceI ibox2 3 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 0 104100958080412010782859664408852196613491070331921209795944115080657119890603408975399485440000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := faceI ibox4 1 true
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox3 0 104100958080412010782859664408852196613491070331921209795944115080657119890603408975399485440000000 true
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox6 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 false
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox6 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 true
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox1 2 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 true
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox9 0 104100958080412010782859664408852196613491070331921209795944115080657119890603408975399485440000000 false
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox10 2 1199243037086346348868232459284744039474041651379008631581543068077859536896000000000000000000000000 false
private noncomputable def ibox12 : Fin 4 → FixedTape.I := faceI ibox11 3 false
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox12 0 102018938918803769927606184674623766618163937306752631213869685376906040649301704487699742720000000 false
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox13 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 false
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox13 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 true
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox12 0 102018938918803769927606184674623766618163937306752631213869685376906040649301704487699742720000000 true
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox16 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 false
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox16 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 true
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox10 2 1199243037086346348868232459284744039474041651379008631581543068077859536896000000000000000000000000 true
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox19 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 false
private noncomputable def ibox21 : Fin 4 → FixedTape.I := faceI ibox20 2 true
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox21 1 399747679028782116289410819761581346491347217126336210527181022692619845632000000000000000000000000 false
private noncomputable def ibox23 : Fin 4 → FixedTape.I := splitI ibox22 0 102018938918803769927606184674623766618163937306752631213869685376906040649301704487699742720000000 false
private noncomputable def ibox24 : Fin 4 → FixedTape.I := faceI ibox23 1 false
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox22 0 102018938918803769927606184674623766618163937306752631213869685376906040649301704487699742720000000 true
private noncomputable def ibox26 : Fin 4 → FixedTape.I := faceI ibox25 1 false
private noncomputable def ibox27 : Fin 4 → FixedTape.I := splitI ibox21 1 399747679028782116289410819761581346491347217126336210527181022692619845632000000000000000000000000 true
private noncomputable def ibox28 : Fin 4 → FixedTape.I := faceI ibox27 0 false
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox19 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 true
private noncomputable def ibox30 : Fin 4 → FixedTape.I := faceI ibox29 0 false
private noncomputable def ibox31 : Fin 4 → FixedTape.I := faceI ibox30 2 true
private noncomputable def ibox32 : Fin 4 → FixedTape.I := splitI ibox9 0 104100958080412010782859664408852196613491070331921209795944115080657119890603408975399485440000000 true
private noncomputable def ibox33 : Fin 4 → FixedTape.I := splitI ibox32 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 false
private noncomputable def ibox34 : Fin 4 → FixedTape.I := faceI ibox33 2 true
private noncomputable def ibox35 : Fin 4 → FixedTape.I := faceI ibox34 1 false
private noncomputable def ibox36 : Fin 4 → FixedTape.I := splitI ibox32 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 true
private noncomputable def ibox37 : Fin 4 → FixedTape.I := faceI ibox36 0 false
private noncomputable def ibox38 : Fin 4 → FixedTape.I := splitI ibox0 0 108264996403628492493366623877309056604145336382258366960092974488159278373206817950798970880000000 true
private noncomputable def ibox39 : Fin 4 → FixedTape.I := splitI ibox38 2 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 false
private noncomputable def ibox40 : Fin 4 → FixedTape.I := faceI ibox39 3 false
private noncomputable def ibox41 : Fin 4 → FixedTape.I := splitI ibox40 0 112429034726844974203873583345765916594799602432595524124241833895661436855810226926198456320000000 false
private noncomputable def ibox42 : Fin 4 → FixedTape.I := splitI ibox41 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 false
private noncomputable def ibox43 : Fin 4 → FixedTape.I := splitI ibox41 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 true
private noncomputable def ibox44 : Fin 4 → FixedTape.I := splitI ibox40 0 112429034726844974203873583345765916594799602432595524124241833895661436855810226926198456320000000 true
private noncomputable def ibox45 : Fin 4 → FixedTape.I := splitI ibox44 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 false
private noncomputable def ibox46 : Fin 4 → FixedTape.I := splitI ibox44 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 true
private noncomputable def ibox47 : Fin 4 → FixedTape.I := splitI ibox38 2 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 true
private noncomputable def ibox48 : Fin 4 → FixedTape.I := splitI ibox47 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 false
private noncomputable def ibox49 : Fin 4 → FixedTape.I := faceI ibox48 2 true
private noncomputable def ibox50 : Fin 4 → FixedTape.I := faceI ibox49 1 false
private noncomputable def ibox51 : Fin 4 → FixedTape.I := splitI ibox50 0 112429034726844974203873583345765916594799602432595524124241833895661436855810226926198456320000000 false
private noncomputable def ibox52 : Fin 4 → FixedTape.I := splitI ibox50 0 112429034726844974203873583345765916594799602432595524124241833895661436855810226926198456320000000 true
private noncomputable def ibox53 : Fin 4 → FixedTape.I := splitI ibox47 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 true
private noncomputable def ibox54 : Fin 4 → FixedTape.I := faceI ibox53 0 false
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
private noncomputable def tree53 : TapeTree := .face 0 false (candidateRows ibox53) tree54
attribute [irreducible] tree53
private theorem sign_53 : ((computed denominator ibox53).gradient 0).hi ≤ 0 := by decide +kernel
private theorem accepted_53 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox53) tree53 = true := by
  simp only [tree53,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox53,?_,accepted_54 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox53)).gradient 0).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox53).gradient 0).hi) denominator_positive).1 sign_53
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
private noncomputable def tree50 : TapeTree := .split 0 (((112429034726844974203873583345765916594799602432595524124241833895661436855810226926198456320000000 : Int) : ℚ)/(denominator : ℚ)) tree51 tree52
attribute [irreducible] tree50
private theorem accepted_50 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox50) tree50 = true := by
  simp only [tree50,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox50 0 (112429034726844974203873583345765916594799602432595524124241833895661436855810226926198456320000000 : Int) false,decode_split denominator ibox50 0 (112429034726844974203873583345765916594799602432595524124241833895661436855810226926198456320000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_51 h,accepted_52 h⟩
private noncomputable def tree49 : TapeTree := .face 1 false (candidateRows ibox49) tree50
attribute [irreducible] tree49
private theorem sign_49 : ((computed denominator ibox49).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_49 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox49) tree49 = true := by
  simp only [tree49,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox49,?_,accepted_50 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox49)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox49).gradient 1).hi) denominator_positive).1 sign_49
private noncomputable def tree48 : TapeTree := .face 2 true (candidateRows ibox48) tree49
attribute [irreducible] tree48
private theorem sign_48 : 0 ≤ ((computed denominator ibox48).gradient 2).lo := by decide +kernel
private theorem accepted_48 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox48) tree48 = true := by
  simp only [tree48,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox48,?_,accepted_49 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox48)).gradient 2).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox48).gradient 2).lo) denominator_positive).2 sign_48
private noncomputable def tree47 : TapeTree := .split 1 (((799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree48 tree53
attribute [irreducible] tree47
private theorem accepted_47 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox47) tree47 = true := by
  simp only [tree47,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox47 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) false,decode_split denominator ibox47 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_48 h,accepted_53 h⟩
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
private noncomputable def tree44 : TapeTree := .split 1 (((799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree45 tree46
attribute [irreducible] tree44
private theorem accepted_44 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox44) tree44 = true := by
  simp only [tree44,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox44 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) false,decode_split denominator ibox44 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) true]
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
private noncomputable def tree41 : TapeTree := .split 1 (((799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree42 tree43
attribute [irreducible] tree41
private theorem accepted_41 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox41) tree41 = true := by
  simp only [tree41,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox41 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) false,decode_split denominator ibox41 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_42 h,accepted_43 h⟩
private noncomputable def tree40 : TapeTree := .split 0 (((112429034726844974203873583345765916594799602432595524124241833895661436855810226926198456320000000 : Int) : ℚ)/(denominator : ℚ)) tree41 tree44
attribute [irreducible] tree40
private theorem accepted_40 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox40) tree40 = true := by
  simp only [tree40,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox40 0 (112429034726844974203873583345765916594799602432595524124241833895661436855810226926198456320000000 : Int) false,decode_split denominator ibox40 0 (112429034726844974203873583345765916594799602432595524124241833895661436855810226926198456320000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_41 h,accepted_44 h⟩
private noncomputable def tree39 : TapeTree := .face 3 false (candidateRows ibox39) tree40
attribute [irreducible] tree39
private theorem sign_39 : ((computed denominator ibox39).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_39 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox39) tree39 = true := by
  simp only [tree39,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox39,?_,accepted_40 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox39)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox39).gradient 3).hi) denominator_positive).1 sign_39
private noncomputable def tree38 : TapeTree := .split 2 (((799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree39 tree47
attribute [irreducible] tree38
private theorem accepted_38 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox38) tree38 = true := by
  simp only [tree38,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox38 2 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) false,decode_split denominator ibox38 2 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_39 h,accepted_47 h⟩
private noncomputable def tree37 : TapeTree := .centered (candidateRows ibox37) (candidateRows (FixedTape.midBox ibox37))
attribute [irreducible] tree37
private theorem sign_37 : 2*denominator*(computed denominator (FixedTape.midBox ibox37)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox37).gradient k).lo.natAbs ((computed denominator ibox37).gradient k).hi.natAbs : Int)*((ibox37 k).hi-(ibox37 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox37
    (computed denominator ibox37) (computed denominator (FixedTape.midBox ibox37))
    (by decide +kernel)
private theorem midpoint_even_37 : ∀ k, 2 ∣ (ibox37 k).lo+(ibox37 k).hi := by decide +kernel
private theorem accepted_37 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox37) tree37 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox37 midpoint_even_37
  simp only [tree37,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox37,candidate_valid h (FixedTape.midBox ibox37),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox37 212 (FixedTape.rowsAux denominator ibox37 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox37) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_37
private noncomputable def tree36 : TapeTree := .face 0 false (candidateRows ibox36) tree37
attribute [irreducible] tree36
private theorem sign_36 : ((computed denominator ibox36).gradient 0).hi ≤ 0 := by decide +kernel
private theorem accepted_36 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox36) tree36 = true := by
  simp only [tree36,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox36,?_,accepted_37 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox36)).gradient 0).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox36).gradient 0).hi) denominator_positive).1 sign_36
private noncomputable def tree35 : TapeTree := .centered (candidateRows ibox35) (candidateRows (FixedTape.midBox ibox35))
attribute [irreducible] tree35
private theorem sign_35 : 2*denominator*(computed denominator (FixedTape.midBox ibox35)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox35).gradient k).lo.natAbs ((computed denominator ibox35).gradient k).hi.natAbs : Int)*((ibox35 k).hi-(ibox35 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox35
    (computed denominator ibox35) (computed denominator (FixedTape.midBox ibox35))
    (by decide +kernel)
private theorem midpoint_even_35 : ∀ k, 2 ∣ (ibox35 k).lo+(ibox35 k).hi := by decide +kernel
private theorem accepted_35 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox35) tree35 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox35 midpoint_even_35
  simp only [tree35,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox35,candidate_valid h (FixedTape.midBox ibox35),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox35 212 (FixedTape.rowsAux denominator ibox35 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox35) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_35
private noncomputable def tree34 : TapeTree := .face 1 false (candidateRows ibox34) tree35
attribute [irreducible] tree34
private theorem sign_34 : ((computed denominator ibox34).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_34 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox34) tree34 = true := by
  simp only [tree34,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox34,?_,accepted_35 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox34)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox34).gradient 1).hi) denominator_positive).1 sign_34
private noncomputable def tree33 : TapeTree := .face 2 true (candidateRows ibox33) tree34
attribute [irreducible] tree33
private theorem sign_33 : 0 ≤ ((computed denominator ibox33).gradient 2).lo := by decide +kernel
private theorem accepted_33 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox33) tree33 = true := by
  simp only [tree33,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox33,?_,accepted_34 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox33)).gradient 2).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox33).gradient 2).lo) denominator_positive).2 sign_33
private noncomputable def tree32 : TapeTree := .split 1 (((799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree33 tree36
attribute [irreducible] tree32
private theorem accepted_32 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox32) tree32 = true := by
  simp only [tree32,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox32 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) false,decode_split denominator ibox32 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_33 h,accepted_36 h⟩
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
private noncomputable def tree30 : TapeTree := .face 2 true (candidateRows ibox30) tree31
attribute [irreducible] tree30
private theorem sign_30 : 0 ≤ ((computed denominator ibox30).gradient 2).lo := by decide +kernel
private theorem accepted_30 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox30) tree30 = true := by
  simp only [tree30,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox30,?_,accepted_31 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox30)).gradient 2).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox30).gradient 2).lo) denominator_positive).2 sign_30
private noncomputable def tree29 : TapeTree := .face 0 false (candidateRows ibox29) tree30
attribute [irreducible] tree29
private theorem sign_29 : ((computed denominator ibox29).gradient 0).hi ≤ 0 := by decide +kernel
private theorem accepted_29 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox29) tree29 = true := by
  simp only [tree29,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox29,?_,accepted_30 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox29)).gradient 0).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox29).gradient 0).hi) denominator_positive).1 sign_29
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
private noncomputable def tree27 : TapeTree := .face 0 false (candidateRows ibox27) tree28
attribute [irreducible] tree27
private theorem sign_27 : ((computed denominator ibox27).gradient 0).hi ≤ 0 := by decide +kernel
private theorem accepted_27 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox27) tree27 = true := by
  simp only [tree27,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox27,?_,accepted_28 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox27)).gradient 0).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox27).gradient 0).hi) denominator_positive).1 sign_27
private noncomputable def tree26 : TapeTree := .centered (candidateRows ibox26) (candidateRows (FixedTape.midBox ibox26))
attribute [irreducible] tree26
private theorem sign_26 : 2*denominator*(computed denominator (FixedTape.midBox ibox26)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox26).gradient k).lo.natAbs ((computed denominator ibox26).gradient k).hi.natAbs : Int)*((ibox26 k).hi-(ibox26 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox26
    (computed denominator ibox26) (computed denominator (FixedTape.midBox ibox26))
    (by decide +kernel)
private theorem midpoint_even_26 : ∀ k, 2 ∣ (ibox26 k).lo+(ibox26 k).hi := by decide +kernel
private theorem accepted_26 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox26) tree26 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox26 midpoint_even_26
  simp only [tree26,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox26,candidate_valid h (FixedTape.midBox ibox26),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox26 212 (FixedTape.rowsAux denominator ibox26 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox26) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_26
private noncomputable def tree25 : TapeTree := .face 1 false (candidateRows ibox25) tree26
attribute [irreducible] tree25
private theorem sign_25 : ((computed denominator ibox25).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_25 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox25) tree25 = true := by
  simp only [tree25,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox25,?_,accepted_26 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox25)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox25).gradient 1).hi) denominator_positive).1 sign_25
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
private noncomputable def tree23 : TapeTree := .face 1 false (candidateRows ibox23) tree24
attribute [irreducible] tree23
private theorem sign_23 : ((computed denominator ibox23).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_23 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox23) tree23 = true := by
  simp only [tree23,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox23,?_,accepted_24 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox23)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox23).gradient 1).hi) denominator_positive).1 sign_23
private noncomputable def tree22 : TapeTree := .split 0 (((102018938918803769927606184674623766618163937306752631213869685376906040649301704487699742720000000 : Int) : ℚ)/(denominator : ℚ)) tree23 tree25
attribute [irreducible] tree22
private theorem accepted_22 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox22) tree22 = true := by
  simp only [tree22,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox22 0 (102018938918803769927606184674623766618163937306752631213869685376906040649301704487699742720000000 : Int) false,decode_split denominator ibox22 0 (102018938918803769927606184674623766618163937306752631213869685376906040649301704487699742720000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_23 h,accepted_25 h⟩
private noncomputable def tree21 : TapeTree := .split 1 (((399747679028782116289410819761581346491347217126336210527181022692619845632000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree22 tree27
attribute [irreducible] tree21
private theorem accepted_21 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox21) tree21 = true := by
  simp only [tree21,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox21 1 (399747679028782116289410819761581346491347217126336210527181022692619845632000000000000000000000000 : Int) false,decode_split denominator ibox21 1 (399747679028782116289410819761581346491347217126336210527181022692619845632000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_22 h,accepted_27 h⟩
private noncomputable def tree20 : TapeTree := .face 2 true (candidateRows ibox20) tree21
attribute [irreducible] tree20
private theorem sign_20 : 0 ≤ ((computed denominator ibox20).gradient 2).lo := by decide +kernel
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox20,?_,accepted_21 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox20)).gradient 2).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox20).gradient 2).lo) denominator_positive).2 sign_20
private noncomputable def tree19 : TapeTree := .split 1 (((799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree20 tree29
attribute [irreducible] tree19
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox19 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) false,decode_split denominator ibox19 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_20 h,accepted_29 h⟩
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
private noncomputable def tree16 : TapeTree := .split 1 (((799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree17 tree18
attribute [irreducible] tree16
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox16 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) false,decode_split denominator ibox16 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) true]
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
private noncomputable def tree14 : TapeTree := .centered (candidateRows ibox14) (candidateRows (FixedTape.midBox ibox14))
attribute [irreducible] tree14
private theorem sign_14 : 2*denominator*(computed denominator (FixedTape.midBox ibox14)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox14).gradient k).lo.natAbs ((computed denominator ibox14).gradient k).hi.natAbs : Int)*((ibox14 k).hi-(ibox14 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox14
    (computed denominator ibox14) (computed denominator (FixedTape.midBox ibox14))
    (by decide +kernel)
private theorem midpoint_even_14 : ∀ k, 2 ∣ (ibox14 k).lo+(ibox14 k).hi := by decide +kernel
private theorem accepted_14 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox14) tree14 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox14 midpoint_even_14
  simp only [tree14,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox14,candidate_valid h (FixedTape.midBox ibox14),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox14 212 (FixedTape.rowsAux denominator ibox14 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox14) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_14
private noncomputable def tree13 : TapeTree := .split 1 (((799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree14 tree15
attribute [irreducible] tree13
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox13 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) false,decode_split denominator ibox13 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_14 h,accepted_15 h⟩
private noncomputable def tree12 : TapeTree := .split 0 (((102018938918803769927606184674623766618163937306752631213869685376906040649301704487699742720000000 : Int) : ℚ)/(denominator : ℚ)) tree13 tree16
attribute [irreducible] tree12
private theorem accepted_12 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox12) tree12 = true := by
  simp only [tree12,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox12 0 (102018938918803769927606184674623766618163937306752631213869685376906040649301704487699742720000000 : Int) false,decode_split denominator ibox12 0 (102018938918803769927606184674623766618163937306752631213869685376906040649301704487699742720000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_13 h,accepted_16 h⟩
private noncomputable def tree11 : TapeTree := .face 3 false (candidateRows ibox11) tree12
attribute [irreducible] tree11
private theorem sign_11 : ((computed denominator ibox11).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox11,?_,accepted_12 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox11)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox11).gradient 3).hi) denominator_positive).1 sign_11
private noncomputable def tree10 : TapeTree := .split 2 (((1199243037086346348868232459284744039474041651379008631581543068077859536896000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree11 tree19
attribute [irreducible] tree10
private theorem accepted_10 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox10) tree10 = true := by
  simp only [tree10,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox10 2 (1199243037086346348868232459284744039474041651379008631581543068077859536896000000000000000000000000 : Int) false,decode_split denominator ibox10 2 (1199243037086346348868232459284744039474041651379008631581543068077859536896000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_11 h,accepted_19 h⟩
private noncomputable def tree9 : TapeTree := .split 0 (((104100958080412010782859664408852196613491070331921209795944115080657119890603408975399485440000000 : Int) : ℚ)/(denominator : ℚ)) tree10 tree32
attribute [irreducible] tree9
private theorem accepted_9 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox9) tree9 = true := by
  simp only [tree9,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox9 0 (104100958080412010782859664408852196613491070331921209795944115080657119890603408975399485440000000 : Int) false,decode_split denominator ibox9 0 (104100958080412010782859664408852196613491070331921209795944115080657119890603408975399485440000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_10 h,accepted_32 h⟩
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
private noncomputable def tree6 : TapeTree := .split 1 (((799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree7 tree8
attribute [irreducible] tree6
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox6 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) false,decode_split denominator ibox6 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_7 h,accepted_8 h⟩
private noncomputable def tree5 : TapeTree := .direct (candidateRows ibox5)
attribute [irreducible] tree5
private theorem sign_5 : (computed denominator ibox5).value.hi ≤ 0 := by decide +kernel
private theorem accepted_5 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox5) tree5 = true := by
  simp only [tree5,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  refine ⟨root_in_range,candidate_valid h ibox5,?_⟩
  rw [candidate_root]
  simpa [FixedTape.decodeRow,FixedTape.decode] using (h.child_10.2.2.2.1 denominator (computed denominator ibox5).value.hi denominator_positive).1 sign_5
private noncomputable def tree4 : TapeTree := .face 1 true (candidateRows ibox4) tree5
attribute [irreducible] tree4
private theorem sign_4 : 0 ≤ ((computed denominator ibox4).gradient 1).lo := by decide +kernel
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox4,?_,accepted_5 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox4)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox4).gradient 1).lo) denominator_positive).2 sign_4
private noncomputable def tree3 : TapeTree := .split 0 (((104100958080412010782859664408852196613491070331921209795944115080657119890603408975399485440000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree6
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 0 (104100958080412010782859664408852196613491070331921209795944115080657119890603408975399485440000000 : Int) false,decode_split denominator ibox3 0 (104100958080412010782859664408852196613491070331921209795944115080657119890603408975399485440000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_6 h⟩
private noncomputable def tree2 : TapeTree := .face 3 false (candidateRows ibox2) tree3
attribute [irreducible] tree2
private theorem sign_2 : ((computed denominator ibox2).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox2,?_,accepted_3 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox2)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox2).gradient 3).hi) denominator_positive).1 sign_2
private noncomputable def tree1 : TapeTree := .split 2 (((799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree2 tree9
attribute [irreducible] tree1
private theorem accepted_1 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox1) tree1 = true := by
  simp only [tree1,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox1 2 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) false,decode_split denominator ibox1 2 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_2 h,accepted_9 h⟩
private noncomputable def tree0 : TapeTree := .split 0 (((108264996403628492493366623877309056604145336382258366960092974488159278373206817950798970880000000 : Int) : ℚ)/(denominator : ℚ)) tree1 tree38
attribute [irreducible] tree0
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox0 0 (108264996403628492493366623877309056604145336382258366960092974488159278373206817950798970880000000 : Int) false,decode_split denominator ibox0 0 (108264996403628492493366623877309056604145336382258366960092974488159278373206817950798970880000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_1 h,accepted_38 h⟩
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (1/16 : ℚ) (7291666666666667/100000000000000000 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 212 = e220 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (1/16 : ℚ) (7291666666666667/100000000000000000 : ℚ)) x → eval e220 x ≤ 0 := by
  have hb := h.child_4 tape 212 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell21_low_internal

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell21_low_internal
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((1/16 : ℚ) : ℝ) < p ∧ p ≤ ((7291666666666667/100000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 21 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 21 p)
    (hk0 : ((7291666666666667/100000000000000000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((1/16 : ℚ) : ℝ))
    (hk1 : ((7291666666666667/100000000000000000 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((1/16 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r), internalResidual (0 : Fin 9) a p A r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell21_low_internal.cell_bound h.child_8 h.child_9 (Cell21_low_internal.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell21_low_internal
