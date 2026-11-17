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
namespace Cell21_high_internal_bottom
private noncomputable def qValues : Fin 1 → ℚ := ![(0/1 : ℚ)]
private noncomputable abbrev e2 : PolyExpr := SharedFiniteSemantics13.e2 qValues
private noncomputable abbrev e6 : PolyExpr := SharedFiniteSemantics13.e6 qValues
private noncomputable abbrev e11 : PolyExpr := SharedFiniteSemantics13.e11 qValues
private noncomputable abbrev e15 : PolyExpr := SharedFiniteSemantics13.e15 qValues
private noncomputable abbrev e38 : PolyExpr := SharedFiniteSemantics13.e38 qValues
private noncomputable abbrev e219 : PolyExpr := SharedFiniteSemantics13.e219 qValues
private noncomputable abbrev node_1 := SharedFiniteSemantics13.node_1 qValues
private noncomputable abbrev node_2 := SharedFiniteSemantics13.node_2 qValues
private noncomputable abbrev node_3 := SharedFiniteSemantics13.node_3 qValues
private noncomputable abbrev node_4 := SharedFiniteSemantics13.node_4 qValues
private noncomputable abbrev node_5 := SharedFiniteSemantics13.node_5 qValues
private noncomputable abbrev node_6 := SharedFiniteSemantics13.node_6 qValues
private noncomputable abbrev node_7 := SharedFiniteSemantics13.node_7 qValues
private noncomputable abbrev node_8 := SharedFiniteSemantics13.node_8 qValues
private noncomputable abbrev node_9 := SharedFiniteSemantics13.node_9 qValues
private noncomputable abbrev node_10 := SharedFiniteSemantics13.node_10 qValues
private noncomputable abbrev node_11 := SharedFiniteSemantics13.node_11 qValues
private noncomputable abbrev node_13 := SharedFiniteSemantics13.node_13 qValues
private noncomputable abbrev node_14 := SharedFiniteSemantics13.node_14 qValues
private noncomputable abbrev node_15 := SharedFiniteSemantics13.node_15 qValues
private noncomputable abbrev node_37 := SharedFiniteSemantics13.node_37 qValues
private noncomputable abbrev node_38 := SharedFiniteSemantics13.node_38 qValues
private noncomputable abbrev node_179 := SharedFiniteSemantics13.node_179 qValues
private noncomputable abbrev node_180 := SharedFiniteSemantics13.node_180 qValues
private noncomputable abbrev node_181 := SharedFiniteSemantics13.node_181 qValues
private noncomputable abbrev node_182 := SharedFiniteSemantics13.node_182 qValues
private noncomputable abbrev node_183 := SharedFiniteSemantics13.node_183 qValues
private noncomputable abbrev node_184 := SharedFiniteSemantics13.node_184 qValues
private noncomputable abbrev node_185 := SharedFiniteSemantics13.node_185 qValues
private noncomputable abbrev node_186 := SharedFiniteSemantics13.node_186 qValues
private noncomputable abbrev node_187 := SharedFiniteSemantics13.node_187 qValues
private noncomputable abbrev node_188 := SharedFiniteSemantics13.node_188 qValues
private noncomputable abbrev node_189 := SharedFiniteSemantics13.node_189 qValues
private noncomputable abbrev node_190 := SharedFiniteSemantics13.node_190 qValues
private noncomputable abbrev node_192 := SharedFiniteSemantics13.node_192 qValues
private noncomputable abbrev node_193 := SharedFiniteSemantics13.node_193 qValues
private noncomputable abbrev node_194 := SharedFiniteSemantics13.node_194 qValues
private noncomputable abbrev node_199 := SharedFiniteSemantics13.node_199 qValues
private noncomputable abbrev node_200 := SharedFiniteSemantics13.node_200 qValues
private noncomputable abbrev node_201 := SharedFiniteSemantics13.node_201 qValues
private noncomputable abbrev node_218 := SharedFiniteSemantics13.node_218 qValues
private noncomputable abbrev node_219 := SharedFiniteSemantics13.node_219 qValues
private noncomputable abbrev semantic_H_36 := SharedFiniteSemantics13.semantic_H_36 qValues
private noncomputable abbrev semantic_psi_217 := SharedFiniteSemantics13.semantic_psi_217 qValues
private noncomputable abbrev semantic_Hd_178 := SharedFiniteSemantics13.semantic_Hd_178 qValues
private noncomputable def aPoint (x : Fin 4 → ℝ) : ℝ := x 0*x 1
private noncomputable def rPoint (x : Fin 4 → ℝ) : ℝ := bStar+(1-bStar)*x 3
private noncomputable def capPoint (x : Fin 4 → ℝ) : ℝ := x 0+(bStar-x 0)*x 2
private noncomputable def yPoint (x : Fin 4 → ℝ) : ℝ := aPoint x+capPoint x-x 0
private theorem point_6 (x : Fin 4 → ℝ) : eval e6 x = aPoint x := by
  simp only [node_2,node_3,node_6] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_15 (x : Fin 4 → ℝ) : eval e15 x = rPoint x := by
  simp only [node_5,node_7,node_13,node_14,node_15] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_2 (x : Fin 4 → ℝ) : eval e2 x = x 0 := by
  simp only [node_2] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_11 (x : Fin 4 → ℝ) : eval e11 x = capPoint x := by
  simp only [node_2,node_4,node_7,node_8,node_9,node_10,node_11] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_38 (x : Fin 4 → ℝ) : eval e38 x = yPoint x := by
  simp only [node_2,node_3,node_4,node_6,node_7,node_8,node_9,node_10,node_11,node_37,node_38] <;>
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
    (1)*eval e219 x = (x 0*(1-x 0))*(aPoint x+priceLambda 21 (x 0)*(HStar (yPoint x)-HStar (aPoint x)-HStar (capPoint x))+priceTau 21 (x 0)*psiStar (rPoint x)+(0)-(0)) := by
  have hp0 : x 0 ≠ 0 := ne_of_gt hp.1
  have hp1 : x 0 ≠ 1 := ne_of_lt hp.2
  have heps : 1-x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  rw [price_lambda_normal _ hp,price_tau_normal _ hp]
  simp only [node_1,node_8,node_179,node_180,node_181,node_182,node_183,node_184,node_185,node_186,node_187,node_188,node_189,node_190,node_192,node_193,node_194,node_199,node_200,node_201,node_218,node_219,semantic_H_36,semantic_psi_217,semantic_Hd_178,point_6,point_15,point_2,point_11,point_38]
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
    (1)*eval e219 x = (x 0*(1-x 0))*(internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,if_pos hA,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (1/16 : ℚ) (7291666666666667/100000000000000000 : ℚ)) x → eval e219 x ≤ 0)
    (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((1/16 : ℚ) : ℝ) < p ∧ p ≤ ((7291666666666667/100000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 21 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 21 p)
    (hkb : ((7291666666666667/100000000000000000 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((1/16 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r)
    (hcase : A ≤ bStar) :
    internalResidual (0 : Fin 9) a p A r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxA,hxr⟩ := h6 (1/16 : ℚ) (7291666666666667/100000000000000000 : ℚ) bStar p a A r hpcell hkb hr ha hap hpA hcase
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,capPoint] using hxa
  have hAx : capPoint x = A := by simpa only [aPoint,rPoint,capPoint] using hxA
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,capPoint] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 21 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 21 (x 0) := by simpa only [hxp] using hT
  have hAb : A ≤ bStar := hcase
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
.mul 1 2,
.const (2840189/5000000 : ℚ),
.neg 1,
.add 6 7,
.mul 8 3,
.add 1 9,
.const (2159811/5000000 : ℚ),
.mul 11 4,
.add 6 12,
.const (1085/4818 : ℚ),
.mul 14 5,
.mul 5 5,
.const (19/146 : ℚ),
.mul 17 16,
.mul 5 16,
.const (35/438 : ℚ),
.mul 20 19,
.add 18 21,
.mul 16 16,
.mul 23 23,
.mul 24 24,
.mul 25 25,
.mul 5 26,
.const (1/66 : ℚ),
.mul 28 27,
.add 22 29,
.neg 30,
.add 15 31,
.const (4818/3733 : ℚ),
.mul 33 32,
.add 5 10,
.add 35 7,
.neg 5,
.add 1 37,
.add 10 36,
.mul 17 39,
.mul 10 10,
.mul 10 36,
.add 41 42,
.mul 36 36,
.add 43 44,
.mul 20 45,
.add 40 46,
.mul 41 41,
.mul 48 48,
.mul 49 49,
.mul 50 50,
.mul 10 41,
.mul 52 52,
.mul 10 53,
.mul 54 54,
.mul 10 55,
.mul 56 56,
.mul 10 57,
.mul 58 36,
.add 51 59,
.mul 57 44,
.add 60 61,
.mul 55 55,
.mul 10 63,
.mul 36 44,
.mul 64 65,
.add 62 66,
.mul 44 44,
.mul 63 68,
.add 67 69,
.mul 53 53,
.mul 10 71,
.mul 72 72,
.mul 10 73,
.mul 36 68,
.mul 74 75,
.add 70 76,
.mul 65 65,
.mul 73 78,
.add 77 79,
.mul 71 71,
.mul 10 81,
.mul 36 78,
.mul 82 83,
.add 80 84,
.mul 68 68,
.mul 81 86,
.add 85 87,
.mul 10 48,
.mul 89 89,
.mul 10 90,
.mul 91 91,
.mul 10 92,
.mul 36 86,
.mul 93 94,
.add 88 95,
.mul 75 75,
.mul 92 97,
.add 96 98,
.mul 90 90,
.mul 10 100,
.mul 36 97,
.mul 101 102,
.add 99 103,
.mul 78 78,
.mul 100 105,
.add 104 106,
.mul 10 49,
.mul 108 108,
.mul 10 109,
.mul 36 105,
.mul 110 111,
.add 107 112,
.mul 83 83,
.mul 109 114,
.add 113 115,
.mul 10 50,
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
.mul 10 166,
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
.add 0 7,
.mul 1 187,
.const (-145513/100000 : ℚ),
.add 186 189,
.mul 190 188,
.mul 5 188,
.mul 182 178,
.add 192 193,
.const (19/73 : ℚ),
.mul 195 13,
.mul 13 13,
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
private noncomputable def ssaQVals : Fin 16 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(2159811/5000000 : ℚ),(1085/4818 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(4818/3733 : ℚ),(-2520631455420736673911951830159397/1241245782574667063865317090560000 : ℚ),(36799418511893608671875000000/969723267636458643644778977 : ℚ),(-1196385022177226809515965750959/2260079914250000723225572560000 : ℚ),(1061454525841096250000000000/28250998928125009040319657 : ℚ),(-145513/100000 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ)]
private theorem ssa_tape : MetricDistortion.OptimizedSSAFinite0.S_e2b3373e00072a5a.p213 ssaQVals = tape := by rfl
private noncomputable def computed (D : Int) (B : Fin 4 → FixedTape.I) : FixedTape.Row :=
  MetricDistortion.OptimizedSSAFinite0.S_e2b3373e00072a5a.computed ssaQVals D B
private theorem ssa_matches (D : Int) (B : Fin 4 → FixedTape.I) :
    (FixedTape.rowsAux D B [] tape).getD 212 FixedTape.zeroRow = computed D B := by
  rw [←ssa_tape]
  exact MetricDistortion.OptimizedSSAFinite0.S_e2b3373e00072a5a.ssa_matches ssaQVals D B

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
private noncomputable def ibox1 : Fin 4 → FixedTape.I := faceI ibox0 3 false
private noncomputable def ibox2 : Fin 4 → FixedTape.I := splitI ibox1 0 108264996403628492493366623877309056604145336382258366960092974488159278373206817950798970880000000 false
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 2 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 0 104100958080412010782859664408852196613491070331921209795944115080657119890603408975399485440000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox4 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 false
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox4 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 true
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox3 0 104100958080412010782859664408852196613491070331921209795944115080657119890603408975399485440000000 true
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox7 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 false
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox7 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 true
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox2 2 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 true
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox10 0 104100958080412010782859664408852196613491070331921209795944115080657119890603408975399485440000000 false
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox11 2 1199243037086346348868232459284744039474041651379008631581543068077859536896000000000000000000000000 false
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox12 0 102018938918803769927606184674623766618163937306752631213869685376906040649301704487699742720000000 false
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox13 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 false
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox13 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 true
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox12 0 102018938918803769927606184674623766618163937306752631213869685376906040649301704487699742720000000 true
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox11 2 1199243037086346348868232459284744039474041651379008631581543068077859536896000000000000000000000000 true
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox17 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 false
private noncomputable def ibox19 : Fin 4 → FixedTape.I := faceI ibox18 2 true
private noncomputable def ibox20 : Fin 4 → FixedTape.I := faceI ibox19 1 false
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox17 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 true
private noncomputable def ibox22 : Fin 4 → FixedTape.I := faceI ibox21 0 false
private noncomputable def ibox23 : Fin 4 → FixedTape.I := splitI ibox10 0 104100958080412010782859664408852196613491070331921209795944115080657119890603408975399485440000000 true
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox23 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 false
private noncomputable def ibox25 : Fin 4 → FixedTape.I := faceI ibox24 2 true
private noncomputable def ibox26 : Fin 4 → FixedTape.I := faceI ibox25 1 false
private noncomputable def ibox27 : Fin 4 → FixedTape.I := splitI ibox23 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 true
private noncomputable def ibox28 : Fin 4 → FixedTape.I := faceI ibox27 0 false
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox1 0 108264996403628492493366623877309056604145336382258366960092974488159278373206817950798970880000000 true
private noncomputable def ibox30 : Fin 4 → FixedTape.I := splitI ibox29 2 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 false
private noncomputable def ibox31 : Fin 4 → FixedTape.I := splitI ibox30 0 112429034726844974203873583345765916594799602432595524124241833895661436855810226926198456320000000 false
private noncomputable def ibox32 : Fin 4 → FixedTape.I := splitI ibox31 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 false
private noncomputable def ibox33 : Fin 4 → FixedTape.I := splitI ibox31 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 true
private noncomputable def ibox34 : Fin 4 → FixedTape.I := splitI ibox30 0 112429034726844974203873583345765916594799602432595524124241833895661436855810226926198456320000000 true
private noncomputable def ibox35 : Fin 4 → FixedTape.I := splitI ibox29 2 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 true
private noncomputable def ibox36 : Fin 4 → FixedTape.I := splitI ibox35 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 false
private noncomputable def ibox37 : Fin 4 → FixedTape.I := faceI ibox36 2 true
private noncomputable def ibox38 : Fin 4 → FixedTape.I := faceI ibox37 1 false
private noncomputable def ibox39 : Fin 4 → FixedTape.I := splitI ibox35 1 799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 true
private noncomputable def ibox40 : Fin 4 → FixedTape.I := faceI ibox39 0 false
private noncomputable def tree40 : TapeTree := .direct (candidateRows ibox40)
attribute [irreducible] tree40
private theorem sign_40 : (computed denominator ibox40).value.hi ≤ 0 := by decide +kernel
private theorem accepted_40 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox40) tree40 = true := by
  simp only [tree40,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  refine ⟨root_in_range,candidate_valid h ibox40,?_⟩
  rw [candidate_root]
  simpa [FixedTape.decodeRow,FixedTape.decode] using (h.child_10.2.2.2.1 denominator (computed denominator ibox40).value.hi denominator_positive).1 sign_40
private noncomputable def tree39 : TapeTree := .face 0 false (candidateRows ibox39) tree40
attribute [irreducible] tree39
private theorem sign_39 : ((computed denominator ibox39).gradient 0).hi ≤ 0 := by decide +kernel
private theorem accepted_39 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox39) tree39 = true := by
  simp only [tree39,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox39,?_,accepted_40 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox39)).gradient 0).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox39).gradient 0).hi) denominator_positive).1 sign_39
private noncomputable def tree38 : TapeTree := .direct (candidateRows ibox38)
attribute [irreducible] tree38
private theorem sign_38 : (computed denominator ibox38).value.hi ≤ 0 := by decide +kernel
private theorem accepted_38 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox38) tree38 = true := by
  simp only [tree38,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  refine ⟨root_in_range,candidate_valid h ibox38,?_⟩
  rw [candidate_root]
  simpa [FixedTape.decodeRow,FixedTape.decode] using (h.child_10.2.2.2.1 denominator (computed denominator ibox38).value.hi denominator_positive).1 sign_38
private noncomputable def tree37 : TapeTree := .face 1 false (candidateRows ibox37) tree38
attribute [irreducible] tree37
private theorem sign_37 : ((computed denominator ibox37).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_37 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox37) tree37 = true := by
  simp only [tree37,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox37,?_,accepted_38 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox37)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox37).gradient 1).hi) denominator_positive).1 sign_37
private noncomputable def tree36 : TapeTree := .face 2 true (candidateRows ibox36) tree37
attribute [irreducible] tree36
private theorem sign_36 : 0 ≤ ((computed denominator ibox36).gradient 2).lo := by decide +kernel
private theorem accepted_36 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox36) tree36 = true := by
  simp only [tree36,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox36,?_,accepted_37 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox36)).gradient 2).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox36).gradient 2).lo) denominator_positive).2 sign_36
private noncomputable def tree35 : TapeTree := .split 1 (((799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree36 tree39
attribute [irreducible] tree35
private theorem accepted_35 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox35) tree35 = true := by
  simp only [tree35,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox35 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) false,decode_split denominator ibox35 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_36 h,accepted_39 h⟩
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
private noncomputable def tree32 : TapeTree := .direct (candidateRows ibox32)
attribute [irreducible] tree32
private theorem sign_32 : (computed denominator ibox32).value.hi ≤ 0 := by decide +kernel
private theorem accepted_32 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox32) tree32 = true := by
  simp only [tree32,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  refine ⟨root_in_range,candidate_valid h ibox32,?_⟩
  rw [candidate_root]
  simpa [FixedTape.decodeRow,FixedTape.decode] using (h.child_10.2.2.2.1 denominator (computed denominator ibox32).value.hi denominator_positive).1 sign_32
private noncomputable def tree31 : TapeTree := .split 1 (((799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree32 tree33
attribute [irreducible] tree31
private theorem accepted_31 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox31) tree31 = true := by
  simp only [tree31,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox31 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) false,decode_split denominator ibox31 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_32 h,accepted_33 h⟩
private noncomputable def tree30 : TapeTree := .split 0 (((112429034726844974203873583345765916594799602432595524124241833895661436855810226926198456320000000 : Int) : ℚ)/(denominator : ℚ)) tree31 tree34
attribute [irreducible] tree30
private theorem accepted_30 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox30) tree30 = true := by
  simp only [tree30,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox30 0 (112429034726844974203873583345765916594799602432595524124241833895661436855810226926198456320000000 : Int) false,decode_split denominator ibox30 0 (112429034726844974203873583345765916594799602432595524124241833895661436855810226926198456320000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_31 h,accepted_34 h⟩
private noncomputable def tree29 : TapeTree := .split 2 (((799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree30 tree35
attribute [irreducible] tree29
private theorem accepted_29 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox29) tree29 = true := by
  simp only [tree29,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox29 2 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) false,decode_split denominator ibox29 2 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_30 h,accepted_35 h⟩
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
private noncomputable def tree26 : TapeTree := .direct (candidateRows ibox26)
attribute [irreducible] tree26
private theorem sign_26 : (computed denominator ibox26).value.hi ≤ 0 := by decide +kernel
private theorem accepted_26 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox26) tree26 = true := by
  simp only [tree26,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  refine ⟨root_in_range,candidate_valid h ibox26,?_⟩
  rw [candidate_root]
  simpa [FixedTape.decodeRow,FixedTape.decode] using (h.child_10.2.2.2.1 denominator (computed denominator ibox26).value.hi denominator_positive).1 sign_26
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
private noncomputable def tree24 : TapeTree := .face 2 true (candidateRows ibox24) tree25
attribute [irreducible] tree24
private theorem sign_24 : 0 ≤ ((computed denominator ibox24).gradient 2).lo := by decide +kernel
private theorem accepted_24 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox24) tree24 = true := by
  simp only [tree24,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox24,?_,accepted_25 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox24)).gradient 2).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox24).gradient 2).lo) denominator_positive).2 sign_24
private noncomputable def tree23 : TapeTree := .split 1 (((799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree24 tree27
attribute [irreducible] tree23
private theorem accepted_23 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox23) tree23 = true := by
  simp only [tree23,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox23 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) false,decode_split denominator ibox23 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_24 h,accepted_27 h⟩
private noncomputable def tree22 : TapeTree := .centered (candidateRows ibox22) (candidateRows (FixedTape.midBox ibox22))
attribute [irreducible] tree22
private theorem sign_22 : 2*denominator*(computed denominator (FixedTape.midBox ibox22)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox22).gradient k).lo.natAbs ((computed denominator ibox22).gradient k).hi.natAbs : Int)*((ibox22 k).hi-(ibox22 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox22
    (computed denominator ibox22) (computed denominator (FixedTape.midBox ibox22))
    (by decide +kernel)
private theorem midpoint_even_22 : ∀ k, 2 ∣ (ibox22 k).lo+(ibox22 k).hi := by decide +kernel
private theorem accepted_22 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox22) tree22 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox22 midpoint_even_22
  simp only [tree22,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox22,candidate_valid h (FixedTape.midBox ibox22),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox22 212 (FixedTape.rowsAux denominator ibox22 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox22) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_22
private noncomputable def tree21 : TapeTree := .face 0 false (candidateRows ibox21) tree22
attribute [irreducible] tree21
private theorem sign_21 : ((computed denominator ibox21).gradient 0).hi ≤ 0 := by decide +kernel
private theorem accepted_21 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox21) tree21 = true := by
  simp only [tree21,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox21,?_,accepted_22 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox21)).gradient 0).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox21).gradient 0).hi) denominator_positive).1 sign_21
private noncomputable def tree20 : TapeTree := .direct (candidateRows ibox20)
attribute [irreducible] tree20
private theorem sign_20 : (computed denominator ibox20).value.hi ≤ 0 := by decide +kernel
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  refine ⟨root_in_range,candidate_valid h ibox20,?_⟩
  rw [candidate_root]
  simpa [FixedTape.decodeRow,FixedTape.decode] using (h.child_10.2.2.2.1 denominator (computed denominator ibox20).value.hi denominator_positive).1 sign_20
private noncomputable def tree19 : TapeTree := .face 1 false (candidateRows ibox19) tree20
attribute [irreducible] tree19
private theorem sign_19 : ((computed denominator ibox19).gradient 1).hi ≤ 0 := by decide +kernel
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox19,?_,accepted_20 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox19)).gradient 1).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox19).gradient 1).hi) denominator_positive).1 sign_19
private noncomputable def tree18 : TapeTree := .face 2 true (candidateRows ibox18) tree19
attribute [irreducible] tree18
private theorem sign_18 : 0 ≤ ((computed denominator ibox18).gradient 2).lo := by decide +kernel
private theorem accepted_18 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox18) tree18 = true := by
  simp only [tree18,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox18,?_,accepted_19 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox18)).gradient 2).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox18).gradient 2).lo) denominator_positive).2 sign_18
private noncomputable def tree17 : TapeTree := .split 1 (((799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree18 tree21
attribute [irreducible] tree17
private theorem accepted_17 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox17) tree17 = true := by
  simp only [tree17,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox17 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) false,decode_split denominator ibox17 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_18 h,accepted_21 h⟩
private noncomputable def tree16 : TapeTree := .centered (candidateRows ibox16) (candidateRows (FixedTape.midBox ibox16))
attribute [irreducible] tree16
private theorem sign_16 : 2*denominator*(computed denominator (FixedTape.midBox ibox16)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox16).gradient k).lo.natAbs ((computed denominator ibox16).gradient k).hi.natAbs : Int)*((ibox16 k).hi-(ibox16 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox16
    (computed denominator ibox16) (computed denominator (FixedTape.midBox ibox16))
    (by decide +kernel)
private theorem midpoint_even_16 : ∀ k, 2 ∣ (ibox16 k).lo+(ibox16 k).hi := by decide +kernel
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox16 midpoint_even_16
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox16,candidate_valid h (FixedTape.midBox ibox16),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox16 212 (FixedTape.rowsAux denominator ibox16 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox16) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_16
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
private noncomputable def tree11 : TapeTree := .split 2 (((1199243037086346348868232459284744039474041651379008631581543068077859536896000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree12 tree17
attribute [irreducible] tree11
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox11 2 (1199243037086346348868232459284744039474041651379008631581543068077859536896000000000000000000000000 : Int) false,decode_split denominator ibox11 2 (1199243037086346348868232459284744039474041651379008631581543068077859536896000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_12 h,accepted_17 h⟩
private noncomputable def tree10 : TapeTree := .split 0 (((104100958080412010782859664408852196613491070331921209795944115080657119890603408975399485440000000 : Int) : ℚ)/(denominator : ℚ)) tree11 tree23
attribute [irreducible] tree10
private theorem accepted_10 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox10) tree10 = true := by
  simp only [tree10,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox10 0 (104100958080412010782859664408852196613491070331921209795944115080657119890603408975399485440000000 : Int) false,decode_split denominator ibox10 0 (104100958080412010782859664408852196613491070331921209795944115080657119890603408975399485440000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_11 h,accepted_23 h⟩
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
private noncomputable def tree7 : TapeTree := .split 1 (((799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree8 tree9
attribute [irreducible] tree7
private theorem accepted_7 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox7) tree7 = true := by
  simp only [tree7,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox7 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) false,decode_split denominator ibox7 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_8 h,accepted_9 h⟩
private noncomputable def tree6 : TapeTree := .centered (candidateRows ibox6) (candidateRows (FixedTape.midBox ibox6))
attribute [irreducible] tree6
private theorem sign_6 : 2*denominator*(computed denominator (FixedTape.midBox ibox6)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox6).gradient k).lo.natAbs ((computed denominator ibox6).gradient k).hi.natAbs : Int)*((ibox6 k).hi-(ibox6 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox6
    (computed denominator ibox6) (computed denominator (FixedTape.midBox ibox6))
    (by decide +kernel)
private theorem midpoint_even_6 : ∀ k, 2 ∣ (ibox6 k).lo+(ibox6 k).hi := by decide +kernel
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox6 midpoint_even_6
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox6,candidate_valid h (FixedTape.midBox ibox6),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox6 212 (FixedTape.rowsAux denominator ibox6 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox6) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_6
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
private noncomputable def tree4 : TapeTree := .split 1 (((799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree5 tree6
attribute [irreducible] tree4
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox4 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) false,decode_split denominator ibox4 1 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_5 h,accepted_6 h⟩
private noncomputable def tree3 : TapeTree := .split 0 (((104100958080412010782859664408852196613491070331921209795944115080657119890603408975399485440000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree7
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 0 (104100958080412010782859664408852196613491070331921209795944115080657119890603408975399485440000000 : Int) false,decode_split denominator ibox3 0 (104100958080412010782859664408852196613491070331921209795944115080657119890603408975399485440000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_7 h⟩
private noncomputable def tree2 : TapeTree := .split 2 (((799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree10
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 2 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) false,decode_split denominator ibox2 2 (799495358057564232578821639523162692982694434252672421054362045385239691264000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_3 h,accepted_10 h⟩
private noncomputable def tree1 : TapeTree := .split 0 (((108264996403628492493366623877309056604145336382258366960092974488159278373206817950798970880000000 : Int) : ℚ)/(denominator : ℚ)) tree2 tree29
attribute [irreducible] tree1
private theorem accepted_1 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox1) tree1 = true := by
  simp only [tree1,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox1 0 (108264996403628492493366623877309056604145336382258366960092974488159278373206817950798970880000000 : Int) false,decode_split denominator ibox1 0 (108264996403628492493366623877309056604145336382258366960092974488159278373206817950798970880000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_2 h,accepted_29 h⟩
private noncomputable def tree0 : TapeTree := .face 3 false (candidateRows ibox0) tree1
attribute [irreducible] tree0
private theorem sign_0 : ((computed denominator ibox0).gradient 3).hi ≤ 0 := by decide +kernel
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 212 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox0,?_,accepted_1 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox0)).gradient 3).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox0).gradient 3).hi) denominator_positive).1 sign_0
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (1/16 : ℚ) (7291666666666667/100000000000000000 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 212 = e219 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (1/16 : ℚ) (7291666666666667/100000000000000000 : ℚ)) x → eval e219 x ≤ 0 := by
  have hb := h.child_4 tape 212 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell21_high_internal_bottom

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell21_high_internal_bottom
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((1/16 : ℚ) : ℝ) < p ∧ p ≤ ((7291666666666667/100000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 21 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 21 p)
    (hkb : ((7291666666666667/100000000000000000 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((1/16 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r)
    (hcase : A ≤ bStar), internalResidual (0 : Fin 9) a p A r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell21_high_internal_bottom.cell_bound h.child_8 h.child_9 (Cell21_high_internal_bottom.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell21_high_internal_bottom
