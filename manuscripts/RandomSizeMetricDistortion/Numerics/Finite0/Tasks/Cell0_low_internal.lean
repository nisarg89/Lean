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
namespace Cell0_low_internal
private noncomputable def qValues : Fin 1 → ℚ := ![(0/1 : ℚ)]
private noncomputable abbrev e2 : PolyExpr := SharedFiniteSemantics1.e2 qValues
private noncomputable abbrev e11 : PolyExpr := SharedFiniteSemantics1.e11 qValues
private noncomputable abbrev e12 : PolyExpr := SharedFiniteSemantics1.e12 qValues
private noncomputable abbrev e16 : PolyExpr := SharedFiniteSemantics1.e16 qValues
private noncomputable abbrev e18 : PolyExpr := SharedFiniteSemantics1.e18 qValues
private noncomputable abbrev e88 : PolyExpr := SharedFiniteSemantics1.e88 qValues
private noncomputable abbrev e91 : PolyExpr := SharedFiniteSemantics1.e91 qValues
private noncomputable abbrev e418 : PolyExpr := SharedFiniteSemantics1.e418 qValues
private noncomputable abbrev node_1 := SharedFiniteSemantics1.node_1 qValues
private noncomputable abbrev node_2 := SharedFiniteSemantics1.node_2 qValues
private noncomputable abbrev node_3 := SharedFiniteSemantics1.node_3 qValues
private noncomputable abbrev node_4 := SharedFiniteSemantics1.node_4 qValues
private noncomputable abbrev node_5 := SharedFiniteSemantics1.node_5 qValues
private noncomputable abbrev node_6 := SharedFiniteSemantics1.node_6 qValues
private noncomputable abbrev node_9 := SharedFiniteSemantics1.node_9 qValues
private noncomputable abbrev node_10 := SharedFiniteSemantics1.node_10 qValues
private noncomputable abbrev node_11 := SharedFiniteSemantics1.node_11 qValues
private noncomputable abbrev node_12 := SharedFiniteSemantics1.node_12 qValues
private noncomputable abbrev node_13 := SharedFiniteSemantics1.node_13 qValues
private noncomputable abbrev node_14 := SharedFiniteSemantics1.node_14 qValues
private noncomputable abbrev node_15 := SharedFiniteSemantics1.node_15 qValues
private noncomputable abbrev node_16 := SharedFiniteSemantics1.node_16 qValues
private noncomputable abbrev node_17 := SharedFiniteSemantics1.node_17 qValues
private noncomputable abbrev node_18 := SharedFiniteSemantics1.node_18 qValues
private noncomputable abbrev node_88 := SharedFiniteSemantics1.node_88 qValues
private noncomputable abbrev node_89 := SharedFiniteSemantics1.node_89 qValues
private noncomputable abbrev node_90 := SharedFiniteSemantics1.node_90 qValues
private noncomputable abbrev node_91 := SharedFiniteSemantics1.node_91 qValues
private noncomputable abbrev node_103 := SharedFiniteSemantics1.node_103 qValues
private noncomputable abbrev node_104 := SharedFiniteSemantics1.node_104 qValues
private noncomputable abbrev node_105 := SharedFiniteSemantics1.node_105 qValues
private noncomputable abbrev node_106 := SharedFiniteSemantics1.node_106 qValues
private noncomputable abbrev node_123 := SharedFiniteSemantics1.node_123 qValues
private noncomputable abbrev node_124 := SharedFiniteSemantics1.node_124 qValues
private noncomputable abbrev node_125 := SharedFiniteSemantics1.node_125 qValues
private noncomputable abbrev node_126 := SharedFiniteSemantics1.node_126 qValues
private noncomputable abbrev node_127 := SharedFiniteSemantics1.node_127 qValues
private noncomputable abbrev node_252 := SharedFiniteSemantics1.node_252 qValues
private noncomputable abbrev node_253 := SharedFiniteSemantics1.node_253 qValues
private noncomputable abbrev node_254 := SharedFiniteSemantics1.node_254 qValues
private noncomputable abbrev node_255 := SharedFiniteSemantics1.node_255 qValues
private noncomputable abbrev node_414 := SharedFiniteSemantics1.node_414 qValues
private noncomputable abbrev node_415 := SharedFiniteSemantics1.node_415 qValues
private noncomputable abbrev node_416 := SharedFiniteSemantics1.node_416 qValues
private noncomputable abbrev node_417 := SharedFiniteSemantics1.node_417 qValues
private noncomputable abbrev node_418 := SharedFiniteSemantics1.node_418 qValues
private noncomputable abbrev semantic_H_39 := SharedFiniteSemantics1.semantic_H_39 qValues
private noncomputable abbrev semantic_H_55 := SharedFiniteSemantics1.semantic_H_55 qValues
private noncomputable abbrev semantic_H_73 := SharedFiniteSemantics1.semantic_H_73 qValues
private noncomputable abbrev semantic_psi_122 := SharedFiniteSemantics1.semantic_psi_122 qValues
private noncomputable abbrev semantic_F0_102 := SharedFiniteSemantics1.semantic_F0_102 qValues
private noncomputable abbrev semantic_pdiff_251 := SharedFiniteSemantics1.semantic_pdiff_251 qValues
private noncomputable abbrev semantic_J_413 := SharedFiniteSemantics1.semantic_J_413 qValues
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
private theorem point_18 (x : Fin 4 → ℝ) : eval e18 x = yPoint x := by
  simp only [node_2,node_3,node_4,node_5,node_6,node_9,node_10,node_11,node_12,node_13,node_14,node_15,node_16,node_17,node_18] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_91 (x : Fin 4 → ℝ) : eval e91 x = rPoint x-capPoint x := by
  simp only [node_1,node_2,node_4,node_5,node_6,node_9,node_10,node_11,node_13,node_14,node_89,node_90,node_91] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_88 (x : Fin 4 → ℝ) : eval e88 x = yPoint x := by
  simp only [node_2,node_3,node_4,node_5,node_6,node_9,node_10,node_11,node_12,node_13,node_14,node_15,node_88] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem price_lambda_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceLambda 0 p = 4*(145513/100000 : ℝ)/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell0,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 0 p = (145513/100000 : ℝ)*(1+4*p-(1/1 : ℝ))/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell0,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (x 0)*eval e418 x = (1)*(aPoint x+priceLambda 0 (x 0)*(HStar (yPoint x)-HStar (aPoint x)-HStar (capPoint x))+priceTau 0 (x 0)*psiStar (rPoint x)+(0)-(0)) := by
  have hp0 : x 0 ≠ 0 := ne_of_gt hp.1
  have hp1 : x 0 ≠ 1 := ne_of_lt hp.2
  have heps : 1-x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  rw [price_lambda_normal _ hp,price_tau_normal _ hp]
  simp only [node_1,node_3,node_103,node_104,node_105,node_106,node_123,node_124,node_125,node_126,node_127,node_252,node_253,node_254,node_255,node_414,node_415,node_416,node_417,node_418,semantic_H_39,semantic_H_55,semantic_H_73,semantic_psi_122,semantic_F0_102,semantic_pdiff_251,semantic_J_413,point_12,point_11,point_2,point_16,point_18,point_91,point_88]
  have hsmall := small_internal_one hs (x 0) (x 1) (capPoint x) (rPoint x) (145513/100000 : ℝ)
  change x 0*(x 1*(1-4*(145513/100000 : ℝ)*sourceF0 (aPoint x)+4*(145513/100000 : ℝ)*psiStar (rPoint x)/sourceDenom)+4*(145513/100000 : ℝ)*(1-x 1)*sourcePD (capPoint x) (rPoint x) (rPoint x-capPoint x)-4*(145513/100000 : ℝ)*x 0*(1-x 1)^2*sourceJ (yPoint x) (capPoint x)) = aPoint x+4*(145513/100000 : ℝ)*(HStar (yPoint x)-HStar (aPoint x)-HStar (capPoint x))/sourceDenom+4*(145513/100000 : ℝ)*x 0*psiStar (rPoint x)/sourceDenom at hsmall
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
  linear_combination hsmall
theorem actual_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) (ha : aPoint x ≤ bStar) (hA : capPoint x ≤ bStar)
    (hL : lambdaStar (x 0) = priceLambda 0 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 0 (x 0)) :
    (x 0)*eval e418 x = (1)*(internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,if_pos hA,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (0/1 : ℚ) (1/4096 : ℚ)) x → eval e418 x ≤ 0)
    (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((0/1 : ℚ) : ℝ) < p ∧ p ≤ ((1/4096 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 0 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 0 p)
    (hk0 : ((1/4096 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((0/1 : ℚ) : ℝ))
    (hk1 : ((1/4096 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((0/1 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r) :
    internalResidual (0 : Fin 9) a p A r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxA,hxr⟩ := h3 (0/1 : ℚ) (1/4096 : ℚ) ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ) p a A r hpcell hk0 hk1 hr ha hap hpA hAr
  have hcut : ((1/4096 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) := by norm_num [bStar]
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxa
  have hAx : capPoint x = A := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxA
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 0 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 0 (x 0) := by simpa only [hxp] using hT
  have hrootb : ((2840189/5000000 : ℚ) : ℝ) ≤ bStar := by norm_num [bStar]
  have hAb : A ≤ bStar := hAr.trans (hr.2.trans hrootb)
  have hflag : aPoint x ≤ bStar := by rw [hax]; exact hap.trans (hpA.trans hAb)
  have hflagA : capPoint x ≤ bStar := by simpa only [hAx] using hAb
  have hb := hbound x hx
  have hv : x 0*eval e418 x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpx.1.le hb
  rw [actual_identity hs x hpx hflag hflagA hLx hTx] at hv
  simp only [one_mul] at hv
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
.const (4818/3733 : ℚ),
.mul 9 9,
.mul 16 16,
.mul 17 17,
.mul 18 18,
.mul 19 19,
.mul 13 13,
.mul 13 21,
.mul 21 21,
.mul 23 23,
.mul 24 24,
.const (4/1 : ℚ),
.add 9 12,
.neg 3,
.add 0 28,
.mul 11 29,
.const (1085/3733 : ℚ),
.const (627/3733 : ℚ),
.mul 32 9,
.const (385/3733 : ℚ),
.mul 34 16,
.add 33 35,
.const (73/3733 : ℚ),
.mul 37 20,
.add 36 38,
.neg 39,
.add 31 40,
.const (145513/25000 : ℚ),
.mul 42 41,
.neg 43,
.add 0 44,
.const (19/73 : ℚ),
.mul 46 8,
.mul 8 8,
.const (35/146 : ℚ),
.mul 49 48,
.add 47 50,
.mul 48 48,
.mul 52 52,
.mul 53 53,
.mul 54 54,
.const (1/2 : ℚ),
.mul 56 55,
.add 51 57,
.neg 58,
.add 14 59,
.mul 15 60,
.mul 42 61,
.add 45 62,
.mul 2 63,
.neg 2,
.add 0 65,
.const (1254/3733 : ℚ),
.mul 67 30,
.add 8 13,
.mul 30 69,
.const (1155/3733 : ℚ),
.mul 71 70,
.add 68 72,
.mul 8 48,
.mul 74 74,
.mul 8 75,
.mul 76 76,
.mul 8 77,
.mul 78 78,
.mul 8 79,
.mul 79 13,
.add 80 81,
.mul 77 77,
.mul 8 83,
.mul 84 21,
.add 82 85,
.mul 83 22,
.add 86 87,
.mul 75 75,
.mul 8 89,
.mul 90 90,
.mul 8 91,
.mul 92 23,
.add 88 93,
.mul 13 23,
.mul 91 95,
.add 94 96,
.mul 89 89,
.mul 8 98,
.mul 22 22,
.mul 99 100,
.add 97 101,
.mul 13 100,
.mul 98 103,
.add 102 104,
.mul 8 52,
.mul 106 106,
.mul 8 107,
.mul 108 108,
.mul 8 109,
.mul 110 24,
.add 105 111,
.mul 13 24,
.mul 109 113,
.add 112 114,
.mul 107 107,
.mul 8 116,
.mul 95 95,
.mul 117 118,
.add 115 119,
.mul 13 118,
.mul 116 121,
.add 120 122,
.mul 8 53,
.mul 124 124,
.mul 8 125,
.mul 100 100,
.mul 126 127,
.add 123 128,
.mul 13 127,
.mul 125 130,
.add 129 131,
.mul 8 54,
.mul 103 103,
.mul 133 134,
.add 132 135,
.mul 13 134,
.mul 54 137,
.add 136 138,
.mul 78 25,
.add 139 140,
.mul 13 25,
.mul 77 142,
.add 141 143,
.mul 113 113,
.mul 90 145,
.add 144 146,
.mul 13 145,
.mul 89 148,
.add 147 149,
.mul 118 118,
.mul 108 151,
.add 150 152,
.mul 13 151,
.mul 107 154,
.add 153 155,
.mul 121 121,
.mul 124 157,
.add 156 158,
.mul 13 157,
.mul 53 160,
.add 159 161,
.mul 127 127,
.mul 76 163,
.add 162 164,
.mul 13 163,
.mul 75 166,
.add 165 167,
.mul 130 130,
.mul 106 169,
.add 168 170,
.mul 13 169,
.mul 52 172,
.add 171 173,
.mul 134 134,
.mul 74 175,
.add 174 176,
.mul 13 175,
.mul 48 178,
.add 177 179,
.mul 137 137,
.mul 8 181,
.add 180 182,
.mul 13 181,
.add 183 184,
.mul 30 185,
.const (2409/3733 : ℚ),
.mul 187 186,
.add 73 188,
.neg 189,
.mul 66 190,
.mul 42 191,
.add 64 192,
.mul 66 66,
.const (2/1 : ℚ),
.mul 195 13,
.add 196 27,
.mul 34 197,
.add 32 198,
.const (32/1 : ℚ),
.mul 200 184,
.mul 181 27,
.const (31/1 : ℚ),
.mul 203 202,
.add 201 204,
.mul 27 27,
.mul 178 206,
.const (30/1 : ℚ),
.mul 208 207,
.add 205 209,
.mul 27 206,
.mul 175 211,
.const (29/1 : ℚ),
.mul 213 212,
.add 210 214,
.mul 206 206,
.mul 172 216,
.const (28/1 : ℚ),
.mul 218 217,
.add 215 219,
.mul 27 216,
.mul 169 221,
.const (27/1 : ℚ),
.mul 223 222,
.add 220 224,
.mul 211 211,
.mul 166 226,
.const (26/1 : ℚ),
.mul 228 227,
.add 225 229,
.mul 27 226,
.mul 163 231,
.const (25/1 : ℚ),
.mul 233 232,
.add 230 234,
.mul 216 216,
.mul 160 236,
.const (24/1 : ℚ),
.mul 238 237,
.add 235 239,
.mul 27 236,
.mul 157 241,
.const (23/1 : ℚ),
.mul 243 242,
.add 240 244,
.mul 221 221,
.mul 154 246,
.const (22/1 : ℚ),
.mul 248 247,
.add 245 249,
.mul 27 246,
.mul 151 251,
.const (21/1 : ℚ),
.mul 253 252,
.add 250 254,
.mul 226 226,
.mul 148 256,
.const (20/1 : ℚ),
.mul 258 257,
.add 255 259,
.mul 27 256,
.mul 145 261,
.const (19/1 : ℚ),
.mul 263 262,
.add 260 264,
.mul 231 231,
.mul 142 266,
.const (18/1 : ℚ),
.mul 268 267,
.add 265 269,
.mul 27 266,
.mul 25 271,
.const (17/1 : ℚ),
.mul 273 272,
.add 270 274,
.mul 236 236,
.mul 137 276,
.const (16/1 : ℚ),
.mul 278 277,
.add 275 279,
.mul 27 276,
.mul 134 281,
.const (15/1 : ℚ),
.mul 283 282,
.add 280 284,
.mul 241 241,
.mul 130 286,
.const (14/1 : ℚ),
.mul 288 287,
.add 285 289,
.mul 27 286,
.mul 127 291,
.const (13/1 : ℚ),
.mul 293 292,
.add 290 294,
.mul 246 246,
.mul 121 296,
.const (12/1 : ℚ),
.mul 298 297,
.add 295 299,
.mul 27 296,
.mul 118 301,
.const (11/1 : ℚ),
.mul 303 302,
.add 300 304,
.mul 251 251,
.mul 113 306,
.const (10/1 : ℚ),
.mul 308 307,
.add 305 309,
.mul 27 306,
.mul 24 311,
.const (9/1 : ℚ),
.mul 313 312,
.add 310 314,
.mul 256 256,
.mul 103 316,
.const (8/1 : ℚ),
.mul 318 317,
.add 315 319,
.mul 27 316,
.mul 100 321,
.const (7/1 : ℚ),
.mul 323 322,
.add 320 324,
.mul 261 261,
.mul 95 326,
.const (6/1 : ℚ),
.mul 328 327,
.add 325 329,
.mul 27 326,
.mul 23 331,
.const (5/1 : ℚ),
.mul 333 332,
.add 330 334,
.mul 266 266,
.mul 22 336,
.mul 26 337,
.add 335 338,
.mul 27 336,
.mul 21 340,
.const (3/1 : ℚ),
.mul 342 341,
.add 339 343,
.mul 271 271,
.mul 13 345,
.mul 195 346,
.add 344 347,
.mul 27 345,
.add 348 349,
.mul 37 350,
.add 199 351,
.mul 194 352,
.mul 1 353,
.mul 42 354,
.neg 355,
.add 193 356]
private noncomputable def ssaQVals : Fin 47 → ℚ := ![(1/1 : ℚ),(49/100 : ℚ),(390189/5000000 : ℚ),(1085/4818 : ℚ),(4818/3733 : ℚ),(4/1 : ℚ),(1085/3733 : ℚ),(627/3733 : ℚ),(385/3733 : ℚ),(73/3733 : ℚ),(145513/25000 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ),(1254/3733 : ℚ),(1155/3733 : ℚ),(2409/3733 : ℚ),(2/1 : ℚ),(32/1 : ℚ),(31/1 : ℚ),(30/1 : ℚ),(29/1 : ℚ),(28/1 : ℚ),(27/1 : ℚ),(26/1 : ℚ),(25/1 : ℚ),(24/1 : ℚ),(23/1 : ℚ),(22/1 : ℚ),(21/1 : ℚ),(20/1 : ℚ),(19/1 : ℚ),(18/1 : ℚ),(17/1 : ℚ),(16/1 : ℚ),(15/1 : ℚ),(14/1 : ℚ),(13/1 : ℚ),(12/1 : ℚ),(11/1 : ℚ),(10/1 : ℚ),(9/1 : ℚ),(8/1 : ℚ),(7/1 : ℚ),(6/1 : ℚ),(5/1 : ℚ),(3/1 : ℚ)]
private theorem ssa_tape : MetricDistortion.OptimizedSSAFinite0.S_d630d3bde3df9d51.p358 ssaQVals = tape := by rfl
private noncomputable def computed (D : Int) (B : Fin 4 → FixedTape.I) : FixedTape.Row :=
  MetricDistortion.OptimizedSSAFinite0.S_d630d3bde3df9d51.computed ssaQVals D B
private theorem ssa_matches (D : Int) (B : Fin 4 → FixedTape.I) :
    (FixedTape.rowsAux D B [] tape).getD 357 FixedTape.zeroRow = computed D B := by
  rw [←ssa_tape]
  exact MetricDistortion.OptimizedSSAFinite0.S_d630d3bde3df9d51.ssa_matches ssaQVals D B

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
private noncomputable def denominator : Int := 29183294757838388933353851123700932280320000000
private theorem denominator_positive : 0 < denominator := by decide +kernel
private noncomputable def candidateRows (B : Fin 4 → FixedTape.I) : List TapeBounds :=
  (FixedTape.rowsAux denominator B [] tape).map (FixedTape.decodeRow denominator)
private theorem root_in_range : 357 < tape.length := by decide +kernel
private theorem references_valid : tapeRefsValidAux 0 tape = true := by decide +kernel
private theorem candidate_valid (h : Needs) (B : Fin 4 → FixedTape.I) :
    tapeCheck (FixedTape.decodeBox denominator B) tape (candidateRows B) = true :=
  h.child_10.1 denominator denominator_positive B tape references_valid
private theorem candidate_root (B : Fin 4 → FixedTape.I) :
    (candidateRows B).getD 357 zeroTapeBounds = FixedTape.decodeRow denominator (computed denominator B) := by
  unfold candidateRows
  rw [←decode_zeroRow denominator,List.getD_map,ssa_matches]
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨0,7124827821737887923182092559497297920000000⟩,⟨0,29183294757838388933353851123700932280320000000⟩,⟨0,29183294757838388933353851123700932280320000000⟩,⟨0,29183294757838388933353851123700932280320000000⟩]
private noncomputable def tree0 : TapeTree := .direct (candidateRows ibox0)
attribute [irreducible] tree0
private theorem sign_0 : (computed denominator ibox0).value.hi ≤ 0 := by decide +kernel
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 357 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  refine ⟨root_in_range,candidate_valid h ibox0,?_⟩
  rw [candidate_root]
  simpa [FixedTape.decodeRow,FixedTape.decode] using (h.child_10.2.2.2.1 denominator (computed denominator ibox0).value.hi denominator_positive).1 sign_0
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (0/1 : ℚ) (1/4096 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 357 = e418 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (0/1 : ℚ) (1/4096 : ℚ)) x → eval e418 x ≤ 0 := by
  have hb := h.child_4 tape 357 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell0_low_internal

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell0_low_internal
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((0/1 : ℚ) : ℝ) < p ∧ p ≤ ((1/4096 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 0 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 0 p)
    (hk0 : ((1/4096 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((0/1 : ℚ) : ℝ))
    (hk1 : ((1/4096 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((0/1 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r), internalResidual (0 : Fin 9) a p A r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell0_low_internal.cell_bound h.child_8 h.child_9 (Cell0_low_internal.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell0_low_internal
