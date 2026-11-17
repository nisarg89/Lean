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
namespace Cell0_high_internal_bottom
private noncomputable def qValues : Fin 1 → ℚ := ![(0/1 : ℚ)]
private noncomputable abbrev e2 : PolyExpr := SharedFiniteSemantics3.e2 qValues
private noncomputable abbrev e6 : PolyExpr := SharedFiniteSemantics3.e6 qValues
private noncomputable abbrev e11 : PolyExpr := SharedFiniteSemantics3.e11 qValues
private noncomputable abbrev e15 : PolyExpr := SharedFiniteSemantics3.e15 qValues
private noncomputable abbrev e17 : PolyExpr := SharedFiniteSemantics3.e17 qValues
private noncomputable abbrev e87 : PolyExpr := SharedFiniteSemantics3.e87 qValues
private noncomputable abbrev e91 : PolyExpr := SharedFiniteSemantics3.e91 qValues
private noncomputable abbrev e418 : PolyExpr := SharedFiniteSemantics3.e418 qValues
private noncomputable abbrev node_1 := SharedFiniteSemantics3.node_1 qValues
private noncomputable abbrev node_2 := SharedFiniteSemantics3.node_2 qValues
private noncomputable abbrev node_3 := SharedFiniteSemantics3.node_3 qValues
private noncomputable abbrev node_4 := SharedFiniteSemantics3.node_4 qValues
private noncomputable abbrev node_5 := SharedFiniteSemantics3.node_5 qValues
private noncomputable abbrev node_6 := SharedFiniteSemantics3.node_6 qValues
private noncomputable abbrev node_7 := SharedFiniteSemantics3.node_7 qValues
private noncomputable abbrev node_8 := SharedFiniteSemantics3.node_8 qValues
private noncomputable abbrev node_9 := SharedFiniteSemantics3.node_9 qValues
private noncomputable abbrev node_10 := SharedFiniteSemantics3.node_10 qValues
private noncomputable abbrev node_11 := SharedFiniteSemantics3.node_11 qValues
private noncomputable abbrev node_13 := SharedFiniteSemantics3.node_13 qValues
private noncomputable abbrev node_14 := SharedFiniteSemantics3.node_14 qValues
private noncomputable abbrev node_15 := SharedFiniteSemantics3.node_15 qValues
private noncomputable abbrev node_16 := SharedFiniteSemantics3.node_16 qValues
private noncomputable abbrev node_17 := SharedFiniteSemantics3.node_17 qValues
private noncomputable abbrev node_87 := SharedFiniteSemantics3.node_87 qValues
private noncomputable abbrev node_88 := SharedFiniteSemantics3.node_88 qValues
private noncomputable abbrev node_89 := SharedFiniteSemantics3.node_89 qValues
private noncomputable abbrev node_90 := SharedFiniteSemantics3.node_90 qValues
private noncomputable abbrev node_91 := SharedFiniteSemantics3.node_91 qValues
private noncomputable abbrev node_103 := SharedFiniteSemantics3.node_103 qValues
private noncomputable abbrev node_104 := SharedFiniteSemantics3.node_104 qValues
private noncomputable abbrev node_105 := SharedFiniteSemantics3.node_105 qValues
private noncomputable abbrev node_106 := SharedFiniteSemantics3.node_106 qValues
private noncomputable abbrev node_123 := SharedFiniteSemantics3.node_123 qValues
private noncomputable abbrev node_124 := SharedFiniteSemantics3.node_124 qValues
private noncomputable abbrev node_125 := SharedFiniteSemantics3.node_125 qValues
private noncomputable abbrev node_126 := SharedFiniteSemantics3.node_126 qValues
private noncomputable abbrev node_127 := SharedFiniteSemantics3.node_127 qValues
private noncomputable abbrev node_252 := SharedFiniteSemantics3.node_252 qValues
private noncomputable abbrev node_253 := SharedFiniteSemantics3.node_253 qValues
private noncomputable abbrev node_254 := SharedFiniteSemantics3.node_254 qValues
private noncomputable abbrev node_255 := SharedFiniteSemantics3.node_255 qValues
private noncomputable abbrev node_414 := SharedFiniteSemantics3.node_414 qValues
private noncomputable abbrev node_415 := SharedFiniteSemantics3.node_415 qValues
private noncomputable abbrev node_416 := SharedFiniteSemantics3.node_416 qValues
private noncomputable abbrev node_417 := SharedFiniteSemantics3.node_417 qValues
private noncomputable abbrev node_418 := SharedFiniteSemantics3.node_418 qValues
private noncomputable abbrev semantic_H_38 := SharedFiniteSemantics3.semantic_H_38 qValues
private noncomputable abbrev semantic_H_54 := SharedFiniteSemantics3.semantic_H_54 qValues
private noncomputable abbrev semantic_H_72 := SharedFiniteSemantics3.semantic_H_72 qValues
private noncomputable abbrev semantic_psi_122 := SharedFiniteSemantics3.semantic_psi_122 qValues
private noncomputable abbrev semantic_F0_102 := SharedFiniteSemantics3.semantic_F0_102 qValues
private noncomputable abbrev semantic_pdiff_251 := SharedFiniteSemantics3.semantic_pdiff_251 qValues
private noncomputable abbrev semantic_J_413 := SharedFiniteSemantics3.semantic_J_413 qValues
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
private theorem point_17 (x : Fin 4 → ℝ) : eval e17 x = yPoint x := by
  simp only [node_2,node_3,node_4,node_6,node_7,node_8,node_9,node_10,node_11,node_16,node_17] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_91 (x : Fin 4 → ℝ) : eval e91 x = rPoint x-capPoint x := by
  simp only [node_1,node_2,node_4,node_5,node_7,node_8,node_9,node_13,node_14,node_88,node_89,node_90,node_91] <;>
    norm_num [qValues,aPoint,rPoint,capPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_87 (x : Fin 4 → ℝ) : eval e87 x = yPoint x := by
  simp only [node_2,node_3,node_4,node_6,node_7,node_8,node_9,node_10,node_87] <;>
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
  simp only [node_1,node_3,node_103,node_104,node_105,node_106,node_123,node_124,node_125,node_126,node_127,node_252,node_253,node_254,node_255,node_414,node_415,node_416,node_417,node_418,semantic_H_38,semantic_H_54,semantic_H_72,semantic_psi_122,semantic_F0_102,semantic_pdiff_251,semantic_J_413,point_6,point_15,point_2,point_11,point_17,point_91,point_87]
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
    (hkb : ((1/4096 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((0/1 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r)
    (hcase : A ≤ bStar) :
    internalResidual (0 : Fin 9) a p A r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxA,hxr⟩ := h6 (0/1 : ℚ) (1/4096 : ℚ) bStar p a A r hpcell hkb hr ha hap hpA hcase
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,capPoint] using hxa
  have hAx : capPoint x = A := by simpa only [aPoint,rPoint,capPoint] using hxA
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,capPoint] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 0 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 0 (x 0) := by simpa only [hxp] using hT
  have hAb : A ≤ bStar := hcase
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
.const (4818/3733 : ℚ),
.mul 5 5,
.mul 16 16,
.mul 17 17,
.mul 18 18,
.mul 19 19,
.mul 10 10,
.mul 10 21,
.mul 21 21,
.mul 23 23,
.mul 24 24,
.const (4/1 : ℚ),
.add 5 9,
.neg 3,
.add 0 28,
.mul 8 29,
.add 30 12,
.const (1085/3733 : ℚ),
.const (627/3733 : ℚ),
.mul 33 5,
.const (385/3733 : ℚ),
.mul 35 16,
.add 34 36,
.const (73/3733 : ℚ),
.mul 38 20,
.add 37 39,
.neg 40,
.add 32 41,
.const (145513/25000 : ℚ),
.mul 43 42,
.neg 44,
.add 0 45,
.const (19/73 : ℚ),
.mul 47 13,
.mul 13 13,
.const (35/146 : ℚ),
.mul 50 49,
.add 48 51,
.mul 49 49,
.mul 53 53,
.mul 54 54,
.mul 55 55,
.const (1/2 : ℚ),
.mul 57 56,
.add 52 58,
.neg 59,
.add 14 60,
.mul 15 61,
.mul 43 62,
.add 46 63,
.mul 2 64,
.neg 2,
.add 0 66,
.const (1254/3733 : ℚ),
.mul 68 31,
.add 13 10,
.mul 31 70,
.const (1155/3733 : ℚ),
.mul 72 71,
.add 69 73,
.mul 13 49,
.mul 75 75,
.mul 13 76,
.mul 77 77,
.mul 13 78,
.mul 79 79,
.mul 13 80,
.mul 80 10,
.add 81 82,
.mul 78 78,
.mul 13 84,
.mul 85 21,
.add 83 86,
.mul 84 22,
.add 87 88,
.mul 76 76,
.mul 13 90,
.mul 91 91,
.mul 13 92,
.mul 93 23,
.add 89 94,
.mul 10 23,
.mul 92 96,
.add 95 97,
.mul 90 90,
.mul 13 99,
.mul 22 22,
.mul 100 101,
.add 98 102,
.mul 10 101,
.mul 99 104,
.add 103 105,
.mul 13 53,
.mul 107 107,
.mul 13 108,
.mul 109 109,
.mul 13 110,
.mul 111 24,
.add 106 112,
.mul 10 24,
.mul 110 114,
.add 113 115,
.mul 108 108,
.mul 13 117,
.mul 96 96,
.mul 118 119,
.add 116 120,
.mul 10 119,
.mul 117 122,
.add 121 123,
.mul 13 54,
.mul 125 125,
.mul 13 126,
.mul 101 101,
.mul 127 128,
.add 124 129,
.mul 10 128,
.mul 126 131,
.add 130 132,
.mul 13 55,
.mul 104 104,
.mul 134 135,
.add 133 136,
.mul 10 135,
.mul 55 138,
.add 137 139,
.mul 79 25,
.add 140 141,
.mul 10 25,
.mul 78 143,
.add 142 144,
.mul 114 114,
.mul 91 146,
.add 145 147,
.mul 10 146,
.mul 90 149,
.add 148 150,
.mul 119 119,
.mul 109 152,
.add 151 153,
.mul 10 152,
.mul 108 155,
.add 154 156,
.mul 122 122,
.mul 125 158,
.add 157 159,
.mul 10 158,
.mul 54 161,
.add 160 162,
.mul 128 128,
.mul 77 164,
.add 163 165,
.mul 10 164,
.mul 76 167,
.add 166 168,
.mul 131 131,
.mul 107 170,
.add 169 171,
.mul 10 170,
.mul 53 173,
.add 172 174,
.mul 135 135,
.mul 75 176,
.add 175 177,
.mul 10 176,
.mul 49 179,
.add 178 180,
.mul 138 138,
.mul 13 182,
.add 181 183,
.mul 10 182,
.add 184 185,
.mul 31 186,
.const (2409/3733 : ℚ),
.mul 188 187,
.add 74 189,
.neg 190,
.mul 67 191,
.mul 43 192,
.add 65 193,
.mul 67 67,
.const (2/1 : ℚ),
.mul 196 10,
.add 197 27,
.mul 35 198,
.add 33 199,
.const (32/1 : ℚ),
.mul 201 185,
.mul 182 27,
.const (31/1 : ℚ),
.mul 204 203,
.add 202 205,
.mul 27 27,
.mul 179 207,
.const (30/1 : ℚ),
.mul 209 208,
.add 206 210,
.mul 27 207,
.mul 176 212,
.const (29/1 : ℚ),
.mul 214 213,
.add 211 215,
.mul 207 207,
.mul 173 217,
.const (28/1 : ℚ),
.mul 219 218,
.add 216 220,
.mul 27 217,
.mul 170 222,
.const (27/1 : ℚ),
.mul 224 223,
.add 221 225,
.mul 212 212,
.mul 167 227,
.const (26/1 : ℚ),
.mul 229 228,
.add 226 230,
.mul 27 227,
.mul 164 232,
.const (25/1 : ℚ),
.mul 234 233,
.add 231 235,
.mul 217 217,
.mul 161 237,
.const (24/1 : ℚ),
.mul 239 238,
.add 236 240,
.mul 27 237,
.mul 158 242,
.const (23/1 : ℚ),
.mul 244 243,
.add 241 245,
.mul 222 222,
.mul 155 247,
.const (22/1 : ℚ),
.mul 249 248,
.add 246 250,
.mul 27 247,
.mul 152 252,
.const (21/1 : ℚ),
.mul 254 253,
.add 251 255,
.mul 227 227,
.mul 149 257,
.const (20/1 : ℚ),
.mul 259 258,
.add 256 260,
.mul 27 257,
.mul 146 262,
.const (19/1 : ℚ),
.mul 264 263,
.add 261 265,
.mul 232 232,
.mul 143 267,
.const (18/1 : ℚ),
.mul 269 268,
.add 266 270,
.mul 27 267,
.mul 25 272,
.const (17/1 : ℚ),
.mul 274 273,
.add 271 275,
.mul 237 237,
.mul 138 277,
.const (16/1 : ℚ),
.mul 279 278,
.add 276 280,
.mul 27 277,
.mul 135 282,
.const (15/1 : ℚ),
.mul 284 283,
.add 281 285,
.mul 242 242,
.mul 131 287,
.const (14/1 : ℚ),
.mul 289 288,
.add 286 290,
.mul 27 287,
.mul 128 292,
.const (13/1 : ℚ),
.mul 294 293,
.add 291 295,
.mul 247 247,
.mul 122 297,
.const (12/1 : ℚ),
.mul 299 298,
.add 296 300,
.mul 27 297,
.mul 119 302,
.const (11/1 : ℚ),
.mul 304 303,
.add 301 305,
.mul 252 252,
.mul 114 307,
.const (10/1 : ℚ),
.mul 309 308,
.add 306 310,
.mul 27 307,
.mul 24 312,
.const (9/1 : ℚ),
.mul 314 313,
.add 311 315,
.mul 257 257,
.mul 104 317,
.const (8/1 : ℚ),
.mul 319 318,
.add 316 320,
.mul 27 317,
.mul 101 322,
.const (7/1 : ℚ),
.mul 324 323,
.add 321 325,
.mul 262 262,
.mul 96 327,
.const (6/1 : ℚ),
.mul 329 328,
.add 326 330,
.mul 27 327,
.mul 23 332,
.const (5/1 : ℚ),
.mul 334 333,
.add 331 335,
.mul 267 267,
.mul 22 337,
.mul 26 338,
.add 336 339,
.mul 27 337,
.mul 21 341,
.const (3/1 : ℚ),
.mul 343 342,
.add 340 344,
.mul 272 272,
.mul 10 346,
.mul 196 347,
.add 345 348,
.mul 27 346,
.add 349 350,
.mul 38 351,
.add 200 352,
.mul 195 353,
.mul 1 354,
.mul 43 355,
.neg 356,
.add 194 357]
private noncomputable def ssaQVals : Fin 47 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(2159811/5000000 : ℚ),(1085/4818 : ℚ),(4818/3733 : ℚ),(4/1 : ℚ),(1085/3733 : ℚ),(627/3733 : ℚ),(385/3733 : ℚ),(73/3733 : ℚ),(145513/25000 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ),(1254/3733 : ℚ),(1155/3733 : ℚ),(2409/3733 : ℚ),(2/1 : ℚ),(32/1 : ℚ),(31/1 : ℚ),(30/1 : ℚ),(29/1 : ℚ),(28/1 : ℚ),(27/1 : ℚ),(26/1 : ℚ),(25/1 : ℚ),(24/1 : ℚ),(23/1 : ℚ),(22/1 : ℚ),(21/1 : ℚ),(20/1 : ℚ),(19/1 : ℚ),(18/1 : ℚ),(17/1 : ℚ),(16/1 : ℚ),(15/1 : ℚ),(14/1 : ℚ),(13/1 : ℚ),(12/1 : ℚ),(11/1 : ℚ),(10/1 : ℚ),(9/1 : ℚ),(8/1 : ℚ),(7/1 : ℚ),(6/1 : ℚ),(5/1 : ℚ),(3/1 : ℚ)]
private theorem ssa_tape : MetricDistortion.OptimizedSSAFinite0.S_fbeab04c614a7161.p359 ssaQVals = tape := by rfl
private noncomputable def computed (D : Int) (B : Fin 4 → FixedTape.I) : FixedTape.Row :=
  MetricDistortion.OptimizedSSAFinite0.S_fbeab04c614a7161.computed ssaQVals D B
private theorem ssa_matches (D : Int) (B : Fin 4 → FixedTape.I) :
    (FixedTape.rowsAux D B [] tape).getD 358 FixedTape.zeroRow = computed D B := by
  rw [←ssa_tape]
  exact MetricDistortion.OptimizedSSAFinite0.S_fbeab04c614a7161.ssa_matches ssaQVals D B

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
private theorem root_in_range : 358 < tape.length := by decide +kernel
private theorem references_valid : tapeRefsValidAux 0 tape = true := by decide +kernel
private theorem candidate_valid (h : Needs) (B : Fin 4 → FixedTape.I) :
    tapeCheck (FixedTape.decodeBox denominator B) tape (candidateRows B) = true :=
  h.child_10.1 denominator denominator_positive B tape references_valid
private theorem candidate_root (B : Fin 4 → FixedTape.I) :
    (candidateRows B).getD 358 zeroTapeBounds = FixedTape.decodeRow denominator (computed denominator B) := by
  unfold candidateRows
  rw [←decode_zeroRow denominator,List.getD_map,ssa_matches]
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨0,7124827821737887923182092559497297920000000⟩,⟨0,29183294757838388933353851123700932280320000000⟩,⟨0,29183294757838388933353851123700932280320000000⟩,⟨0,29183294757838388933353851123700932280320000000⟩]
private noncomputable def tree0 : TapeTree := .direct (candidateRows ibox0)
attribute [irreducible] tree0
private theorem sign_0 : (computed denominator ibox0).value.hi ≤ 0 := by decide +kernel
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 358 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  refine ⟨root_in_range,candidate_valid h ibox0,?_⟩
  rw [candidate_root]
  simpa [FixedTape.decodeRow,FixedTape.decode] using (h.child_10.2.2.2.1 denominator (computed denominator ibox0).value.hi denominator_positive).1 sign_0
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (0/1 : ℚ) (1/4096 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 358 = e418 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (0/1 : ℚ) (1/4096 : ℚ)) x → eval e418 x ≤ 0 := by
  have hb := h.child_4 tape 358 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell0_high_internal_bottom

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell0_high_internal_bottom
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((0/1 : ℚ) : ℝ) < p ∧ p ≤ ((1/4096 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 0 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 0 p)
    (hkb : ((1/4096 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((0/1 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r)
    (hcase : A ≤ bStar), internalResidual (0 : Fin 9) a p A r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell0_high_internal_bottom.cell_bound h.child_8 h.child_9 (Cell0_high_internal_bottom.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell0_high_internal_bottom
