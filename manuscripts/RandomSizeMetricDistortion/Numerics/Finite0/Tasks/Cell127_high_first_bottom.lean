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
namespace Cell127_high_first_bottom
private noncomputable def qValues : Fin 1 → ℚ := ![(0/1 : ℚ)]
private noncomputable abbrev e2 : PolyExpr := SharedFiniteSemantics35.e2 qValues
private noncomputable abbrev e7 : PolyExpr := SharedFiniteSemantics35.e7 qValues
private noncomputable abbrev e11 : PolyExpr := SharedFiniteSemantics35.e11 qValues
private noncomputable abbrev e14 : PolyExpr := SharedFiniteSemantics35.e14 qValues
private noncomputable abbrev e230 : PolyExpr := SharedFiniteSemantics35.e230 qValues
private noncomputable abbrev node_1 := SharedFiniteSemantics35.node_1 qValues
private noncomputable abbrev node_2 := SharedFiniteSemantics35.node_2 qValues
private noncomputable abbrev node_3 := SharedFiniteSemantics35.node_3 qValues
private noncomputable abbrev node_4 := SharedFiniteSemantics35.node_4 qValues
private noncomputable abbrev node_6 := SharedFiniteSemantics35.node_6 qValues
private noncomputable abbrev node_7 := SharedFiniteSemantics35.node_7 qValues
private noncomputable abbrev node_9 := SharedFiniteSemantics35.node_9 qValues
private noncomputable abbrev node_10 := SharedFiniteSemantics35.node_10 qValues
private noncomputable abbrev node_11 := SharedFiniteSemantics35.node_11 qValues
private noncomputable abbrev node_13 := SharedFiniteSemantics35.node_13 qValues
private noncomputable abbrev node_14 := SharedFiniteSemantics35.node_14 qValues
private noncomputable abbrev node_213 := SharedFiniteSemantics35.node_213 qValues
private noncomputable abbrev node_214 := SharedFiniteSemantics35.node_214 qValues
private noncomputable abbrev node_215 := SharedFiniteSemantics35.node_215 qValues
private noncomputable abbrev node_229 := SharedFiniteSemantics35.node_229 qValues
private noncomputable abbrev node_230 := SharedFiniteSemantics35.node_230 qValues
private noncomputable abbrev semantic_psi_32 := SharedFiniteSemantics35.semantic_psi_32 qValues
private noncomputable abbrev semantic_psi_228 := SharedFiniteSemantics35.semantic_psi_228 qValues
private noncomputable abbrev semantic_increment_211 := SharedFiniteSemantics35.semantic_increment_211 qValues
private noncomputable abbrev semantic_dH_212 := SharedFiniteSemantics35.semantic_dH_212 qValues
private noncomputable def aPoint (x : Fin 4 → ℝ) : ℝ := bStar*x 1
private noncomputable def rPoint (x : Fin 4 → ℝ) : ℝ := bStar+(1-bStar)*x 2
private noncomputable def yPoint (x : Fin 4 → ℝ) : ℝ := aPoint x+1-x 0
private theorem point_7 (x : Fin 4 → ℝ) : eval e7 x = aPoint x := by
  simp only [node_3,node_6,node_7] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_11 (x : Fin 4 → ℝ) : eval e11 x = rPoint x := by
  simp only [node_4,node_6,node_9,node_10,node_11] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_2 (x : Fin 4 → ℝ) : eval e2 x = x 0 := by
  simp only [node_2] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_14 (x : Fin 4 → ℝ) : eval e14 x = 1-x 0 := by
  simp only [node_1,node_2,node_13,node_14] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem price_lambda_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceLambda 127 p = (145513/100000 : ℝ)/(sourceDenom*(1-p)) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell127,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 127 p = (145513/100000 : ℝ)*((1/1 : ℝ)-1)/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell127,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e230 x = (1)*(aPoint x+priceLambda 127 (x 0)*(HStar (yPoint x)-HStar (aPoint x))+priceTau 127 (x 0)*psiStar (rPoint x)+(0)-(cStar)) := by
  have hp0 : x 0 ≠ 0 := ne_of_gt hp.1
  have hp1 : x 0 ≠ 1 := ne_of_lt hp.2
  have heps : 1-x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  rw [price_lambda_normal _ hp,price_tau_normal _ hp]
  simp only [node_213,node_214,node_215,node_229,node_230,semantic_psi_32,semantic_psi_228,semantic_increment_211,semantic_dH_212,point_7,point_11,point_2,point_14]
  have hlarge := large_first_bottom hs (aPoint x) (x 0) hp1
  have hy : aPoint x+1-x 0 = yPoint x := by rfl
  rw [hy] at hlarge
  norm_num [qValues,eta,etas,Fin.val_zero,sourceDenom,muStar,cStar] at *
  generalize HStar (yPoint x) = z0 at *
  generalize HStar (aPoint x) = z1 at *
  generalize psiStar (aPoint x) = z2 at *
  generalize psiStar (rPoint x) = z3 at *
  generalize sourceF0 (aPoint x) = z4 at *
  generalize sourceInc (aPoint x) (1-x 0) = z5 at *
  generalize sourceInc (aPoint x) ((1-x 0)*x 2) = z6 at *
  generalize sourcePD (aPoint x) (rPoint x) (rPoint x-aPoint x) = z7 at *
  field_simp [hp0,heps] at hlarge ⊢
  nlinarith [hlarge]
theorem actual_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) (ha : aPoint x ≤ bStar)
    (hL : lambdaStar (x 0) = priceLambda 127 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 127 (x 0)) :
    (1)*eval e230 x = (1)*(firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (99/100 : ℚ) (1/1 : ℚ)) x → eval e230 x ≤ 0)
    (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((99/100 : ℚ) : ℝ) < p ∧ p ≤ ((1/1 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 127 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 127 p)
    (hkb : ((1/1 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((99/100 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : a ≤ bStar) :
    firstResidual (0 : Fin 9) a p r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨x,hx,hxp,hxa,hxr⟩ := h4 (99/100 : ℚ) (1/1 : ℚ) bStar p a r hpcell hkb hr ha hap hcase
  have hcut : ¬(((1/1 : ℚ) : ℝ) ≤ bStar) := by norm_num [bStar]
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,if_neg hcut] using hxa
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,if_neg hcut] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 127 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 127 (x 0) := by simpa only [hxp] using hT
  have hflag : aPoint x ≤ bStar := by simpa only [hax] using hcase
  have hb := hbound x hx
  have hv : (1 : ℝ)*eval e230 x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 1) hb
  rw [actual_identity hs x hpx hflag hLx hTx] at hv
  simp only [one_mul] at hv
  simpa only [hxp,hax,hrx] using hv
private noncomputable def tape : List TapeOp := [
.const (1/1 : ℚ),
.var 0,
.var 1,
.const (2840189/5000000 : ℚ),
.mul 3 2,
.neg 1,
.add 0 5,
.const (1085/4818 : ℚ),
.const (19/73 : ℚ),
.mul 8 4,
.mul 4 4,
.const (35/146 : ℚ),
.mul 11 10,
.add 9 12,
.mul 10 10,
.mul 14 14,
.mul 15 15,
.mul 16 16,
.const (1/2 : ℚ),
.mul 18 17,
.add 13 19,
.neg 20,
.add 7 21,
.const (4818/3733 : ℚ),
.mul 23 22,
.const (627/3733 : ℚ),
.mul 25 6,
.mul 4 6,
.const (1155/3733 : ℚ),
.mul 28 27,
.add 26 29,
.mul 6 6,
.const (385/3733 : ℚ),
.mul 32 31,
.add 30 33,
.mul 4 10,
.mul 35 35,
.mul 4 36,
.mul 37 37,
.mul 4 38,
.mul 39 39,
.mul 4 40,
.mul 41 6,
.const (38544/3733 : ℚ),
.mul 43 42,
.add 34 44,
.mul 40 31,
.const (398288/3733 : ℚ),
.mul 47 46,
.add 45 48,
.mul 38 38,
.mul 4 50,
.mul 6 31,
.mul 51 52,
.const (2987160/3733 : ℚ),
.mul 54 53,
.add 49 55,
.mul 31 31,
.mul 50 57,
.const (17325528/3733 : ℚ),
.mul 59 58,
.add 56 60,
.mul 36 36,
.mul 4 62,
.mul 63 63,
.mul 4 64,
.mul 6 57,
.mul 65 66,
.const (80852464/3733 : ℚ),
.mul 68 67,
.add 61 69,
.mul 52 52,
.mul 64 71,
.const (311859504/3733 : ℚ),
.mul 73 72,
.add 70 74,
.mul 62 62,
.mul 4 76,
.mul 6 71,
.mul 77 78,
.const (1013543388/3733 : ℚ),
.mul 80 79,
.add 75 81,
.mul 57 57,
.mul 76 83,
.const (2815398300/3733 : ℚ),
.mul 85 84,
.add 82 86,
.mul 4 14,
.mul 88 88,
.mul 4 89,
.mul 90 90,
.mul 4 91,
.mul 6 83,
.mul 92 93,
.const (6756955920/3733 : ℚ),
.mul 95 94,
.add 87 96,
.mul 66 66,
.mul 91 98,
.const (14128180560/3733 : ℚ),
.mul 100 99,
.add 97 101,
.mul 89 89,
.mul 4 103,
.mul 6 98,
.mul 104 105,
.const (25901664360/3733 : ℚ),
.mul 107 106,
.add 102 108,
.mul 71 71,
.mul 103 110,
.const (41841150120/3733 : ℚ),
.mul 112 111,
.add 109 113,
.mul 4 15,
.mul 115 115,
.mul 4 116,
.mul 6 110,
.mul 117 118,
.const (59773071600/3733 : ℚ),
.mul 120 119,
.add 114 121,
.mul 78 78,
.mul 116 123,
.const (75712557360/3733 : ℚ),
.mul 125 124,
.add 122 126,
.mul 4 16,
.mul 6 123,
.mul 128 129,
.const (85176627030/3733 : ℚ),
.mul 131 130,
.add 127 132,
.mul 83 83,
.mul 16 134,
.mul 131 135,
.add 133 136,
.mul 6 134,
.mul 39 138,
.mul 125 139,
.add 137 140,
.mul 93 93,
.mul 38 142,
.mul 120 143,
.add 141 144,
.mul 6 142,
.mul 63 146,
.mul 112 147,
.add 145 148,
.mul 98 98,
.mul 62 150,
.mul 107 151,
.add 149 152,
.mul 6 150,
.mul 90 154,
.mul 100 155,
.add 153 156,
.mul 105 105,
.mul 89 158,
.mul 95 159,
.add 157 160,
.mul 6 158,
.mul 115 162,
.mul 85 163,
.add 161 164,
.mul 110 110,
.mul 15 166,
.mul 80 167,
.add 165 168,
.mul 6 166,
.mul 37 170,
.mul 73 171,
.add 169 172,
.mul 118 118,
.mul 36 174,
.mul 68 175,
.add 173 176,
.mul 6 174,
.mul 88 178,
.mul 59 179,
.add 177 180,
.mul 123 123,
.mul 14 182,
.mul 54 183,
.add 181 184,
.mul 6 182,
.mul 35 186,
.mul 47 187,
.add 185 188,
.mul 129 129,
.mul 10 190,
.mul 43 191,
.add 189 192,
.mul 6 190,
.mul 4 194,
.const (2409/3733 : ℚ),
.mul 196 195,
.add 193 197,
.mul 134 134,
.const (73/3733 : ℚ),
.mul 200 199,
.add 198 201,
.neg 202,
.add 24 203,
.const (145513/100000 : ℚ),
.mul 205 204,
.add 4 206,
.const (-113609/200000 : ℚ),
.add 207 208]
private noncomputable def ssaQVals : Fin 29 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(1085/4818 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ),(4818/3733 : ℚ),(627/3733 : ℚ),(1155/3733 : ℚ),(385/3733 : ℚ),(38544/3733 : ℚ),(398288/3733 : ℚ),(2987160/3733 : ℚ),(17325528/3733 : ℚ),(80852464/3733 : ℚ),(311859504/3733 : ℚ),(1013543388/3733 : ℚ),(2815398300/3733 : ℚ),(6756955920/3733 : ℚ),(14128180560/3733 : ℚ),(25901664360/3733 : ℚ),(41841150120/3733 : ℚ),(59773071600/3733 : ℚ),(75712557360/3733 : ℚ),(85176627030/3733 : ℚ),(2409/3733 : ℚ),(73/3733 : ℚ),(145513/100000 : ℚ),(-113609/200000 : ℚ)]
private theorem ssa_tape : MetricDistortion.OptimizedSSAFinite0.S_aaa4e8b09ed7acd6.p210 ssaQVals = tape := by rfl
private noncomputable def computed (D : Int) (B : Fin 4 → FixedTape.I) : FixedTape.Row :=
  MetricDistortion.OptimizedSSAFinite0.S_aaa4e8b09ed7acd6.computed ssaQVals D B
private theorem ssa_matches (D : Int) (B : Fin 4 → FixedTape.I) :
    (FixedTape.rowsAux D B [] tape).getD 209 FixedTape.zeroRow = computed D B := by
  rw [←ssa_tape]
  exact MetricDistortion.OptimizedSSAFinite0.S_aaa4e8b09ed7acd6.ssa_matches ssaQVals D B

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
private noncomputable def denominator : Int := 22799449029561241354182696190391353344000000000
private theorem denominator_positive : 0 < denominator := by decide +kernel
private noncomputable def candidateRows (B : Fin 4 → FixedTape.I) : List TapeBounds :=
  (FixedTape.rowsAux denominator B [] tape).map (FixedTape.decodeRow denominator)
private theorem root_in_range : 209 < tape.length := by decide +kernel
private theorem references_valid : tapeRefsValidAux 0 tape = true := by decide +kernel
private theorem candidate_valid (h : Needs) (B : Fin 4 → FixedTape.I) :
    tapeCheck (FixedTape.decodeBox denominator B) tape (candidateRows B) = true :=
  h.child_10.1 denominator denominator_positive B tape references_valid
private theorem candidate_root (B : Fin 4 → FixedTape.I) :
    (candidateRows B).getD 209 zeroTapeBounds = FixedTape.decodeRow denominator (computed denominator B) := by
  unfold candidateRows
  rw [←decode_zeroRow denominator,List.getD_map,ssa_matches]
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨22571454539265628940640869228487439810560000000,22799449029561241354182696190391353344000000000⟩,⟨0,22799449029561241354182696190391353344000000000⟩,⟨0,22799449029561241354182696190391353344000000000⟩,⟨0,22799449029561241354182696190391353344000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := faceI ibox0 0 true
private noncomputable def ibox2 : Fin 4 → FixedTape.I := faceI ibox1 2 true
private noncomputable def ibox3 : Fin 4 → FixedTape.I := faceI ibox2 3 true
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 1 11399724514780620677091348095195676672000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox3 1 11399724514780620677091348095195676672000000000 true
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox5 1 17099586772170931015637022142793515008000000000 false
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox5 1 17099586772170931015637022142793515008000000000 true
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox7 1 19949517900866086184909859166592434176000000000 false
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox7 1 19949517900866086184909859166592434176000000000 true
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox9 1 21374483465213663769546277678491893760000000000 false
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox9 1 21374483465213663769546277678491893760000000000 true
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox11 1 22086966247387452561864486934441623552000000000 false
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox11 1 22086966247387452561864486934441623552000000000 true
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox13 1 22443207638474346958023591562416488448000000000 false
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox13 1 22443207638474346958023591562416488448000000000 true
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox15 1 22621328334017794156103143876403920896000000000 false
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox15 1 22621328334017794156103143876403920896000000000 true
private noncomputable def tree17 : TapeTree := .centered (candidateRows ibox17) (candidateRows (FixedTape.midBox ibox17))
attribute [irreducible] tree17
private theorem sign_17 : 2*denominator*(computed denominator (FixedTape.midBox ibox17)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox17).gradient k).lo.natAbs ((computed denominator ibox17).gradient k).hi.natAbs : Int)*((ibox17 k).hi-(ibox17 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox17
    (computed denominator ibox17) (computed denominator (FixedTape.midBox ibox17))
    (by decide +kernel)
private theorem midpoint_even_17 : ∀ k, 2 ∣ (ibox17 k).lo+(ibox17 k).hi := by decide +kernel
private theorem accepted_17 (h : Needs) : verifyTapeTree tape 209 (FixedTape.decodeBox denominator ibox17) tree17 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox17 midpoint_even_17
  simp only [tree17,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox17,candidate_valid h (FixedTape.midBox ibox17),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox17 209 (FixedTape.rowsAux denominator ibox17 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox17) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_17
private noncomputable def tree16 : TapeTree := .centered (candidateRows ibox16) (candidateRows (FixedTape.midBox ibox16))
attribute [irreducible] tree16
private theorem sign_16 : 2*denominator*(computed denominator (FixedTape.midBox ibox16)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox16).gradient k).lo.natAbs ((computed denominator ibox16).gradient k).hi.natAbs : Int)*((ibox16 k).hi-(ibox16 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox16
    (computed denominator ibox16) (computed denominator (FixedTape.midBox ibox16))
    (by decide +kernel)
private theorem midpoint_even_16 : ∀ k, 2 ∣ (ibox16 k).lo+(ibox16 k).hi := by decide +kernel
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 209 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox16 midpoint_even_16
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox16,candidate_valid h (FixedTape.midBox ibox16),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox16 209 (FixedTape.rowsAux denominator ibox16 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox16) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_16
private noncomputable def tree15 : TapeTree := .split 1 (((22621328334017794156103143876403920896000000000 : Int) : ℚ)/(denominator : ℚ)) tree16 tree17
attribute [irreducible] tree15
private theorem accepted_15 (h : Needs) : verifyTapeTree tape 209 (FixedTape.decodeBox denominator ibox15) tree15 = true := by
  simp only [tree15,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox15 1 (22621328334017794156103143876403920896000000000 : Int) false,decode_split denominator ibox15 1 (22621328334017794156103143876403920896000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_16 h,accepted_17 h⟩
private noncomputable def tree14 : TapeTree := .centered (candidateRows ibox14) (candidateRows (FixedTape.midBox ibox14))
attribute [irreducible] tree14
private theorem sign_14 : 2*denominator*(computed denominator (FixedTape.midBox ibox14)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox14).gradient k).lo.natAbs ((computed denominator ibox14).gradient k).hi.natAbs : Int)*((ibox14 k).hi-(ibox14 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox14
    (computed denominator ibox14) (computed denominator (FixedTape.midBox ibox14))
    (by decide +kernel)
private theorem midpoint_even_14 : ∀ k, 2 ∣ (ibox14 k).lo+(ibox14 k).hi := by decide +kernel
private theorem accepted_14 (h : Needs) : verifyTapeTree tape 209 (FixedTape.decodeBox denominator ibox14) tree14 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox14 midpoint_even_14
  simp only [tree14,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox14,candidate_valid h (FixedTape.midBox ibox14),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox14 209 (FixedTape.rowsAux denominator ibox14 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox14) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_14
private noncomputable def tree13 : TapeTree := .split 1 (((22443207638474346958023591562416488448000000000 : Int) : ℚ)/(denominator : ℚ)) tree14 tree15
attribute [irreducible] tree13
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 209 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox13 1 (22443207638474346958023591562416488448000000000 : Int) false,decode_split denominator ibox13 1 (22443207638474346958023591562416488448000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_14 h,accepted_15 h⟩
private noncomputable def tree12 : TapeTree := .centered (candidateRows ibox12) (candidateRows (FixedTape.midBox ibox12))
attribute [irreducible] tree12
private theorem sign_12 : 2*denominator*(computed denominator (FixedTape.midBox ibox12)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox12).gradient k).lo.natAbs ((computed denominator ibox12).gradient k).hi.natAbs : Int)*((ibox12 k).hi-(ibox12 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox12
    (computed denominator ibox12) (computed denominator (FixedTape.midBox ibox12))
    (by decide +kernel)
private theorem midpoint_even_12 : ∀ k, 2 ∣ (ibox12 k).lo+(ibox12 k).hi := by decide +kernel
private theorem accepted_12 (h : Needs) : verifyTapeTree tape 209 (FixedTape.decodeBox denominator ibox12) tree12 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox12 midpoint_even_12
  simp only [tree12,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox12,candidate_valid h (FixedTape.midBox ibox12),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox12 209 (FixedTape.rowsAux denominator ibox12 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox12) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_12
private noncomputable def tree11 : TapeTree := .split 1 (((22086966247387452561864486934441623552000000000 : Int) : ℚ)/(denominator : ℚ)) tree12 tree13
attribute [irreducible] tree11
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 209 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox11 1 (22086966247387452561864486934441623552000000000 : Int) false,decode_split denominator ibox11 1 (22086966247387452561864486934441623552000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_12 h,accepted_13 h⟩
private noncomputable def tree10 : TapeTree := .centered (candidateRows ibox10) (candidateRows (FixedTape.midBox ibox10))
attribute [irreducible] tree10
private theorem sign_10 : 2*denominator*(computed denominator (FixedTape.midBox ibox10)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox10).gradient k).lo.natAbs ((computed denominator ibox10).gradient k).hi.natAbs : Int)*((ibox10 k).hi-(ibox10 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox10
    (computed denominator ibox10) (computed denominator (FixedTape.midBox ibox10))
    (by decide +kernel)
private theorem midpoint_even_10 : ∀ k, 2 ∣ (ibox10 k).lo+(ibox10 k).hi := by decide +kernel
private theorem accepted_10 (h : Needs) : verifyTapeTree tape 209 (FixedTape.decodeBox denominator ibox10) tree10 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox10 midpoint_even_10
  simp only [tree10,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox10,candidate_valid h (FixedTape.midBox ibox10),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox10 209 (FixedTape.rowsAux denominator ibox10 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox10) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_10
private noncomputable def tree9 : TapeTree := .split 1 (((21374483465213663769546277678491893760000000000 : Int) : ℚ)/(denominator : ℚ)) tree10 tree11
attribute [irreducible] tree9
private theorem accepted_9 (h : Needs) : verifyTapeTree tape 209 (FixedTape.decodeBox denominator ibox9) tree9 = true := by
  simp only [tree9,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox9 1 (21374483465213663769546277678491893760000000000 : Int) false,decode_split denominator ibox9 1 (21374483465213663769546277678491893760000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_10 h,accepted_11 h⟩
private noncomputable def tree8 : TapeTree := .centered (candidateRows ibox8) (candidateRows (FixedTape.midBox ibox8))
attribute [irreducible] tree8
private theorem sign_8 : 2*denominator*(computed denominator (FixedTape.midBox ibox8)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox8).gradient k).lo.natAbs ((computed denominator ibox8).gradient k).hi.natAbs : Int)*((ibox8 k).hi-(ibox8 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox8
    (computed denominator ibox8) (computed denominator (FixedTape.midBox ibox8))
    (by decide +kernel)
private theorem midpoint_even_8 : ∀ k, 2 ∣ (ibox8 k).lo+(ibox8 k).hi := by decide +kernel
private theorem accepted_8 (h : Needs) : verifyTapeTree tape 209 (FixedTape.decodeBox denominator ibox8) tree8 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox8 midpoint_even_8
  simp only [tree8,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox8,candidate_valid h (FixedTape.midBox ibox8),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox8 209 (FixedTape.rowsAux denominator ibox8 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox8) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_8
private noncomputable def tree7 : TapeTree := .split 1 (((19949517900866086184909859166592434176000000000 : Int) : ℚ)/(denominator : ℚ)) tree8 tree9
attribute [irreducible] tree7
private theorem accepted_7 (h : Needs) : verifyTapeTree tape 209 (FixedTape.decodeBox denominator ibox7) tree7 = true := by
  simp only [tree7,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox7 1 (19949517900866086184909859166592434176000000000 : Int) false,decode_split denominator ibox7 1 (19949517900866086184909859166592434176000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_8 h,accepted_9 h⟩
private noncomputable def tree6 : TapeTree := .centered (candidateRows ibox6) (candidateRows (FixedTape.midBox ibox6))
attribute [irreducible] tree6
private theorem sign_6 : 2*denominator*(computed denominator (FixedTape.midBox ibox6)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox6).gradient k).lo.natAbs ((computed denominator ibox6).gradient k).hi.natAbs : Int)*((ibox6 k).hi-(ibox6 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox6
    (computed denominator ibox6) (computed denominator (FixedTape.midBox ibox6))
    (by decide +kernel)
private theorem midpoint_even_6 : ∀ k, 2 ∣ (ibox6 k).lo+(ibox6 k).hi := by decide +kernel
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 209 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox6 midpoint_even_6
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox6,candidate_valid h (FixedTape.midBox ibox6),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox6 209 (FixedTape.rowsAux denominator ibox6 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox6) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_6
private noncomputable def tree5 : TapeTree := .split 1 (((17099586772170931015637022142793515008000000000 : Int) : ℚ)/(denominator : ℚ)) tree6 tree7
attribute [irreducible] tree5
private theorem accepted_5 (h : Needs) : verifyTapeTree tape 209 (FixedTape.decodeBox denominator ibox5) tree5 = true := by
  simp only [tree5,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox5 1 (17099586772170931015637022142793515008000000000 : Int) false,decode_split denominator ibox5 1 (17099586772170931015637022142793515008000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_6 h,accepted_7 h⟩
private noncomputable def tree4 : TapeTree := .centered (candidateRows ibox4) (candidateRows (FixedTape.midBox ibox4))
attribute [irreducible] tree4
private theorem sign_4 : 2*denominator*(computed denominator (FixedTape.midBox ibox4)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox4).gradient k).lo.natAbs ((computed denominator ibox4).gradient k).hi.natAbs : Int)*((ibox4 k).hi-(ibox4 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox4
    (computed denominator ibox4) (computed denominator (FixedTape.midBox ibox4))
    (by decide +kernel)
private theorem midpoint_even_4 : ∀ k, 2 ∣ (ibox4 k).lo+(ibox4 k).hi := by decide +kernel
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 209 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox4 midpoint_even_4
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox4,candidate_valid h (FixedTape.midBox ibox4),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox4 209 (FixedTape.rowsAux denominator ibox4 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox4) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_4
private noncomputable def tree3 : TapeTree := .split 1 (((11399724514780620677091348095195676672000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree5
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 209 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 1 (11399724514780620677091348095195676672000000000 : Int) false,decode_split denominator ibox3 1 (11399724514780620677091348095195676672000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_5 h⟩
private noncomputable def tree2 : TapeTree := .face 3 true (candidateRows ibox2) tree3
attribute [irreducible] tree2
private theorem sign_2 : 0 ≤ ((computed denominator ibox2).gradient 3).lo := by decide +kernel
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 209 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox2,?_,accepted_3 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox2)).gradient 3).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox2).gradient 3).lo) denominator_positive).2 sign_2
private noncomputable def tree1 : TapeTree := .face 2 true (candidateRows ibox1) tree2
attribute [irreducible] tree1
private theorem sign_1 : 0 ≤ ((computed denominator ibox1).gradient 2).lo := by decide +kernel
private theorem accepted_1 (h : Needs) : verifyTapeTree tape 209 (FixedTape.decodeBox denominator ibox1) tree1 = true := by
  simp only [tree1,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox1,?_,accepted_2 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox1)).gradient 2).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox1).gradient 2).lo) denominator_positive).2 sign_1
private noncomputable def tree0 : TapeTree := .face 0 true (candidateRows ibox0) tree1
attribute [irreducible] tree0
private theorem sign_0 : 0 ≤ ((computed denominator ibox0).gradient 0).lo := by decide +kernel
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 209 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox0,?_,accepted_1 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox0)).gradient 0).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox0).gradient 0).lo) denominator_positive).2 sign_0
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (99/100 : ℚ) (1/1 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 209 = e230 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (99/100 : ℚ) (1/1 : ℚ)) x → eval e230 x ≤ 0 := by
  have hb := h.child_4 tape 209 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell127_high_first_bottom

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell127_high_first_bottom
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((99/100 : ℚ) : ℝ) < p ∧ p ≤ ((1/1 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 127 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 127 p)
    (hkb : ((1/1 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((99/100 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : a ≤ bStar), firstResidual (0 : Fin 9) a p r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell127_high_first_bottom.cell_bound h.child_8 h.child_9 (Cell127_high_first_bottom.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell127_high_first_bottom
