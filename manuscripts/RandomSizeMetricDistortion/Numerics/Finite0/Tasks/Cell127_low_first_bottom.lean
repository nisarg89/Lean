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
namespace Cell127_low_first_bottom
private noncomputable def qValues : Fin 1 → ℚ := ![(0/1 : ℚ)]
private noncomputable abbrev e2 : PolyExpr := SharedFiniteSemantics33.e2 qValues
private noncomputable abbrev e7 : PolyExpr := SharedFiniteSemantics33.e7 qValues
private noncomputable abbrev e12 : PolyExpr := SharedFiniteSemantics33.e12 qValues
private noncomputable abbrev e15 : PolyExpr := SharedFiniteSemantics33.e15 qValues
private noncomputable abbrev e231 : PolyExpr := SharedFiniteSemantics33.e231 qValues
private noncomputable abbrev node_1 := SharedFiniteSemantics33.node_1 qValues
private noncomputable abbrev node_2 := SharedFiniteSemantics33.node_2 qValues
private noncomputable abbrev node_3 := SharedFiniteSemantics33.node_3 qValues
private noncomputable abbrev node_4 := SharedFiniteSemantics33.node_4 qValues
private noncomputable abbrev node_6 := SharedFiniteSemantics33.node_6 qValues
private noncomputable abbrev node_7 := SharedFiniteSemantics33.node_7 qValues
private noncomputable abbrev node_10 := SharedFiniteSemantics33.node_10 qValues
private noncomputable abbrev node_11 := SharedFiniteSemantics33.node_11 qValues
private noncomputable abbrev node_12 := SharedFiniteSemantics33.node_12 qValues
private noncomputable abbrev node_14 := SharedFiniteSemantics33.node_14 qValues
private noncomputable abbrev node_15 := SharedFiniteSemantics33.node_15 qValues
private noncomputable abbrev node_214 := SharedFiniteSemantics33.node_214 qValues
private noncomputable abbrev node_215 := SharedFiniteSemantics33.node_215 qValues
private noncomputable abbrev node_216 := SharedFiniteSemantics33.node_216 qValues
private noncomputable abbrev node_230 := SharedFiniteSemantics33.node_230 qValues
private noncomputable abbrev node_231 := SharedFiniteSemantics33.node_231 qValues
private noncomputable abbrev semantic_psi_33 := SharedFiniteSemantics33.semantic_psi_33 qValues
private noncomputable abbrev semantic_psi_229 := SharedFiniteSemantics33.semantic_psi_229 qValues
private noncomputable abbrev semantic_increment_212 := SharedFiniteSemantics33.semantic_increment_212 qValues
private noncomputable abbrev semantic_dH_213 := SharedFiniteSemantics33.semantic_dH_213 qValues
private noncomputable def aPoint (x : Fin 4 → ℝ) : ℝ := ((49/100 : ℚ) : ℝ)*x 1
private noncomputable def rPoint (x : Fin 4 → ℝ) : ℝ := ((49/100 : ℚ) : ℝ)+(((2840189/5000000 : ℚ) : ℝ)-((49/100 : ℚ) : ℝ))*x 2
private noncomputable def yPoint (x : Fin 4 → ℝ) : ℝ := aPoint x+1-x 0
private theorem point_7 (x : Fin 4 → ℝ) : eval e7 x = aPoint x := by
  simp only [node_3,node_6,node_7] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_12 (x : Fin 4 → ℝ) : eval e12 x = rPoint x := by
  simp only [node_4,node_6,node_10,node_11,node_12] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_2 (x : Fin 4 → ℝ) : eval e2 x = x 0 := by
  simp only [node_2] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_15 (x : Fin 4 → ℝ) : eval e15 x = 1-x 0 := by
  simp only [node_1,node_2,node_14,node_15] <;>
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
    (1)*eval e231 x = (1)*(aPoint x+priceLambda 127 (x 0)*(HStar (yPoint x)-HStar (aPoint x))+priceTau 127 (x 0)*psiStar (rPoint x)+(0)-(cStar)) := by
  have hp0 : x 0 ≠ 0 := ne_of_gt hp.1
  have hp1 : x 0 ≠ 1 := ne_of_lt hp.2
  have heps : 1-x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  rw [price_lambda_normal _ hp,price_tau_normal _ hp]
  simp only [node_214,node_215,node_216,node_230,node_231,semantic_psi_33,semantic_psi_229,semantic_increment_212,semantic_dH_213,point_7,point_12,point_2,point_15]
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
    (1)*eval e231 x = (1)*(firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (99/100 : ℚ) (1/1 : ℚ)) x → eval e231 x ≤ 0)
    (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((99/100 : ℚ) : ℝ) < p ∧ p ≤ ((1/1 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 127 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 127 p)
    (hk0 : ((1/1 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((99/100 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : a ≤ ((49/100 : ℚ) : ℝ)) :
    firstResidual (0 : Fin 9) a p r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨x,hx,hxp,hxa,hxr⟩ := h1 (99/100 : ℚ) (1/1 : ℚ) ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ) p a r hpcell hk0 hr ha hap hcase
  have hcut : ¬(((1/1 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ)) := by norm_num [bStar]
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,if_neg hcut] using hxa
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,if_neg hcut] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 127 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 127 (x 0) := by simpa only [hxp] using hT
  have hrootb : ((2840189/5000000 : ℚ) : ℝ) ≤ bStar := by norm_num [bStar]
  have hflag : aPoint x ≤ bStar := by rw [hax]; exact (hap.trans (min_le_right _ _)).trans (hr.2.trans hrootb)
  have hb := hbound x hx
  have hv : (1 : ℝ)*eval e231 x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 1) hb
  rw [actual_identity hs x hpx hflag hLx hTx] at hv
  simp only [one_mul] at hv
  simpa only [hxp,hax,hrx] using hv
private noncomputable def tape : List TapeOp := [
.const (1/1 : ℚ),
.var 0,
.var 1,
.const (49/100 : ℚ),
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
private noncomputable def ssaQVals : Fin 29 → ℚ := ![(1/1 : ℚ),(49/100 : ℚ),(1085/4818 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ),(4818/3733 : ℚ),(627/3733 : ℚ),(1155/3733 : ℚ),(385/3733 : ℚ),(38544/3733 : ℚ),(398288/3733 : ℚ),(2987160/3733 : ℚ),(17325528/3733 : ℚ),(80852464/3733 : ℚ),(311859504/3733 : ℚ),(1013543388/3733 : ℚ),(2815398300/3733 : ℚ),(6756955920/3733 : ℚ),(14128180560/3733 : ℚ),(25901664360/3733 : ℚ),(41841150120/3733 : ℚ),(59773071600/3733 : ℚ),(75712557360/3733 : ℚ),(85176627030/3733 : ℚ),(2409/3733 : ℚ),(73/3733 : ℚ),(145513/100000 : ℚ),(-113609/200000 : ℚ)]
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
private noncomputable def denominator : Int := 712482782173788792318209255949729792000000000
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
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨705357954352050904395027163390232494080000000,712482782173788792318209255949729792000000000⟩,⟨0,712482782173788792318209255949729792000000000⟩,⟨0,712482782173788792318209255949729792000000000⟩,⟨0,712482782173788792318209255949729792000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := faceI ibox0 0 true
private noncomputable def ibox2 : Fin 4 → FixedTape.I := faceI ibox1 1 true
private noncomputable def tree2 : TapeTree := .direct (candidateRows ibox2)
attribute [irreducible] tree2
private theorem sign_2 : (computed denominator ibox2).value.hi ≤ 0 := by decide +kernel
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 209 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  refine ⟨root_in_range,candidate_valid h ibox2,?_⟩
  rw [candidate_root]
  simpa [FixedTape.decodeRow,FixedTape.decode] using (h.child_10.2.2.2.1 denominator (computed denominator ibox2).value.hi denominator_positive).1 sign_2
private noncomputable def tree1 : TapeTree := .face 1 true (candidateRows ibox1) tree2
attribute [irreducible] tree1
private theorem sign_1 : 0 ≤ ((computed denominator ibox1).gradient 1).lo := by decide +kernel
private theorem accepted_1 (h : Needs) : verifyTapeTree tape 209 (FixedTape.decodeBox denominator ibox1) tree1 = true := by
  simp only [tree1,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox1,?_,accepted_2 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox1)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox1).gradient 1).lo) denominator_positive).2 sign_1
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
private theorem same_expression : tapeExpr tape 209 = e231 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (99/100 : ℚ) (1/1 : ℚ)) x → eval e231 x ≤ 0 := by
  have hb := h.child_4 tape 209 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell127_low_first_bottom

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell127_low_first_bottom
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((99/100 : ℚ) : ℝ) < p ∧ p ≤ ((1/1 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 127 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 127 p)
    (hk0 : ((1/1 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((99/100 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : a ≤ ((49/100 : ℚ) : ℝ)), firstResidual (0 : Fin 9) a p r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell127_low_first_bottom.cell_bound h.child_8 h.child_9 (Cell127_low_first_bottom.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell127_low_first_bottom
