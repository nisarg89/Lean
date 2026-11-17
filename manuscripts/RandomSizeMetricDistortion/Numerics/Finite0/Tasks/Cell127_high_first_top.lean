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
namespace Cell127_high_first_top
private noncomputable def qValues : Fin 1 → ℚ := ![(0/1 : ℚ)]
private noncomputable abbrev e2 : PolyExpr := SharedFiniteSemantics36.e2 qValues
private noncomputable abbrev e10 : PolyExpr := SharedFiniteSemantics36.e10 qValues
private noncomputable abbrev e14 : PolyExpr := SharedFiniteSemantics36.e14 qValues
private noncomputable abbrev e40 : PolyExpr := SharedFiniteSemantics36.e40 qValues
private noncomputable abbrev e45 : PolyExpr := SharedFiniteSemantics36.e45 qValues
private noncomputable abbrev e225 : PolyExpr := SharedFiniteSemantics36.e225 qValues
private noncomputable abbrev node_1 := SharedFiniteSemantics36.node_1 qValues
private noncomputable abbrev node_2 := SharedFiniteSemantics36.node_2 qValues
private noncomputable abbrev node_3 := SharedFiniteSemantics36.node_3 qValues
private noncomputable abbrev node_4 := SharedFiniteSemantics36.node_4 qValues
private noncomputable abbrev node_6 := SharedFiniteSemantics36.node_6 qValues
private noncomputable abbrev node_7 := SharedFiniteSemantics36.node_7 qValues
private noncomputable abbrev node_8 := SharedFiniteSemantics36.node_8 qValues
private noncomputable abbrev node_9 := SharedFiniteSemantics36.node_9 qValues
private noncomputable abbrev node_10 := SharedFiniteSemantics36.node_10 qValues
private noncomputable abbrev node_11 := SharedFiniteSemantics36.node_11 qValues
private noncomputable abbrev node_12 := SharedFiniteSemantics36.node_12 qValues
private noncomputable abbrev node_13 := SharedFiniteSemantics36.node_13 qValues
private noncomputable abbrev node_14 := SharedFiniteSemantics36.node_14 qValues
private noncomputable abbrev node_35 := SharedFiniteSemantics36.node_35 qValues
private noncomputable abbrev node_39 := SharedFiniteSemantics36.node_39 qValues
private noncomputable abbrev node_40 := SharedFiniteSemantics36.node_40 qValues
private noncomputable abbrev node_41 := SharedFiniteSemantics36.node_41 qValues
private noncomputable abbrev node_42 := SharedFiniteSemantics36.node_42 qValues
private noncomputable abbrev node_43 := SharedFiniteSemantics36.node_43 qValues
private noncomputable abbrev node_44 := SharedFiniteSemantics36.node_44 qValues
private noncomputable abbrev node_45 := SharedFiniteSemantics36.node_45 qValues
private noncomputable abbrev node_225 := SharedFiniteSemantics36.node_225 qValues
private noncomputable abbrev semantic_psi_34 := SharedFiniteSemantics36.semantic_psi_34 qValues
private noncomputable abbrev semantic_increment_224 := SharedFiniteSemantics36.semantic_increment_224 qValues
private noncomputable abbrev semantic_pdiff_326 := SharedFiniteSemantics36.semantic_pdiff_326 qValues
private noncomputable def aPoint (x : Fin 4 → ℝ) : ℝ := bStar+(x 0-bStar)*x 1
private noncomputable def rPoint (x : Fin 4 → ℝ) : ℝ := aPoint x+(1-aPoint x)*x 2
private noncomputable def yPoint (x : Fin 4 → ℝ) : ℝ := aPoint x+1-x 0
private theorem point_10 (x : Fin 4 → ℝ) : eval e10 x = aPoint x := by
  simp only [node_2,node_3,node_6,node_7,node_8,node_9,node_10] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_14 (x : Fin 4 → ℝ) : eval e14 x = rPoint x := by
  simp only [node_1,node_2,node_3,node_4,node_6,node_7,node_8,node_9,node_10,node_11,node_12,node_13,node_14] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_2 (x : Fin 4 → ℝ) : eval e2 x = x 0 := by
  simp only [node_2] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_40 (x : Fin 4 → ℝ) : eval e40 x = 1-x 0 := by
  simp only [node_1,node_2,node_39,node_40] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_45 (x : Fin 4 → ℝ) : eval e45 x = rPoint x-aPoint x := by
  simp only [node_1,node_2,node_3,node_4,node_7,node_8,node_39,node_40,node_41,node_42,node_43,node_44,node_45] <;>
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
    (1)*eval e225 x = (1)*(aPoint x+priceLambda 127 (x 0)*(HStar (yPoint x)-HStar (aPoint x))+priceTau 127 (x 0)*psiStar (rPoint x)+(cStar-aPoint x-eta (0 : Fin 9)*psiStar (aPoint x))-(cStar)) := by
  have hp0 : x 0 ≠ 0 := ne_of_gt hp.1
  have hp1 : x 0 ≠ 1 := ne_of_lt hp.2
  have heps : 1-x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  rw [price_lambda_normal _ hp,price_tau_normal _ hp]
  simp only [node_35,node_225,semantic_psi_34,semantic_increment_224,semantic_pdiff_326,point_10,point_14,point_2,point_40,point_45]
  have hlarge := large_first_top hs (aPoint x) (x 0) (rPoint x) (145513/100000 : ℝ) (1/1 : ℝ) cStar hp1
  have hy : aPoint x+(1-x 0) = yPoint x := by dsimp only [yPoint]; ring
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
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) (ha : bStar < aPoint x)
    (hL : lambdaStar (x 0) = priceLambda 127 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 127 (x 0)) :
    (1)*eval e225 x = (1)*(firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_neg (not_le.mpr ha),hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (99/100 : ℚ) (1/1 : ℚ)) x → eval e225 x ≤ 0)
    (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((99/100 : ℚ) : ℝ) < p ∧ p ≤ ((1/1 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 127 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 127 p)
    (hkb : ((1/1 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((99/100 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : bStar < a) :
    firstResidual (0 : Fin 9) a p r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxr⟩ := h5 (99/100 : ℚ) (1/1 : ℚ) bStar p a r hpcell hkb hr.2 hap hcase
  have hax : aPoint x = a := by simpa only [aPoint,rPoint] using hxa
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 127 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 127 (x 0) := by simpa only [hxp] using hT
  have hflag : bStar < aPoint x := by simpa only [hax] using hcase
  have hb := hbound x hx
  have hv : (1 : ℝ)*eval e225 x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 1) hb
  rw [actual_identity hs x hpx hflag hLx hTx] at hv
  simp only [one_mul] at hv
  simpa only [hxp,hax,hrx] using hv
private noncomputable def tape : List TapeOp := [
.const (1/1 : ℚ),
.var 0,
.var 1,
.const (2840189/5000000 : ℚ),
.const (-2840189/5000000 : ℚ),
.add 1 4,
.mul 5 2,
.add 3 6,
.mul 7 7,
.mul 8 8,
.mul 9 9,
.mul 10 10,
.const (145513/100000 : ℚ),
.neg 1,
.add 0 13,
.const (627/3733 : ℚ),
.mul 15 14,
.mul 7 14,
.const (1155/3733 : ℚ),
.mul 18 17,
.add 16 19,
.mul 14 14,
.const (385/3733 : ℚ),
.mul 22 21,
.add 20 23,
.mul 7 8,
.mul 25 25,
.mul 7 26,
.mul 27 27,
.mul 7 28,
.mul 29 29,
.mul 7 30,
.mul 31 14,
.const (38544/3733 : ℚ),
.mul 33 32,
.add 24 34,
.mul 30 21,
.const (398288/3733 : ℚ),
.mul 37 36,
.add 35 38,
.mul 28 28,
.mul 7 40,
.mul 14 21,
.mul 41 42,
.const (2987160/3733 : ℚ),
.mul 44 43,
.add 39 45,
.mul 21 21,
.mul 40 47,
.const (17325528/3733 : ℚ),
.mul 49 48,
.add 46 50,
.mul 26 26,
.mul 7 52,
.mul 53 53,
.mul 7 54,
.mul 14 47,
.mul 55 56,
.const (80852464/3733 : ℚ),
.mul 58 57,
.add 51 59,
.mul 42 42,
.mul 54 61,
.const (311859504/3733 : ℚ),
.mul 63 62,
.add 60 64,
.mul 52 52,
.mul 7 66,
.mul 14 61,
.mul 67 68,
.const (1013543388/3733 : ℚ),
.mul 70 69,
.add 65 71,
.mul 47 47,
.mul 66 73,
.const (2815398300/3733 : ℚ),
.mul 75 74,
.add 72 76,
.mul 7 9,
.mul 78 78,
.mul 7 79,
.mul 80 80,
.mul 7 81,
.mul 14 73,
.mul 82 83,
.const (6756955920/3733 : ℚ),
.mul 85 84,
.add 77 86,
.mul 56 56,
.mul 81 88,
.const (14128180560/3733 : ℚ),
.mul 90 89,
.add 87 91,
.mul 79 79,
.mul 7 93,
.mul 14 88,
.mul 94 95,
.const (25901664360/3733 : ℚ),
.mul 97 96,
.add 92 98,
.mul 61 61,
.mul 93 100,
.const (41841150120/3733 : ℚ),
.mul 102 101,
.add 99 103,
.mul 7 10,
.mul 105 105,
.mul 7 106,
.mul 14 100,
.mul 107 108,
.const (59773071600/3733 : ℚ),
.mul 110 109,
.add 104 111,
.mul 68 68,
.mul 106 113,
.const (75712557360/3733 : ℚ),
.mul 115 114,
.add 112 116,
.mul 7 11,
.mul 14 113,
.mul 118 119,
.const (85176627030/3733 : ℚ),
.mul 121 120,
.add 117 122,
.mul 73 73,
.mul 11 124,
.mul 121 125,
.add 123 126,
.mul 14 124,
.mul 29 128,
.mul 115 129,
.add 127 130,
.mul 83 83,
.mul 28 132,
.mul 110 133,
.add 131 134,
.mul 14 132,
.mul 53 136,
.mul 102 137,
.add 135 138,
.mul 88 88,
.mul 52 140,
.mul 97 141,
.add 139 142,
.mul 14 140,
.mul 80 144,
.mul 90 145,
.add 143 146,
.mul 95 95,
.mul 79 148,
.mul 85 149,
.add 147 150,
.mul 14 148,
.mul 105 152,
.mul 75 153,
.add 151 154,
.mul 100 100,
.mul 10 156,
.mul 70 157,
.add 155 158,
.mul 14 156,
.mul 27 160,
.mul 63 161,
.add 159 162,
.mul 108 108,
.mul 26 164,
.mul 58 165,
.add 163 166,
.mul 14 164,
.mul 78 168,
.mul 49 169,
.add 167 170,
.mul 113 113,
.mul 9 172,
.mul 44 173,
.add 171 174,
.mul 14 172,
.mul 25 176,
.mul 37 177,
.add 175 178,
.mul 119 119,
.mul 8 180,
.mul 33 181,
.add 179 182,
.mul 14 180,
.mul 7 184,
.const (2409/3733 : ℚ),
.mul 186 185,
.add 183 187,
.mul 124 124,
.const (73/3733 : ℚ),
.mul 190 189,
.add 188 191,
.neg 192,
.mul 12 193]
private noncomputable def ssaQVals : Fin 24 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(-2840189/5000000 : ℚ),(145513/100000 : ℚ),(627/3733 : ℚ),(1155/3733 : ℚ),(385/3733 : ℚ),(38544/3733 : ℚ),(398288/3733 : ℚ),(2987160/3733 : ℚ),(17325528/3733 : ℚ),(80852464/3733 : ℚ),(311859504/3733 : ℚ),(1013543388/3733 : ℚ),(2815398300/3733 : ℚ),(6756955920/3733 : ℚ),(14128180560/3733 : ℚ),(25901664360/3733 : ℚ),(41841150120/3733 : ℚ),(59773071600/3733 : ℚ),(75712557360/3733 : ℚ),(85176627030/3733 : ℚ),(2409/3733 : ℚ),(73/3733 : ℚ)]
private theorem ssa_tape : MetricDistortion.OptimizedSSAFinite0.S_320a5ceee8cec79b.p195 ssaQVals = tape := by rfl
private noncomputable def computed (D : Int) (B : Fin 4 → FixedTape.I) : FixedTape.Row :=
  MetricDistortion.OptimizedSSAFinite0.S_320a5ceee8cec79b.computed ssaQVals D B
private theorem ssa_matches (D : Int) (B : Fin 4 → FixedTape.I) :
    (FixedTape.rowsAux D B [] tape).getD 194 FixedTape.zeroRow = computed D B := by
  rw [←ssa_tape]
  exact MetricDistortion.OptimizedSSAFinite0.S_320a5ceee8cec79b.ssa_matches ssaQVals D B

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
private theorem root_in_range : 194 < tape.length := by decide +kernel
private theorem references_valid : tapeRefsValidAux 0 tape = true := by decide +kernel
private theorem candidate_valid (h : Needs) (B : Fin 4 → FixedTape.I) :
    tapeCheck (FixedTape.decodeBox denominator B) tape (candidateRows B) = true :=
  h.child_10.1 denominator denominator_positive B tape references_valid
private theorem candidate_root (B : Fin 4 → FixedTape.I) :
    (candidateRows B).getD 194 zeroTapeBounds = FixedTape.decodeRow denominator (computed denominator B) := by
  unfold candidateRows
  rw [←decode_zeroRow denominator,List.getD_map,ssa_matches]
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨705357954352050904395027163390232494080000000,712482782173788792318209255949729792000000000⟩,⟨0,712482782173788792318209255949729792000000000⟩,⟨0,712482782173788792318209255949729792000000000⟩,⟨0,712482782173788792318209255949729792000000000⟩]
private noncomputable def tree0 : TapeTree := .direct (candidateRows ibox0)
attribute [irreducible] tree0
private theorem sign_0 : (computed denominator ibox0).value.hi ≤ 0 := by decide +kernel
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 194 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  refine ⟨root_in_range,candidate_valid h ibox0,?_⟩
  rw [candidate_root]
  simpa [FixedTape.decodeRow,FixedTape.decode] using (h.child_10.2.2.2.1 denominator (computed denominator ibox0).value.hi denominator_positive).1 sign_0
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (99/100 : ℚ) (1/1 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 194 = e225 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (99/100 : ℚ) (1/1 : ℚ)) x → eval e225 x ≤ 0 := by
  have hb := h.child_4 tape 194 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell127_high_first_top

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell127_high_first_top
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((99/100 : ℚ) : ℝ) < p ∧ p ≤ ((1/1 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 127 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 127 p)
    (hkb : ((1/1 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((99/100 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : bStar < a), firstResidual (0 : Fin 9) a p r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell127_high_first_top.cell_bound h.child_8 h.child_9 (Cell127_high_first_top.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell127_high_first_top
