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
namespace Cell127_low_first_top
private noncomputable def qValues : Fin 1 → ℚ := ![(0/1 : ℚ)]
private noncomputable abbrev e2 : PolyExpr := SharedFiniteSemantics34.e2 qValues
private noncomputable abbrev e11 : PolyExpr := SharedFiniteSemantics34.e11 qValues
private noncomputable abbrev e15 : PolyExpr := SharedFiniteSemantics34.e15 qValues
private noncomputable abbrev e18 : PolyExpr := SharedFiniteSemantics34.e18 qValues
private noncomputable abbrev e234 : PolyExpr := SharedFiniteSemantics34.e234 qValues
private noncomputable abbrev node_1 := SharedFiniteSemantics34.node_1 qValues
private noncomputable abbrev node_2 := SharedFiniteSemantics34.node_2 qValues
private noncomputable abbrev node_3 := SharedFiniteSemantics34.node_3 qValues
private noncomputable abbrev node_4 := SharedFiniteSemantics34.node_4 qValues
private noncomputable abbrev node_6 := SharedFiniteSemantics34.node_6 qValues
private noncomputable abbrev node_7 := SharedFiniteSemantics34.node_7 qValues
private noncomputable abbrev node_9 := SharedFiniteSemantics34.node_9 qValues
private noncomputable abbrev node_10 := SharedFiniteSemantics34.node_10 qValues
private noncomputable abbrev node_11 := SharedFiniteSemantics34.node_11 qValues
private noncomputable abbrev node_12 := SharedFiniteSemantics34.node_12 qValues
private noncomputable abbrev node_13 := SharedFiniteSemantics34.node_13 qValues
private noncomputable abbrev node_14 := SharedFiniteSemantics34.node_14 qValues
private noncomputable abbrev node_15 := SharedFiniteSemantics34.node_15 qValues
private noncomputable abbrev node_17 := SharedFiniteSemantics34.node_17 qValues
private noncomputable abbrev node_18 := SharedFiniteSemantics34.node_18 qValues
private noncomputable abbrev node_217 := SharedFiniteSemantics34.node_217 qValues
private noncomputable abbrev node_218 := SharedFiniteSemantics34.node_218 qValues
private noncomputable abbrev node_219 := SharedFiniteSemantics34.node_219 qValues
private noncomputable abbrev node_233 := SharedFiniteSemantics34.node_233 qValues
private noncomputable abbrev node_234 := SharedFiniteSemantics34.node_234 qValues
private noncomputable abbrev semantic_psi_36 := SharedFiniteSemantics34.semantic_psi_36 qValues
private noncomputable abbrev semantic_psi_232 := SharedFiniteSemantics34.semantic_psi_232 qValues
private noncomputable abbrev semantic_increment_215 := SharedFiniteSemantics34.semantic_increment_215 qValues
private noncomputable abbrev semantic_dH_216 := SharedFiniteSemantics34.semantic_dH_216 qValues
private noncomputable def aPoint (x : Fin 4 → ℝ) : ℝ := ((49/100 : ℚ) : ℝ)+(((2840189/5000000 : ℚ) : ℝ)-((49/100 : ℚ) : ℝ))*x 1
private noncomputable def rPoint (x : Fin 4 → ℝ) : ℝ := aPoint x+(((2840189/5000000 : ℚ) : ℝ)-aPoint x)*x 2
private noncomputable def yPoint (x : Fin 4 → ℝ) : ℝ := aPoint x+1-x 0
private theorem point_11 (x : Fin 4 → ℝ) : eval e11 x = aPoint x := by
  simp only [node_3,node_6,node_9,node_10,node_11] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_15 (x : Fin 4 → ℝ) : eval e15 x = rPoint x := by
  simp only [node_3,node_4,node_6,node_7,node_9,node_10,node_11,node_12,node_13,node_14,node_15] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_2 (x : Fin 4 → ℝ) : eval e2 x = x 0 := by
  simp only [node_2] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_18 (x : Fin 4 → ℝ) : eval e18 x = 1-x 0 := by
  simp only [node_1,node_2,node_17,node_18] <;>
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
    (1)*eval e234 x = (1)*(aPoint x+priceLambda 127 (x 0)*(HStar (yPoint x)-HStar (aPoint x))+priceTau 127 (x 0)*psiStar (rPoint x)+(0)-(cStar)) := by
  have hp0 : x 0 ≠ 0 := ne_of_gt hp.1
  have hp1 : x 0 ≠ 1 := ne_of_lt hp.2
  have heps : 1-x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  rw [price_lambda_normal _ hp,price_tau_normal _ hp]
  simp only [node_217,node_218,node_219,node_233,node_234,semantic_psi_36,semantic_psi_232,semantic_increment_215,semantic_dH_216,point_11,point_15,point_2,point_18]
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
    (1)*eval e234 x = (1)*(firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (99/100 : ℚ) (1/1 : ℚ)) x → eval e234 x ≤ 0)
    (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((99/100 : ℚ) : ℝ) < p ∧ p ≤ ((1/1 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 127 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 127 p)
    (hk0 : ((1/1 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((99/100 : ℚ) : ℝ))
    (hk1 : ((1/1 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((99/100 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : ((49/100 : ℚ) : ℝ) < a) :
    firstResidual (0 : Fin 9) a p r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxr⟩ := h2 (99/100 : ℚ) (1/1 : ℚ) ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ) p a r hpcell hk0 hk1 hr hap hcase
  have hcut : ¬(((1/1 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ)) := by norm_num [bStar]
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,if_neg hcut] using hxa
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,if_neg hcut] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 127 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 127 (x 0) := by simpa only [hxp] using hT
  have hrootb : ((2840189/5000000 : ℚ) : ℝ) ≤ bStar := by norm_num [bStar]
  have hflag : aPoint x ≤ bStar := by rw [hax]; exact (hap.trans (min_le_right _ _)).trans (hr.2.trans hrootb)
  have hb := hbound x hx
  have hv : (1 : ℝ)*eval e234 x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 1) hb
  rw [actual_identity hs x hpx hflag hLx hTx] at hv
  simp only [one_mul] at hv
  simpa only [hxp,hax,hrx] using hv
private noncomputable def tape : List TapeOp := [
.const (1/1 : ℚ),
.var 0,
.var 1,
.const (49/100 : ℚ),
.const (390189/5000000 : ℚ),
.mul 4 2,
.add 3 5,
.neg 1,
.add 0 7,
.const (1085/4818 : ℚ),
.const (19/73 : ℚ),
.mul 10 6,
.mul 6 6,
.const (35/146 : ℚ),
.mul 13 12,
.add 11 14,
.mul 12 12,
.mul 16 16,
.mul 17 17,
.mul 18 18,
.const (1/2 : ℚ),
.mul 20 19,
.add 15 21,
.neg 22,
.add 9 23,
.const (4818/3733 : ℚ),
.mul 25 24,
.const (627/3733 : ℚ),
.mul 27 8,
.mul 6 8,
.const (1155/3733 : ℚ),
.mul 30 29,
.add 28 31,
.mul 8 8,
.const (385/3733 : ℚ),
.mul 34 33,
.add 32 35,
.mul 6 12,
.mul 37 37,
.mul 6 38,
.mul 39 39,
.mul 6 40,
.mul 41 41,
.mul 6 42,
.mul 43 8,
.const (38544/3733 : ℚ),
.mul 45 44,
.add 36 46,
.mul 42 33,
.const (398288/3733 : ℚ),
.mul 49 48,
.add 47 50,
.mul 40 40,
.mul 6 52,
.mul 8 33,
.mul 53 54,
.const (2987160/3733 : ℚ),
.mul 56 55,
.add 51 57,
.mul 33 33,
.mul 52 59,
.const (17325528/3733 : ℚ),
.mul 61 60,
.add 58 62,
.mul 38 38,
.mul 6 64,
.mul 65 65,
.mul 6 66,
.mul 8 59,
.mul 67 68,
.const (80852464/3733 : ℚ),
.mul 70 69,
.add 63 71,
.mul 54 54,
.mul 66 73,
.const (311859504/3733 : ℚ),
.mul 75 74,
.add 72 76,
.mul 64 64,
.mul 6 78,
.mul 8 73,
.mul 79 80,
.const (1013543388/3733 : ℚ),
.mul 82 81,
.add 77 83,
.mul 59 59,
.mul 78 85,
.const (2815398300/3733 : ℚ),
.mul 87 86,
.add 84 88,
.mul 6 16,
.mul 90 90,
.mul 6 91,
.mul 92 92,
.mul 6 93,
.mul 8 85,
.mul 94 95,
.const (6756955920/3733 : ℚ),
.mul 97 96,
.add 89 98,
.mul 68 68,
.mul 93 100,
.const (14128180560/3733 : ℚ),
.mul 102 101,
.add 99 103,
.mul 91 91,
.mul 6 105,
.mul 8 100,
.mul 106 107,
.const (25901664360/3733 : ℚ),
.mul 109 108,
.add 104 110,
.mul 73 73,
.mul 105 112,
.const (41841150120/3733 : ℚ),
.mul 114 113,
.add 111 115,
.mul 6 17,
.mul 117 117,
.mul 6 118,
.mul 8 112,
.mul 119 120,
.const (59773071600/3733 : ℚ),
.mul 122 121,
.add 116 123,
.mul 80 80,
.mul 118 125,
.const (75712557360/3733 : ℚ),
.mul 127 126,
.add 124 128,
.mul 6 18,
.mul 8 125,
.mul 130 131,
.const (85176627030/3733 : ℚ),
.mul 133 132,
.add 129 134,
.mul 85 85,
.mul 18 136,
.mul 133 137,
.add 135 138,
.mul 8 136,
.mul 41 140,
.mul 127 141,
.add 139 142,
.mul 95 95,
.mul 40 144,
.mul 122 145,
.add 143 146,
.mul 8 144,
.mul 65 148,
.mul 114 149,
.add 147 150,
.mul 100 100,
.mul 64 152,
.mul 109 153,
.add 151 154,
.mul 8 152,
.mul 92 156,
.mul 102 157,
.add 155 158,
.mul 107 107,
.mul 91 160,
.mul 97 161,
.add 159 162,
.mul 8 160,
.mul 117 164,
.mul 87 165,
.add 163 166,
.mul 112 112,
.mul 17 168,
.mul 82 169,
.add 167 170,
.mul 8 168,
.mul 39 172,
.mul 75 173,
.add 171 174,
.mul 120 120,
.mul 38 176,
.mul 70 177,
.add 175 178,
.mul 8 176,
.mul 90 180,
.mul 61 181,
.add 179 182,
.mul 125 125,
.mul 16 184,
.mul 56 185,
.add 183 186,
.mul 8 184,
.mul 37 188,
.mul 49 189,
.add 187 190,
.mul 131 131,
.mul 12 192,
.mul 45 193,
.add 191 194,
.mul 8 192,
.mul 6 196,
.const (2409/3733 : ℚ),
.mul 198 197,
.add 195 199,
.mul 136 136,
.const (73/3733 : ℚ),
.mul 202 201,
.add 200 203,
.neg 204,
.add 26 205,
.const (145513/100000 : ℚ),
.mul 207 206,
.add 6 208,
.const (-113609/200000 : ℚ),
.add 209 210]
private noncomputable def ssaQVals : Fin 30 → ℚ := ![(1/1 : ℚ),(49/100 : ℚ),(390189/5000000 : ℚ),(1085/4818 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ),(4818/3733 : ℚ),(627/3733 : ℚ),(1155/3733 : ℚ),(385/3733 : ℚ),(38544/3733 : ℚ),(398288/3733 : ℚ),(2987160/3733 : ℚ),(17325528/3733 : ℚ),(80852464/3733 : ℚ),(311859504/3733 : ℚ),(1013543388/3733 : ℚ),(2815398300/3733 : ℚ),(6756955920/3733 : ℚ),(14128180560/3733 : ℚ),(25901664360/3733 : ℚ),(41841150120/3733 : ℚ),(59773071600/3733 : ℚ),(75712557360/3733 : ℚ),(85176627030/3733 : ℚ),(2409/3733 : ℚ),(73/3733 : ℚ),(145513/100000 : ℚ),(-113609/200000 : ℚ)]
private theorem ssa_tape : MetricDistortion.OptimizedSSAFinite0.S_75ff2bbd7ad426c2.p212 ssaQVals = tape := by rfl
private noncomputable def computed (D : Int) (B : Fin 4 → FixedTape.I) : FixedTape.Row :=
  MetricDistortion.OptimizedSSAFinite0.S_75ff2bbd7ad426c2.computed ssaQVals D B
private theorem ssa_matches (D : Int) (B : Fin 4 → FixedTape.I) :
    (FixedTape.rowsAux D B [] tape).getD 211 FixedTape.zeroRow = computed D B := by
  rw [←ssa_tape]
  exact MetricDistortion.OptimizedSSAFinite0.S_75ff2bbd7ad426c2.ssa_matches ssaQVals D B

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
private noncomputable def denominator : Int := 5699862257390310338545674047597838336000000000
private theorem denominator_positive : 0 < denominator := by decide +kernel
private noncomputable def candidateRows (B : Fin 4 → FixedTape.I) : List TapeBounds :=
  (FixedTape.rowsAux denominator B [] tape).map (FixedTape.decodeRow denominator)
private theorem root_in_range : 211 < tape.length := by decide +kernel
private theorem references_valid : tapeRefsValidAux 0 tape = true := by decide +kernel
private theorem candidate_valid (h : Needs) (B : Fin 4 → FixedTape.I) :
    tapeCheck (FixedTape.decodeBox denominator B) tape (candidateRows B) = true :=
  h.child_10.1 denominator denominator_positive B tape references_valid
private theorem candidate_root (B : Fin 4 → FixedTape.I) :
    (candidateRows B).getD 211 zeroTapeBounds = FixedTape.decodeRow denominator (computed denominator B) := by
  unfold candidateRows
  rw [←decode_zeroRow denominator,List.getD_map,ssa_matches]
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨5642863634816407235160217307121859952640000000,5699862257390310338545674047597838336000000000⟩,⟨0,5699862257390310338545674047597838336000000000⟩,⟨0,5699862257390310338545674047597838336000000000⟩,⟨0,5699862257390310338545674047597838336000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := faceI ibox0 0 true
private noncomputable def ibox2 : Fin 4 → FixedTape.I := faceI ibox1 2 true
private noncomputable def ibox3 : Fin 4 → FixedTape.I := faceI ibox2 3 true
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 1 2849931128695155169272837023798919168000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox3 1 2849931128695155169272837023798919168000000000 true
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox5 1 4274896693042732753909255535698378752000000000 false
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox5 1 4274896693042732753909255535698378752000000000 true
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox7 1 4987379475216521546227464791648108544000000000 false
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox7 1 4987379475216521546227464791648108544000000000 true
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox9 1 5343620866303415942386569419622973440000000000 false
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox9 1 5343620866303415942386569419622973440000000000 true
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox11 1 5521741561846863140466121733610405888000000000 false
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox11 1 5521741561846863140466121733610405888000000000 true
private noncomputable def tree13 : TapeTree := .centered (candidateRows ibox13) (candidateRows (FixedTape.midBox ibox13))
attribute [irreducible] tree13
private theorem sign_13 : 2*denominator*(computed denominator (FixedTape.midBox ibox13)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox13).gradient k).lo.natAbs ((computed denominator ibox13).gradient k).hi.natAbs : Int)*((ibox13 k).hi-(ibox13 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox13
    (computed denominator ibox13) (computed denominator (FixedTape.midBox ibox13))
    (by decide +kernel)
private theorem midpoint_even_13 : ∀ k, 2 ∣ (ibox13 k).lo+(ibox13 k).hi := by decide +kernel
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 211 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox13 midpoint_even_13
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox13,candidate_valid h (FixedTape.midBox ibox13),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox13 211 (FixedTape.rowsAux denominator ibox13 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox13) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_13
private noncomputable def tree12 : TapeTree := .centered (candidateRows ibox12) (candidateRows (FixedTape.midBox ibox12))
attribute [irreducible] tree12
private theorem sign_12 : 2*denominator*(computed denominator (FixedTape.midBox ibox12)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox12).gradient k).lo.natAbs ((computed denominator ibox12).gradient k).hi.natAbs : Int)*((ibox12 k).hi-(ibox12 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox12
    (computed denominator ibox12) (computed denominator (FixedTape.midBox ibox12))
    (by decide +kernel)
private theorem midpoint_even_12 : ∀ k, 2 ∣ (ibox12 k).lo+(ibox12 k).hi := by decide +kernel
private theorem accepted_12 (h : Needs) : verifyTapeTree tape 211 (FixedTape.decodeBox denominator ibox12) tree12 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox12 midpoint_even_12
  simp only [tree12,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox12,candidate_valid h (FixedTape.midBox ibox12),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox12 211 (FixedTape.rowsAux denominator ibox12 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox12) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_12
private noncomputable def tree11 : TapeTree := .split 1 (((5521741561846863140466121733610405888000000000 : Int) : ℚ)/(denominator : ℚ)) tree12 tree13
attribute [irreducible] tree11
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 211 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox11 1 (5521741561846863140466121733610405888000000000 : Int) false,decode_split denominator ibox11 1 (5521741561846863140466121733610405888000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_12 h,accepted_13 h⟩
private noncomputable def tree10 : TapeTree := .centered (candidateRows ibox10) (candidateRows (FixedTape.midBox ibox10))
attribute [irreducible] tree10
private theorem sign_10 : 2*denominator*(computed denominator (FixedTape.midBox ibox10)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox10).gradient k).lo.natAbs ((computed denominator ibox10).gradient k).hi.natAbs : Int)*((ibox10 k).hi-(ibox10 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox10
    (computed denominator ibox10) (computed denominator (FixedTape.midBox ibox10))
    (by decide +kernel)
private theorem midpoint_even_10 : ∀ k, 2 ∣ (ibox10 k).lo+(ibox10 k).hi := by decide +kernel
private theorem accepted_10 (h : Needs) : verifyTapeTree tape 211 (FixedTape.decodeBox denominator ibox10) tree10 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox10 midpoint_even_10
  simp only [tree10,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox10,candidate_valid h (FixedTape.midBox ibox10),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox10 211 (FixedTape.rowsAux denominator ibox10 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox10) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_10
private noncomputable def tree9 : TapeTree := .split 1 (((5343620866303415942386569419622973440000000000 : Int) : ℚ)/(denominator : ℚ)) tree10 tree11
attribute [irreducible] tree9
private theorem accepted_9 (h : Needs) : verifyTapeTree tape 211 (FixedTape.decodeBox denominator ibox9) tree9 = true := by
  simp only [tree9,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox9 1 (5343620866303415942386569419622973440000000000 : Int) false,decode_split denominator ibox9 1 (5343620866303415942386569419622973440000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_10 h,accepted_11 h⟩
private noncomputable def tree8 : TapeTree := .centered (candidateRows ibox8) (candidateRows (FixedTape.midBox ibox8))
attribute [irreducible] tree8
private theorem sign_8 : 2*denominator*(computed denominator (FixedTape.midBox ibox8)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox8).gradient k).lo.natAbs ((computed denominator ibox8).gradient k).hi.natAbs : Int)*((ibox8 k).hi-(ibox8 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox8
    (computed denominator ibox8) (computed denominator (FixedTape.midBox ibox8))
    (by decide +kernel)
private theorem midpoint_even_8 : ∀ k, 2 ∣ (ibox8 k).lo+(ibox8 k).hi := by decide +kernel
private theorem accepted_8 (h : Needs) : verifyTapeTree tape 211 (FixedTape.decodeBox denominator ibox8) tree8 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox8 midpoint_even_8
  simp only [tree8,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox8,candidate_valid h (FixedTape.midBox ibox8),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox8 211 (FixedTape.rowsAux denominator ibox8 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox8) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_8
private noncomputable def tree7 : TapeTree := .split 1 (((4987379475216521546227464791648108544000000000 : Int) : ℚ)/(denominator : ℚ)) tree8 tree9
attribute [irreducible] tree7
private theorem accepted_7 (h : Needs) : verifyTapeTree tape 211 (FixedTape.decodeBox denominator ibox7) tree7 = true := by
  simp only [tree7,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox7 1 (4987379475216521546227464791648108544000000000 : Int) false,decode_split denominator ibox7 1 (4987379475216521546227464791648108544000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_8 h,accepted_9 h⟩
private noncomputable def tree6 : TapeTree := .centered (candidateRows ibox6) (candidateRows (FixedTape.midBox ibox6))
attribute [irreducible] tree6
private theorem sign_6 : 2*denominator*(computed denominator (FixedTape.midBox ibox6)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox6).gradient k).lo.natAbs ((computed denominator ibox6).gradient k).hi.natAbs : Int)*((ibox6 k).hi-(ibox6 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox6
    (computed denominator ibox6) (computed denominator (FixedTape.midBox ibox6))
    (by decide +kernel)
private theorem midpoint_even_6 : ∀ k, 2 ∣ (ibox6 k).lo+(ibox6 k).hi := by decide +kernel
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 211 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox6 midpoint_even_6
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox6,candidate_valid h (FixedTape.midBox ibox6),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox6 211 (FixedTape.rowsAux denominator ibox6 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox6) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_6
private noncomputable def tree5 : TapeTree := .split 1 (((4274896693042732753909255535698378752000000000 : Int) : ℚ)/(denominator : ℚ)) tree6 tree7
attribute [irreducible] tree5
private theorem accepted_5 (h : Needs) : verifyTapeTree tape 211 (FixedTape.decodeBox denominator ibox5) tree5 = true := by
  simp only [tree5,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox5 1 (4274896693042732753909255535698378752000000000 : Int) false,decode_split denominator ibox5 1 (4274896693042732753909255535698378752000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_6 h,accepted_7 h⟩
private noncomputable def tree4 : TapeTree := .centered (candidateRows ibox4) (candidateRows (FixedTape.midBox ibox4))
attribute [irreducible] tree4
private theorem sign_4 : 2*denominator*(computed denominator (FixedTape.midBox ibox4)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox4).gradient k).lo.natAbs ((computed denominator ibox4).gradient k).hi.natAbs : Int)*((ibox4 k).hi-(ibox4 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox4
    (computed denominator ibox4) (computed denominator (FixedTape.midBox ibox4))
    (by decide +kernel)
private theorem midpoint_even_4 : ∀ k, 2 ∣ (ibox4 k).lo+(ibox4 k).hi := by decide +kernel
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 211 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox4 midpoint_even_4
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox4,candidate_valid h (FixedTape.midBox ibox4),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox4 211 (FixedTape.rowsAux denominator ibox4 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox4) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_4
private noncomputable def tree3 : TapeTree := .split 1 (((2849931128695155169272837023798919168000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree5
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 211 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 1 (2849931128695155169272837023798919168000000000 : Int) false,decode_split denominator ibox3 1 (2849931128695155169272837023798919168000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_5 h⟩
private noncomputable def tree2 : TapeTree := .face 3 true (candidateRows ibox2) tree3
attribute [irreducible] tree2
private theorem sign_2 : 0 ≤ ((computed denominator ibox2).gradient 3).lo := by decide +kernel
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 211 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox2,?_,accepted_3 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox2)).gradient 3).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox2).gradient 3).lo) denominator_positive).2 sign_2
private noncomputable def tree1 : TapeTree := .face 2 true (candidateRows ibox1) tree2
attribute [irreducible] tree1
private theorem sign_1 : 0 ≤ ((computed denominator ibox1).gradient 2).lo := by decide +kernel
private theorem accepted_1 (h : Needs) : verifyTapeTree tape 211 (FixedTape.decodeBox denominator ibox1) tree1 = true := by
  simp only [tree1,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox1,?_,accepted_2 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox1)).gradient 2).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox1).gradient 2).lo) denominator_positive).2 sign_1
private noncomputable def tree0 : TapeTree := .face 0 true (candidateRows ibox0) tree1
attribute [irreducible] tree0
private theorem sign_0 : 0 ≤ ((computed denominator ibox0).gradient 0).lo := by decide +kernel
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 211 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
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
private theorem same_expression : tapeExpr tape 211 = e234 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (99/100 : ℚ) (1/1 : ℚ)) x → eval e234 x ≤ 0 := by
  have hb := h.child_4 tape 211 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell127_low_first_top

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell127_low_first_top
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((99/100 : ℚ) : ℝ) < p ∧ p ≤ ((1/1 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 127 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 127 p)
    (hk0 : ((1/1 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((99/100 : ℚ) : ℝ))
    (hk1 : ((1/1 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((99/100 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : ((49/100 : ℚ) : ℝ) < a), firstResidual (0 : Fin 9) a p r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell127_low_first_top.cell_bound h.child_8 h.child_9 (Cell127_low_first_top.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell127_low_first_top
