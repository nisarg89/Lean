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
namespace Cell75_low_first_top
private noncomputable def qValues : Fin 4 → ℚ := ![(409328352489947143769368016179674106/508003913094906734051026794427946085 : ℚ),(1180579358712720771539875000000000000/914407043570832121291848229970302953 : ℚ),(5366844543256561053689211576587611333/1968765103970904843722651715757989186 : ℚ),(-15069019430257197580692500000000000000/8859442967869071796751932720910951337 : ℚ)]
private noncomputable abbrev e2 : PolyExpr := SharedFiniteSemantics17.e2 qValues
private noncomputable abbrev e10 : PolyExpr := SharedFiniteSemantics17.e10 qValues
private noncomputable abbrev e15 : PolyExpr := SharedFiniteSemantics17.e15 qValues
private noncomputable abbrev e19 : PolyExpr := SharedFiniteSemantics17.e19 qValues
private noncomputable abbrev e98 : PolyExpr := SharedFiniteSemantics17.e98 qValues
private noncomputable abbrev node_1 := SharedFiniteSemantics17.node_1 qValues
private noncomputable abbrev node_2 := SharedFiniteSemantics17.node_2 qValues
private noncomputable abbrev node_3 := SharedFiniteSemantics17.node_3 qValues
private noncomputable abbrev node_4 := SharedFiniteSemantics17.node_4 qValues
private noncomputable abbrev node_6 := SharedFiniteSemantics17.node_6 qValues
private noncomputable abbrev node_7 := SharedFiniteSemantics17.node_7 qValues
private noncomputable abbrev node_8 := SharedFiniteSemantics17.node_8 qValues
private noncomputable abbrev node_9 := SharedFiniteSemantics17.node_9 qValues
private noncomputable abbrev node_10 := SharedFiniteSemantics17.node_10 qValues
private noncomputable abbrev node_11 := SharedFiniteSemantics17.node_11 qValues
private noncomputable abbrev node_12 := SharedFiniteSemantics17.node_12 qValues
private noncomputable abbrev node_13 := SharedFiniteSemantics17.node_13 qValues
private noncomputable abbrev node_14 := SharedFiniteSemantics17.node_14 qValues
private noncomputable abbrev node_15 := SharedFiniteSemantics17.node_15 qValues
private noncomputable abbrev node_17 := SharedFiniteSemantics17.node_17 qValues
private noncomputable abbrev node_18 := SharedFiniteSemantics17.node_18 qValues
private noncomputable abbrev node_19 := SharedFiniteSemantics17.node_19 qValues
private noncomputable abbrev node_57 := SharedFiniteSemantics17.node_57 qValues
private noncomputable abbrev node_58 := SharedFiniteSemantics17.node_58 qValues
private noncomputable abbrev node_59 := SharedFiniteSemantics17.node_59 qValues
private noncomputable abbrev node_60 := SharedFiniteSemantics17.node_60 qValues
private noncomputable abbrev node_61 := SharedFiniteSemantics17.node_61 qValues
private noncomputable abbrev node_62 := SharedFiniteSemantics17.node_62 qValues
private noncomputable abbrev node_63 := SharedFiniteSemantics17.node_63 qValues
private noncomputable abbrev node_64 := SharedFiniteSemantics17.node_64 qValues
private noncomputable abbrev node_65 := SharedFiniteSemantics17.node_65 qValues
private noncomputable abbrev node_66 := SharedFiniteSemantics17.node_66 qValues
private noncomputable abbrev node_67 := SharedFiniteSemantics17.node_67 qValues
private noncomputable abbrev node_69 := SharedFiniteSemantics17.node_69 qValues
private noncomputable abbrev node_70 := SharedFiniteSemantics17.node_70 qValues
private noncomputable abbrev node_71 := SharedFiniteSemantics17.node_71 qValues
private noncomputable abbrev node_76 := SharedFiniteSemantics17.node_76 qValues
private noncomputable abbrev node_77 := SharedFiniteSemantics17.node_77 qValues
private noncomputable abbrev node_78 := SharedFiniteSemantics17.node_78 qValues
private noncomputable abbrev node_79 := SharedFiniteSemantics17.node_79 qValues
private noncomputable abbrev node_80 := SharedFiniteSemantics17.node_80 qValues
private noncomputable abbrev node_97 := SharedFiniteSemantics17.node_97 qValues
private noncomputable abbrev node_98 := SharedFiniteSemantics17.node_98 qValues
private noncomputable abbrev semantic_H_40 := SharedFiniteSemantics17.semantic_H_40 qValues
private noncomputable abbrev semantic_H_56 := SharedFiniteSemantics17.semantic_H_56 qValues
private noncomputable abbrev semantic_psi_96 := SharedFiniteSemantics17.semantic_psi_96 qValues
private noncomputable def aPoint (x : Fin 4 → ℝ) : ℝ := ((49/100 : ℚ) : ℝ)+(x 0-((49/100 : ℚ) : ℝ))*x 1
private noncomputable def rPoint (x : Fin 4 → ℝ) : ℝ := aPoint x+(((2840189/5000000 : ℚ) : ℝ)-aPoint x)*x 2
private noncomputable def yPoint (x : Fin 4 → ℝ) : ℝ := aPoint x+1-x 0
private theorem point_10 (x : Fin 4 → ℝ) : eval e10 x = aPoint x := by
  simp only [node_2,node_3,node_6,node_7,node_8,node_9,node_10] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_15 (x : Fin 4 → ℝ) : eval e15 x = rPoint x := by
  simp only [node_2,node_3,node_4,node_6,node_7,node_8,node_9,node_10,node_11,node_12,node_13,node_14,node_15] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_2 (x : Fin 4 → ℝ) : eval e2 x = x 0 := by
  simp only [node_2] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem point_19 (x : Fin 4 → ℝ) : eval e19 x = yPoint x := by
  simp only [node_1,node_2,node_3,node_6,node_7,node_8,node_9,node_10,node_17,node_18,node_19] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem price_lambda_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceLambda 75 p = ((409328352489947143769368016179674106/508003913094906734051026794427946085 : ℝ)+(1180579358712720771539875000000000000/914407043570832121291848229970302953 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell75,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 75 p = (((5366844543256561053689211576587611333/1968765103970904843722651715757989186 : ℝ)+(-15069019430257197580692500000000000000/8859442967869071796751932720910951337 : ℝ)*p)-(145513/100000 : ℝ)*(1/1 : ℝ))/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell75,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e98 x = (x 0*(1-x 0))*(aPoint x+priceLambda 75 (x 0)*(HStar (yPoint x)-HStar (aPoint x))+priceTau 75 (x 0)*psiStar (rPoint x)+(0)-(cStar)) := by
  have hp0 : x 0 ≠ 0 := ne_of_gt hp.1
  have hp1 : x 0 ≠ 1 := ne_of_lt hp.2
  have heps : 1-x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  rw [price_lambda_normal _ hp,price_tau_normal _ hp]
  simp only [node_1,node_17,node_18,node_57,node_58,node_59,node_60,node_61,node_62,node_63,node_64,node_65,node_66,node_67,node_69,node_70,node_71,node_76,node_77,node_78,node_79,node_80,node_97,node_98,semantic_H_40,semantic_H_56,semantic_psi_96,point_10,point_15,point_2,point_19]
  norm_num [qValues,eta,etas,Fin.val_zero,sourceDenom,muStar,cStar] at *
  generalize HStar (yPoint x) = z0 at *
  generalize HStar (aPoint x) = z1 at *
  generalize psiStar (aPoint x) = z2 at *
  generalize psiStar (rPoint x) = z3 at *
  generalize sourceF0 (aPoint x) = z4 at *
  generalize sourceInc (aPoint x) (1-x 0) = z5 at *
  generalize sourceInc (aPoint x) ((1-x 0)*x 2) = z6 at *
  generalize sourcePD (aPoint x) (rPoint x) (rPoint x-aPoint x) = z7 at *
  field_simp [hp0,heps] <;> ring
theorem actual_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) (ha : aPoint x ≤ bStar)
    (hL : lambdaStar (x 0) = priceLambda 75 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 75 (x 0)) :
    (1)*eval e98 x = (x 0*(1-x 0))*(firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (2760416666666667/5000000000000000 : ℚ) (9/16 : ℚ)) x → eval e98 x ≤ 0)
    (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((2760416666666667/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((9/16 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 75 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 75 p)
    (hk0 : ((9/16 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((2760416666666667/5000000000000000 : ℚ) : ℝ))
    (hk1 : ((9/16 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((2760416666666667/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : ((49/100 : ℚ) : ℝ) < a) :
    firstResidual (0 : Fin 9) a p r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxr⟩ := h2 (2760416666666667/5000000000000000 : ℚ) (9/16 : ℚ) ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ) p a r hpcell hk0 hk1 hr hap hcase
  have hcut : ((9/16 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) := by norm_num [bStar]
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,if_pos hcut] using hxa
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,if_pos hcut] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 75 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 75 (x 0) := by simpa only [hxp] using hT
  have hrootb : ((2840189/5000000 : ℚ) : ℝ) ≤ bStar := by norm_num [bStar]
  have hflag : aPoint x ≤ bStar := by rw [hax]; exact (hap.trans (min_le_right _ _)).trans (hr.2.trans hrootb)
  have hb := hbound x hx
  have hv : (1 : ℝ)*eval e98 x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 1) hb
  rw [actual_identity hs x hpx hflag hLx hTx] at hv
  have hscale : 0 < x 0*(1-x 0) := mul_pos hpx.1 (sub_pos.mpr hpx.2)
  have hv : firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x) ≤ 0 := le_of_not_gt (fun hpos => (not_lt_of_ge hv) (mul_pos hscale hpos))
  simpa only [hxp,hax,hrx] using hv
private noncomputable def tape : List TapeOp := [
.const (1/1 : ℚ),
.var 0,
.var 1,
.var 2,
.const (49/100 : ℚ),
.const (-49/100 : ℚ),
.add 1 5,
.mul 6 2,
.add 4 7,
.const (2840189/5000000 : ℚ),
.neg 8,
.add 9 10,
.mul 11 3,
.add 8 12,
.neg 1,
.add 0 14,
.add 8 15,
.const (1085/4818 : ℚ),
.mul 17 16,
.mul 16 16,
.const (19/146 : ℚ),
.mul 20 19,
.mul 16 19,
.const (35/438 : ℚ),
.mul 23 22,
.add 21 24,
.mul 19 19,
.mul 26 26,
.mul 27 27,
.mul 28 28,
.mul 16 29,
.const (1/66 : ℚ),
.mul 31 30,
.add 25 32,
.neg 33,
.add 18 34,
.const (4818/3733 : ℚ),
.mul 36 35,
.mul 17 8,
.mul 8 8,
.mul 20 39,
.mul 8 39,
.mul 23 41,
.add 40 42,
.mul 39 39,
.mul 44 44,
.mul 45 45,
.mul 46 46,
.mul 8 47,
.mul 31 48,
.add 43 49,
.neg 50,
.add 38 51,
.mul 36 52,
.neg 53,
.add 37 54,
.const (409328352489947143769368016179674106/508003913094906734051026794427946085 : ℚ),
.const (1180579358712720771539875000000000000/914407043570832121291848229970302953 : ℚ),
.mul 57 1,
.add 56 58,
.const (5366844543256561053689211576587611333/1968765103970904843722651715757989186 : ℚ),
.const (-15069019430257197580692500000000000000/8859442967869071796751932720910951337 : ℚ),
.mul 61 1,
.add 60 62,
.mul 1 15,
.const (-145513/100000 : ℚ),
.add 63 65,
.mul 66 64,
.const (-113609/200000 : ℚ),
.add 8 68,
.mul 69 64,
.mul 59 55,
.add 70 71,
.const (19/73 : ℚ),
.mul 73 13,
.mul 13 13,
.const (35/146 : ℚ),
.mul 76 75,
.add 74 77,
.mul 75 75,
.mul 79 79,
.mul 80 80,
.mul 81 81,
.const (1/2 : ℚ),
.mul 83 82,
.add 78 84,
.neg 85,
.add 17 86,
.mul 36 87,
.mul 67 88,
.add 72 89]
private noncomputable def ssaQVals : Fin 18 → ℚ := ![(1/1 : ℚ),(49/100 : ℚ),(-49/100 : ℚ),(2840189/5000000 : ℚ),(1085/4818 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(4818/3733 : ℚ),(409328352489947143769368016179674106/508003913094906734051026794427946085 : ℚ),(1180579358712720771539875000000000000/914407043570832121291848229970302953 : ℚ),(5366844543256561053689211576587611333/1968765103970904843722651715757989186 : ℚ),(-15069019430257197580692500000000000000/8859442967869071796751932720910951337 : ℚ),(-145513/100000 : ℚ),(-113609/200000 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ)]
private theorem ssa_tape : MetricDistortion.OptimizedSSAFinite0.S_e1eab25161459de6.p91 ssaQVals = tape := by rfl
private noncomputable def computed (D : Int) (B : Fin 4 → FixedTape.I) : FixedTape.Row :=
  MetricDistortion.OptimizedSSAFinite0.S_e1eab25161459de6.computed ssaQVals D B
private theorem ssa_matches (D : Int) (B : Fin 4 → FixedTape.I) :
    (FixedTape.rowsAux D B [] tape).getD 90 FixedTape.zeroRow = computed D B := by
  rw [←ssa_tape]
  exact MetricDistortion.OptimizedSSAFinite0.S_e1eab25161459de6.ssa_matches ssaQVals D B

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
private noncomputable def denominator : Int := 1847014612970503242596880529233575075795132097671154255900839454316096788890271341340413814374400000000000000000000000
private theorem denominator_positive : 0 < denominator := by decide +kernel
private noncomputable def candidateRows (B : Fin 4 → FixedTape.I) : List TapeBounds :=
  (FixedTape.rowsAux denominator B [] tape).map (FixedTape.decodeRow denominator)
private theorem root_in_range : 90 < tape.length := by decide +kernel
private theorem references_valid : tapeRefsValidAux 0 tape = true := by decide +kernel
private theorem candidate_valid (h : Needs) (B : Fin 4 → FixedTape.I) :
    tapeCheck (FixedTape.decodeBox denominator B) tape (candidateRows B) = true :=
  h.child_10.1 denominator denominator_positive B tape references_valid
private theorem candidate_root (B : Fin 4 → FixedTape.I) :
    (candidateRows B).getD 90 zeroTapeBounds = FixedTape.decodeRow denominator (computed denominator B) := by
  unfold candidateRows
  rw [←decode_zeroRow denominator,List.getD_map,ssa_matches]
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨1019705984244132121651335323547919079553931127827621465120728293480628828922467590771472719370622756027587624960000000,1038945719795908073960745297693885980134761804940024268944222193052804443750777629503982770585600000000000000000000000⟩,⟨0,1847014612970503242596880529233575075795132097671154255900839454316096788890271341340413814374400000000000000000000000⟩,⟨0,1847014612970503242596880529233575075795132097671154255900839454316096788890271341340413814374400000000000000000000000⟩,⟨0,1847014612970503242596880529233575075795132097671154255900839454316096788890271341340413814374400000000000000000000000⟩]
private noncomputable def tree0 : TapeTree := .direct (candidateRows ibox0)
attribute [irreducible] tree0
private theorem sign_0 : (computed denominator ibox0).value.hi ≤ 0 := by decide +kernel
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 90 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  refine ⟨root_in_range,candidate_valid h ibox0,?_⟩
  rw [candidate_root]
  simpa [FixedTape.decodeRow,FixedTape.decode] using (h.child_10.2.2.2.1 denominator (computed denominator ibox0).value.hi denominator_positive).1 sign_0
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (2760416666666667/5000000000000000 : ℚ) (9/16 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 90 = e98 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (2760416666666667/5000000000000000 : ℚ) (9/16 : ℚ)) x → eval e98 x ≤ 0 := by
  have hb := h.child_4 tape 90 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell75_low_first_top

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell75_low_first_top
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((2760416666666667/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((9/16 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 75 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 75 p)
    (hk0 : ((9/16 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((2760416666666667/5000000000000000 : ℚ) : ℝ))
    (hk1 : ((9/16 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((2760416666666667/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : ((49/100 : ℚ) : ℝ) < a), firstResidual (0 : Fin 9) a p r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell75_low_first_top.cell_bound h.child_8 h.child_9 (Cell75_low_first_top.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell75_low_first_top
