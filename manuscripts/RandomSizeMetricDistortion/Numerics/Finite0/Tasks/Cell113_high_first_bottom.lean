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
namespace Cell113_high_first_bottom
private noncomputable def qValues : Fin 2 → ℚ := ![(17467061935620057123461209407557589004/5540942664688768372373977241655459795 : ℚ),(-1815615940977725473987000000000000000/1108188532937753674474795448331091959 : ℚ)]
private noncomputable abbrev e2 : PolyExpr := SharedFiniteSemantics25.e2 qValues
private noncomputable abbrev e7 : PolyExpr := SharedFiniteSemantics25.e7 qValues
private noncomputable abbrev e11 : PolyExpr := SharedFiniteSemantics25.e11 qValues
private noncomputable abbrev e15 : PolyExpr := SharedFiniteSemantics25.e15 qValues
private noncomputable abbrev e70 : PolyExpr := SharedFiniteSemantics25.e70 qValues
private noncomputable abbrev node_1 := SharedFiniteSemantics25.node_1 qValues
private noncomputable abbrev node_2 := SharedFiniteSemantics25.node_2 qValues
private noncomputable abbrev node_3 := SharedFiniteSemantics25.node_3 qValues
private noncomputable abbrev node_4 := SharedFiniteSemantics25.node_4 qValues
private noncomputable abbrev node_6 := SharedFiniteSemantics25.node_6 qValues
private noncomputable abbrev node_7 := SharedFiniteSemantics25.node_7 qValues
private noncomputable abbrev node_9 := SharedFiniteSemantics25.node_9 qValues
private noncomputable abbrev node_10 := SharedFiniteSemantics25.node_10 qValues
private noncomputable abbrev node_11 := SharedFiniteSemantics25.node_11 qValues
private noncomputable abbrev node_13 := SharedFiniteSemantics25.node_13 qValues
private noncomputable abbrev node_14 := SharedFiniteSemantics25.node_14 qValues
private noncomputable abbrev node_15 := SharedFiniteSemantics25.node_15 qValues
private noncomputable abbrev node_53 := SharedFiniteSemantics25.node_53 qValues
private noncomputable abbrev node_54 := SharedFiniteSemantics25.node_54 qValues
private noncomputable abbrev node_55 := SharedFiniteSemantics25.node_55 qValues
private noncomputable abbrev node_56 := SharedFiniteSemantics25.node_56 qValues
private noncomputable abbrev node_57 := SharedFiniteSemantics25.node_57 qValues
private noncomputable abbrev node_58 := SharedFiniteSemantics25.node_58 qValues
private noncomputable abbrev node_60 := SharedFiniteSemantics25.node_60 qValues
private noncomputable abbrev node_66 := SharedFiniteSemantics25.node_66 qValues
private noncomputable abbrev node_67 := SharedFiniteSemantics25.node_67 qValues
private noncomputable abbrev node_68 := SharedFiniteSemantics25.node_68 qValues
private noncomputable abbrev node_69 := SharedFiniteSemantics25.node_69 qValues
private noncomputable abbrev node_70 := SharedFiniteSemantics25.node_70 qValues
private noncomputable abbrev semantic_H_36 := SharedFiniteSemantics25.semantic_H_36 qValues
private noncomputable abbrev semantic_H_52 := SharedFiniteSemantics25.semantic_H_52 qValues
private noncomputable abbrev semantic_psi_86 := SharedFiniteSemantics25.semantic_psi_86 qValues
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
private theorem point_15 (x : Fin 4 → ℝ) : eval e15 x = yPoint x := by
  simp only [node_1,node_2,node_3,node_6,node_7,node_13,node_14,node_15] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem price_lambda_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceLambda 113 p = ((17467061935620057123461209407557589004/5540942664688768372373977241655459795 : ℝ)+(-1815615940977725473987000000000000000/1108188532937753674474795448331091959 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell113,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 113 p = 0 := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell113,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e70 x = (x 0*(1-x 0))*(aPoint x+priceLambda 113 (x 0)*(HStar (yPoint x)-HStar (aPoint x))+priceTau 113 (x 0)*psiStar (rPoint x)+(0)-(cStar)) := by
  have hp0 : x 0 ≠ 0 := ne_of_gt hp.1
  have hp1 : x 0 ≠ 1 := ne_of_lt hp.2
  have heps : 1-x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  rw [price_lambda_normal _ hp,price_tau_normal _ hp]
  simp only [node_1,node_13,node_14,node_53,node_54,node_55,node_56,node_57,node_58,node_60,node_66,node_67,node_68,node_69,node_70,semantic_H_36,semantic_H_52,semantic_psi_86,point_7,point_11,point_2,point_15]
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
    (hL : lambdaStar (x 0) = priceLambda 113 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 113 (x 0)) :
    (1)*eval e70 x = (x 0*(1-x 0))*(firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (4322916666666667/5000000000000000 : ℚ) (7/8 : ℚ)) x → eval e70 x ≤ 0)
    (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((4322916666666667/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((7/8 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 113 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 113 p)
    (hkb : ((7/8 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((4322916666666667/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : a ≤ bStar) :
    firstResidual (0 : Fin 9) a p r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨x,hx,hxp,hxa,hxr⟩ := h4 (4322916666666667/5000000000000000 : ℚ) (7/8 : ℚ) bStar p a r hpcell hkb hr ha hap hcase
  have hcut : ¬(((7/8 : ℚ) : ℝ) ≤ bStar) := by norm_num [bStar]
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,if_neg hcut] using hxa
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,if_neg hcut] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 113 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 113 (x 0) := by simpa only [hxp] using hT
  have hflag : aPoint x ≤ bStar := by simpa only [hax] using hcase
  have hb := hbound x hx
  have hv : (1 : ℝ)*eval e70 x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 1) hb
  rw [actual_identity hs x hpx hflag hLx hTx] at hv
  have hscale : 0 < x 0*(1-x 0) := mul_pos hpx.1 (sub_pos.mpr hpx.2)
  have hv : firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x) ≤ 0 := le_of_not_gt (fun hpos => (not_lt_of_ge hv) (mul_pos hscale hpos))
  simpa only [hxp,hax,hrx] using hv
private noncomputable def tape : List TapeOp := [
.const (1/1 : ℚ),
.var 0,
.var 1,
.const (2840189/5000000 : ℚ),
.mul 3 2,
.neg 1,
.add 0 5,
.add 4 6,
.const (1085/4818 : ℚ),
.mul 8 7,
.mul 7 7,
.const (19/146 : ℚ),
.mul 11 10,
.mul 7 10,
.const (35/438 : ℚ),
.mul 14 13,
.add 12 15,
.mul 10 10,
.mul 17 17,
.mul 18 18,
.mul 19 19,
.mul 7 20,
.const (1/66 : ℚ),
.mul 22 21,
.add 16 23,
.neg 24,
.add 9 25,
.const (4818/3733 : ℚ),
.mul 27 26,
.mul 8 4,
.mul 4 4,
.mul 11 30,
.mul 4 30,
.mul 14 32,
.add 31 33,
.mul 30 30,
.mul 35 35,
.mul 36 36,
.mul 37 37,
.mul 4 38,
.mul 22 39,
.add 34 40,
.neg 41,
.add 29 42,
.mul 27 43,
.neg 44,
.add 28 45,
.const (17467061935620057123461209407557589004/5540942664688768372373977241655459795 : ℚ),
.const (-1815615940977725473987000000000000000/1108188532937753674474795448331091959 : ℚ),
.mul 48 1,
.add 47 49,
.mul 1 6,
.const (-113609/200000 : ℚ),
.add 4 52,
.mul 53 51,
.mul 50 46,
.add 54 55]
private noncomputable def ssaQVals : Fin 10 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(1085/4818 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(4818/3733 : ℚ),(17467061935620057123461209407557589004/5540942664688768372373977241655459795 : ℚ),(-1815615940977725473987000000000000000/1108188532937753674474795448331091959 : ℚ),(-113609/200000 : ℚ)]
private theorem ssa_tape : MetricDistortion.OptimizedSSAFinite0.S_75f0087db2b0bd70.p57 ssaQVals = tape := by rfl
private noncomputable def computed (D : Int) (B : Fin 4 → FixedTape.I) : FixedTape.Row :=
  MetricDistortion.OptimizedSSAFinite0.S_75f0087db2b0bd70.computed ssaQVals D B
private theorem ssa_matches (D : Int) (B : Fin 4 → FixedTape.I) :
    (FixedTape.rowsAux D B [] tape).getD 56 FixedTape.zeroRow = computed D B := by
  rw [←ssa_tape]
  exact MetricDistortion.OptimizedSSAFinite0.S_75f0087db2b0bd70.ssa_matches ssaQVals D B

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
private noncomputable def denominator : Int := 26318841637352670587355497356885160482353464923084482799863841945131417600000000000000000000000
private theorem denominator_positive : 0 < denominator := by decide +kernel
private noncomputable def candidateRows (B : Fin 4 → FixedTape.I) : List TapeBounds :=
  (FixedTape.rowsAux denominator B [] tape).map (FixedTape.decodeRow denominator)
private theorem root_in_range : 56 < tape.length := by decide +kernel
private theorem references_valid : tapeRefsValidAux 0 tape = true := by decide +kernel
private theorem candidate_valid (h : Needs) (B : Fin 4 → FixedTape.I) :
    tapeCheck (FixedTape.decodeBox denominator B) tape (candidateRows B) = true :=
  h.child_10.1 denominator denominator_positive B tape references_valid
private theorem candidate_root (B : Fin 4 → FixedTape.I) :
    (candidateRows B).getD 56 zeroTapeBounds = FixedTape.decodeRow denominator (computed denominator B) := by
  unfold candidateRows
  rw [←decode_zeroRow denominator,List.getD_map,ssa_matches]
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨22754831832294498199907216246651667490734590340427491244279941554027058124256129675427840000000,23028986432683586763936060187274515422059281807698922449880861701989990400000000000000000000000⟩,⟨0,26318841637352670587355497356885160482353464923084482799863841945131417600000000000000000000000⟩,⟨0,26318841637352670587355497356885160482353464923084482799863841945131417600000000000000000000000⟩,⟨0,26318841637352670587355497356885160482353464923084482799863841945131417600000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := faceI ibox0 2 true
private noncomputable def ibox2 : Fin 4 → FixedTape.I := faceI ibox1 3 true
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 1 13159420818676335293677748678442580241176732461542241399931920972565708800000000000000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 1 6579710409338167646838874339221290120588366230771120699965960486282854400000000000000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox4 1 3289855204669083823419437169610645060294183115385560349982980243141427200000000000000000000000 false
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox5 1 1644927602334541911709718584805322530147091557692780174991490121570713600000000000000000000000 false
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox5 1 1644927602334541911709718584805322530147091557692780174991490121570713600000000000000000000000 true
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox4 1 3289855204669083823419437169610645060294183115385560349982980243141427200000000000000000000000 true
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox8 1 4934782807003625735129155754415967590441274673078340524974470364712140800000000000000000000000 false
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox8 1 4934782807003625735129155754415967590441274673078340524974470364712140800000000000000000000000 true
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox3 1 6579710409338167646838874339221290120588366230771120699965960486282854400000000000000000000000 true
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox11 1 9869565614007251470258311508831935180882549346156681049948940729424281600000000000000000000000 false
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox12 1 8224638011672709558548592924026612650735457788463900874957450607853568000000000000000000000000 false
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox12 1 8224638011672709558548592924026612650735457788463900874957450607853568000000000000000000000000 true
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox11 1 9869565614007251470258311508831935180882549346156681049948940729424281600000000000000000000000 true
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox15 1 11514493216341793381968030093637257711029640903849461224940430850994995200000000000000000000000 false
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox15 1 11514493216341793381968030093637257711029640903849461224940430850994995200000000000000000000000 true
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox2 1 13159420818676335293677748678442580241176732461542241399931920972565708800000000000000000000000 true
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox18 1 19739131228014502940516623017663870361765098692313362099897881458848563200000000000000000000000 false
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox19 1 16449276023345419117097185848053225301470915576927801749914901215707136000000000000000000000000 false
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox20 1 14804348421010877205387467263247902771323824019235021574923411094136422400000000000000000000000 false
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox20 1 14804348421010877205387467263247902771323824019235021574923411094136422400000000000000000000000 true
private noncomputable def ibox23 : Fin 4 → FixedTape.I := splitI ibox19 1 16449276023345419117097185848053225301470915576927801749914901215707136000000000000000000000000 true
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox23 1 18094203625679961028806904432858547831618007134620581924906391337277849600000000000000000000000 false
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox23 1 18094203625679961028806904432858547831618007134620581924906391337277849600000000000000000000000 true
private noncomputable def ibox26 : Fin 4 → FixedTape.I := splitI ibox18 1 19739131228014502940516623017663870361765098692313362099897881458848563200000000000000000000000 true
private noncomputable def ibox27 : Fin 4 → FixedTape.I := splitI ibox26 1 23028986432683586763936060187274515422059281807698922449880861701989990400000000000000000000000 false
private noncomputable def ibox28 : Fin 4 → FixedTape.I := splitI ibox27 1 21384058830349044852226341602469192891912190250006142274889371580419276800000000000000000000000 false
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox27 1 21384058830349044852226341602469192891912190250006142274889371580419276800000000000000000000000 true
private noncomputable def ibox30 : Fin 4 → FixedTape.I := splitI ibox26 1 23028986432683586763936060187274515422059281807698922449880861701989990400000000000000000000000 true
private noncomputable def tree30 : TapeTree := .centered (candidateRows ibox30) (candidateRows (FixedTape.midBox ibox30))
attribute [irreducible] tree30
private theorem sign_30 : 2*denominator*(computed denominator (FixedTape.midBox ibox30)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox30).gradient k).lo.natAbs ((computed denominator ibox30).gradient k).hi.natAbs : Int)*((ibox30 k).hi-(ibox30 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox30
    (computed denominator ibox30) (computed denominator (FixedTape.midBox ibox30))
    (by decide +kernel)
private theorem midpoint_even_30 : ∀ k, 2 ∣ (ibox30 k).lo+(ibox30 k).hi := by decide +kernel
private theorem accepted_30 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox30) tree30 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox30 midpoint_even_30
  simp only [tree30,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox30,candidate_valid h (FixedTape.midBox ibox30),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox30 56 (FixedTape.rowsAux denominator ibox30 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox30) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_30
private noncomputable def tree29 : TapeTree := .centered (candidateRows ibox29) (candidateRows (FixedTape.midBox ibox29))
attribute [irreducible] tree29
private theorem sign_29 : 2*denominator*(computed denominator (FixedTape.midBox ibox29)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox29).gradient k).lo.natAbs ((computed denominator ibox29).gradient k).hi.natAbs : Int)*((ibox29 k).hi-(ibox29 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox29
    (computed denominator ibox29) (computed denominator (FixedTape.midBox ibox29))
    (by decide +kernel)
private theorem midpoint_even_29 : ∀ k, 2 ∣ (ibox29 k).lo+(ibox29 k).hi := by decide +kernel
private theorem accepted_29 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox29) tree29 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox29 midpoint_even_29
  simp only [tree29,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox29,candidate_valid h (FixedTape.midBox ibox29),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox29 56 (FixedTape.rowsAux denominator ibox29 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox29) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_29
private noncomputable def tree28 : TapeTree := .centered (candidateRows ibox28) (candidateRows (FixedTape.midBox ibox28))
attribute [irreducible] tree28
private theorem sign_28 : 2*denominator*(computed denominator (FixedTape.midBox ibox28)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox28).gradient k).lo.natAbs ((computed denominator ibox28).gradient k).hi.natAbs : Int)*((ibox28 k).hi-(ibox28 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox28
    (computed denominator ibox28) (computed denominator (FixedTape.midBox ibox28))
    (by decide +kernel)
private theorem midpoint_even_28 : ∀ k, 2 ∣ (ibox28 k).lo+(ibox28 k).hi := by decide +kernel
private theorem accepted_28 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox28) tree28 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox28 midpoint_even_28
  simp only [tree28,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox28,candidate_valid h (FixedTape.midBox ibox28),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox28 56 (FixedTape.rowsAux denominator ibox28 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox28) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_28
private noncomputable def tree27 : TapeTree := .split 1 (((21384058830349044852226341602469192891912190250006142274889371580419276800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree28 tree29
attribute [irreducible] tree27
private theorem accepted_27 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox27) tree27 = true := by
  simp only [tree27,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox27 1 (21384058830349044852226341602469192891912190250006142274889371580419276800000000000000000000000 : Int) false,decode_split denominator ibox27 1 (21384058830349044852226341602469192891912190250006142274889371580419276800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_28 h,accepted_29 h⟩
private noncomputable def tree26 : TapeTree := .split 1 (((23028986432683586763936060187274515422059281807698922449880861701989990400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree27 tree30
attribute [irreducible] tree26
private theorem accepted_26 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox26) tree26 = true := by
  simp only [tree26,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox26 1 (23028986432683586763936060187274515422059281807698922449880861701989990400000000000000000000000 : Int) false,decode_split denominator ibox26 1 (23028986432683586763936060187274515422059281807698922449880861701989990400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_27 h,accepted_30 h⟩
private noncomputable def tree25 : TapeTree := .centered (candidateRows ibox25) (candidateRows (FixedTape.midBox ibox25))
attribute [irreducible] tree25
private theorem sign_25 : 2*denominator*(computed denominator (FixedTape.midBox ibox25)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox25).gradient k).lo.natAbs ((computed denominator ibox25).gradient k).hi.natAbs : Int)*((ibox25 k).hi-(ibox25 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox25
    (computed denominator ibox25) (computed denominator (FixedTape.midBox ibox25))
    (by decide +kernel)
private theorem midpoint_even_25 : ∀ k, 2 ∣ (ibox25 k).lo+(ibox25 k).hi := by decide +kernel
private theorem accepted_25 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox25) tree25 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox25 midpoint_even_25
  simp only [tree25,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox25,candidate_valid h (FixedTape.midBox ibox25),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox25 56 (FixedTape.rowsAux denominator ibox25 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox25) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_25
private noncomputable def tree24 : TapeTree := .centered (candidateRows ibox24) (candidateRows (FixedTape.midBox ibox24))
attribute [irreducible] tree24
private theorem sign_24 : 2*denominator*(computed denominator (FixedTape.midBox ibox24)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox24).gradient k).lo.natAbs ((computed denominator ibox24).gradient k).hi.natAbs : Int)*((ibox24 k).hi-(ibox24 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox24
    (computed denominator ibox24) (computed denominator (FixedTape.midBox ibox24))
    (by decide +kernel)
private theorem midpoint_even_24 : ∀ k, 2 ∣ (ibox24 k).lo+(ibox24 k).hi := by decide +kernel
private theorem accepted_24 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox24) tree24 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox24 midpoint_even_24
  simp only [tree24,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox24,candidate_valid h (FixedTape.midBox ibox24),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox24 56 (FixedTape.rowsAux denominator ibox24 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox24) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_24
private noncomputable def tree23 : TapeTree := .split 1 (((18094203625679961028806904432858547831618007134620581924906391337277849600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree24 tree25
attribute [irreducible] tree23
private theorem accepted_23 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox23) tree23 = true := by
  simp only [tree23,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox23 1 (18094203625679961028806904432858547831618007134620581924906391337277849600000000000000000000000 : Int) false,decode_split denominator ibox23 1 (18094203625679961028806904432858547831618007134620581924906391337277849600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_24 h,accepted_25 h⟩
private noncomputable def tree22 : TapeTree := .centered (candidateRows ibox22) (candidateRows (FixedTape.midBox ibox22))
attribute [irreducible] tree22
private theorem sign_22 : 2*denominator*(computed denominator (FixedTape.midBox ibox22)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox22).gradient k).lo.natAbs ((computed denominator ibox22).gradient k).hi.natAbs : Int)*((ibox22 k).hi-(ibox22 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox22
    (computed denominator ibox22) (computed denominator (FixedTape.midBox ibox22))
    (by decide +kernel)
private theorem midpoint_even_22 : ∀ k, 2 ∣ (ibox22 k).lo+(ibox22 k).hi := by decide +kernel
private theorem accepted_22 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox22) tree22 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox22 midpoint_even_22
  simp only [tree22,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox22,candidate_valid h (FixedTape.midBox ibox22),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox22 56 (FixedTape.rowsAux denominator ibox22 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox22) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_22
private noncomputable def tree21 : TapeTree := .centered (candidateRows ibox21) (candidateRows (FixedTape.midBox ibox21))
attribute [irreducible] tree21
private theorem sign_21 : 2*denominator*(computed denominator (FixedTape.midBox ibox21)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox21).gradient k).lo.natAbs ((computed denominator ibox21).gradient k).hi.natAbs : Int)*((ibox21 k).hi-(ibox21 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox21
    (computed denominator ibox21) (computed denominator (FixedTape.midBox ibox21))
    (by decide +kernel)
private theorem midpoint_even_21 : ∀ k, 2 ∣ (ibox21 k).lo+(ibox21 k).hi := by decide +kernel
private theorem accepted_21 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox21) tree21 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox21 midpoint_even_21
  simp only [tree21,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox21,candidate_valid h (FixedTape.midBox ibox21),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox21 56 (FixedTape.rowsAux denominator ibox21 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox21) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_21
private noncomputable def tree20 : TapeTree := .split 1 (((14804348421010877205387467263247902771323824019235021574923411094136422400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree21 tree22
attribute [irreducible] tree20
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox20 1 (14804348421010877205387467263247902771323824019235021574923411094136422400000000000000000000000 : Int) false,decode_split denominator ibox20 1 (14804348421010877205387467263247902771323824019235021574923411094136422400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_21 h,accepted_22 h⟩
private noncomputable def tree19 : TapeTree := .split 1 (((16449276023345419117097185848053225301470915576927801749914901215707136000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree20 tree23
attribute [irreducible] tree19
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox19 1 (16449276023345419117097185848053225301470915576927801749914901215707136000000000000000000000000 : Int) false,decode_split denominator ibox19 1 (16449276023345419117097185848053225301470915576927801749914901215707136000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_20 h,accepted_23 h⟩
private noncomputable def tree18 : TapeTree := .split 1 (((19739131228014502940516623017663870361765098692313362099897881458848563200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree19 tree26
attribute [irreducible] tree18
private theorem accepted_18 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox18) tree18 = true := by
  simp only [tree18,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox18 1 (19739131228014502940516623017663870361765098692313362099897881458848563200000000000000000000000 : Int) false,decode_split denominator ibox18 1 (19739131228014502940516623017663870361765098692313362099897881458848563200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_19 h,accepted_26 h⟩
private noncomputable def tree17 : TapeTree := .centered (candidateRows ibox17) (candidateRows (FixedTape.midBox ibox17))
attribute [irreducible] tree17
private theorem sign_17 : 2*denominator*(computed denominator (FixedTape.midBox ibox17)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox17).gradient k).lo.natAbs ((computed denominator ibox17).gradient k).hi.natAbs : Int)*((ibox17 k).hi-(ibox17 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox17
    (computed denominator ibox17) (computed denominator (FixedTape.midBox ibox17))
    (by decide +kernel)
private theorem midpoint_even_17 : ∀ k, 2 ∣ (ibox17 k).lo+(ibox17 k).hi := by decide +kernel
private theorem accepted_17 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox17) tree17 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox17 midpoint_even_17
  simp only [tree17,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox17,candidate_valid h (FixedTape.midBox ibox17),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox17 56 (FixedTape.rowsAux denominator ibox17 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox17) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_17
private noncomputable def tree16 : TapeTree := .centered (candidateRows ibox16) (candidateRows (FixedTape.midBox ibox16))
attribute [irreducible] tree16
private theorem sign_16 : 2*denominator*(computed denominator (FixedTape.midBox ibox16)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox16).gradient k).lo.natAbs ((computed denominator ibox16).gradient k).hi.natAbs : Int)*((ibox16 k).hi-(ibox16 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox16
    (computed denominator ibox16) (computed denominator (FixedTape.midBox ibox16))
    (by decide +kernel)
private theorem midpoint_even_16 : ∀ k, 2 ∣ (ibox16 k).lo+(ibox16 k).hi := by decide +kernel
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox16 midpoint_even_16
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox16,candidate_valid h (FixedTape.midBox ibox16),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox16 56 (FixedTape.rowsAux denominator ibox16 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox16) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_16
private noncomputable def tree15 : TapeTree := .split 1 (((11514493216341793381968030093637257711029640903849461224940430850994995200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree16 tree17
attribute [irreducible] tree15
private theorem accepted_15 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox15) tree15 = true := by
  simp only [tree15,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox15 1 (11514493216341793381968030093637257711029640903849461224940430850994995200000000000000000000000 : Int) false,decode_split denominator ibox15 1 (11514493216341793381968030093637257711029640903849461224940430850994995200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_16 h,accepted_17 h⟩
private noncomputable def tree14 : TapeTree := .centered (candidateRows ibox14) (candidateRows (FixedTape.midBox ibox14))
attribute [irreducible] tree14
private theorem sign_14 : 2*denominator*(computed denominator (FixedTape.midBox ibox14)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox14).gradient k).lo.natAbs ((computed denominator ibox14).gradient k).hi.natAbs : Int)*((ibox14 k).hi-(ibox14 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox14
    (computed denominator ibox14) (computed denominator (FixedTape.midBox ibox14))
    (by decide +kernel)
private theorem midpoint_even_14 : ∀ k, 2 ∣ (ibox14 k).lo+(ibox14 k).hi := by decide +kernel
private theorem accepted_14 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox14) tree14 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox14 midpoint_even_14
  simp only [tree14,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox14,candidate_valid h (FixedTape.midBox ibox14),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox14 56 (FixedTape.rowsAux denominator ibox14 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox14) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_14
private noncomputable def tree13 : TapeTree := .centered (candidateRows ibox13) (candidateRows (FixedTape.midBox ibox13))
attribute [irreducible] tree13
private theorem sign_13 : 2*denominator*(computed denominator (FixedTape.midBox ibox13)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox13).gradient k).lo.natAbs ((computed denominator ibox13).gradient k).hi.natAbs : Int)*((ibox13 k).hi-(ibox13 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox13
    (computed denominator ibox13) (computed denominator (FixedTape.midBox ibox13))
    (by decide +kernel)
private theorem midpoint_even_13 : ∀ k, 2 ∣ (ibox13 k).lo+(ibox13 k).hi := by decide +kernel
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox13 midpoint_even_13
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox13,candidate_valid h (FixedTape.midBox ibox13),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox13 56 (FixedTape.rowsAux denominator ibox13 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox13) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_13
private noncomputable def tree12 : TapeTree := .split 1 (((8224638011672709558548592924026612650735457788463900874957450607853568000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree13 tree14
attribute [irreducible] tree12
private theorem accepted_12 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox12) tree12 = true := by
  simp only [tree12,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox12 1 (8224638011672709558548592924026612650735457788463900874957450607853568000000000000000000000000 : Int) false,decode_split denominator ibox12 1 (8224638011672709558548592924026612650735457788463900874957450607853568000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_13 h,accepted_14 h⟩
private noncomputable def tree11 : TapeTree := .split 1 (((9869565614007251470258311508831935180882549346156681049948940729424281600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree12 tree15
attribute [irreducible] tree11
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox11 1 (9869565614007251470258311508831935180882549346156681049948940729424281600000000000000000000000 : Int) false,decode_split denominator ibox11 1 (9869565614007251470258311508831935180882549346156681049948940729424281600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_12 h,accepted_15 h⟩
private noncomputable def tree10 : TapeTree := .centered (candidateRows ibox10) (candidateRows (FixedTape.midBox ibox10))
attribute [irreducible] tree10
private theorem sign_10 : 2*denominator*(computed denominator (FixedTape.midBox ibox10)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox10).gradient k).lo.natAbs ((computed denominator ibox10).gradient k).hi.natAbs : Int)*((ibox10 k).hi-(ibox10 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox10
    (computed denominator ibox10) (computed denominator (FixedTape.midBox ibox10))
    (by decide +kernel)
private theorem midpoint_even_10 : ∀ k, 2 ∣ (ibox10 k).lo+(ibox10 k).hi := by decide +kernel
private theorem accepted_10 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox10) tree10 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox10 midpoint_even_10
  simp only [tree10,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox10,candidate_valid h (FixedTape.midBox ibox10),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox10 56 (FixedTape.rowsAux denominator ibox10 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox10) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_10
private noncomputable def tree9 : TapeTree := .centered (candidateRows ibox9) (candidateRows (FixedTape.midBox ibox9))
attribute [irreducible] tree9
private theorem sign_9 : 2*denominator*(computed denominator (FixedTape.midBox ibox9)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox9).gradient k).lo.natAbs ((computed denominator ibox9).gradient k).hi.natAbs : Int)*((ibox9 k).hi-(ibox9 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox9
    (computed denominator ibox9) (computed denominator (FixedTape.midBox ibox9))
    (by decide +kernel)
private theorem midpoint_even_9 : ∀ k, 2 ∣ (ibox9 k).lo+(ibox9 k).hi := by decide +kernel
private theorem accepted_9 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox9) tree9 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox9 midpoint_even_9
  simp only [tree9,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox9,candidate_valid h (FixedTape.midBox ibox9),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox9 56 (FixedTape.rowsAux denominator ibox9 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox9) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_9
private noncomputable def tree8 : TapeTree := .split 1 (((4934782807003625735129155754415967590441274673078340524974470364712140800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree9 tree10
attribute [irreducible] tree8
private theorem accepted_8 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox8) tree8 = true := by
  simp only [tree8,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox8 1 (4934782807003625735129155754415967590441274673078340524974470364712140800000000000000000000000 : Int) false,decode_split denominator ibox8 1 (4934782807003625735129155754415967590441274673078340524974470364712140800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_9 h,accepted_10 h⟩
private noncomputable def tree7 : TapeTree := .centered (candidateRows ibox7) (candidateRows (FixedTape.midBox ibox7))
attribute [irreducible] tree7
private theorem sign_7 : 2*denominator*(computed denominator (FixedTape.midBox ibox7)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox7).gradient k).lo.natAbs ((computed denominator ibox7).gradient k).hi.natAbs : Int)*((ibox7 k).hi-(ibox7 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox7
    (computed denominator ibox7) (computed denominator (FixedTape.midBox ibox7))
    (by decide +kernel)
private theorem midpoint_even_7 : ∀ k, 2 ∣ (ibox7 k).lo+(ibox7 k).hi := by decide +kernel
private theorem accepted_7 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox7) tree7 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox7 midpoint_even_7
  simp only [tree7,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox7,candidate_valid h (FixedTape.midBox ibox7),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox7 56 (FixedTape.rowsAux denominator ibox7 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox7) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_7
private noncomputable def tree6 : TapeTree := .centered (candidateRows ibox6) (candidateRows (FixedTape.midBox ibox6))
attribute [irreducible] tree6
private theorem sign_6 : 2*denominator*(computed denominator (FixedTape.midBox ibox6)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox6).gradient k).lo.natAbs ((computed denominator ibox6).gradient k).hi.natAbs : Int)*((ibox6 k).hi-(ibox6 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox6
    (computed denominator ibox6) (computed denominator (FixedTape.midBox ibox6))
    (by decide +kernel)
private theorem midpoint_even_6 : ∀ k, 2 ∣ (ibox6 k).lo+(ibox6 k).hi := by decide +kernel
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox6 midpoint_even_6
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox6,candidate_valid h (FixedTape.midBox ibox6),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox6 56 (FixedTape.rowsAux denominator ibox6 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox6) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_6
private noncomputable def tree5 : TapeTree := .split 1 (((1644927602334541911709718584805322530147091557692780174991490121570713600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree6 tree7
attribute [irreducible] tree5
private theorem accepted_5 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox5) tree5 = true := by
  simp only [tree5,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox5 1 (1644927602334541911709718584805322530147091557692780174991490121570713600000000000000000000000 : Int) false,decode_split denominator ibox5 1 (1644927602334541911709718584805322530147091557692780174991490121570713600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_6 h,accepted_7 h⟩
private noncomputable def tree4 : TapeTree := .split 1 (((3289855204669083823419437169610645060294183115385560349982980243141427200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree5 tree8
attribute [irreducible] tree4
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox4 1 (3289855204669083823419437169610645060294183115385560349982980243141427200000000000000000000000 : Int) false,decode_split denominator ibox4 1 (3289855204669083823419437169610645060294183115385560349982980243141427200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_5 h,accepted_8 h⟩
private noncomputable def tree3 : TapeTree := .split 1 (((6579710409338167646838874339221290120588366230771120699965960486282854400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree11
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 1 (6579710409338167646838874339221290120588366230771120699965960486282854400000000000000000000000 : Int) false,decode_split denominator ibox3 1 (6579710409338167646838874339221290120588366230771120699965960486282854400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_11 h⟩
private noncomputable def tree2 : TapeTree := .split 1 (((13159420818676335293677748678442580241176732461542241399931920972565708800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree18
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 1 (13159420818676335293677748678442580241176732461542241399931920972565708800000000000000000000000 : Int) false,decode_split denominator ibox2 1 (13159420818676335293677748678442580241176732461542241399931920972565708800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_3 h,accepted_18 h⟩
private noncomputable def tree1 : TapeTree := .face 3 true (candidateRows ibox1) tree2
attribute [irreducible] tree1
private theorem sign_1 : 0 ≤ ((computed denominator ibox1).gradient 3).lo := by decide +kernel
private theorem accepted_1 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox1) tree1 = true := by
  simp only [tree1,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox1,?_,accepted_2 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox1)).gradient 3).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox1).gradient 3).lo) denominator_positive).2 sign_1
private noncomputable def tree0 : TapeTree := .face 2 true (candidateRows ibox0) tree1
attribute [irreducible] tree0
private theorem sign_0 : 0 ≤ ((computed denominator ibox0).gradient 2).lo := by decide +kernel
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 56 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox0,?_,accepted_1 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox0)).gradient 2).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox0).gradient 2).lo) denominator_positive).2 sign_0
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (4322916666666667/5000000000000000 : ℚ) (7/8 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 56 = e70 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (4322916666666667/5000000000000000 : ℚ) (7/8 : ℚ)) x → eval e70 x ≤ 0 := by
  have hb := h.child_4 tape 56 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell113_high_first_bottom

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell113_high_first_bottom
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((4322916666666667/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((7/8 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 113 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 113 p)
    (hkb : ((7/8 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((4322916666666667/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : a ≤ bStar), firstResidual (0 : Fin 9) a p r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell113_high_first_bottom.cell_bound h.child_8 h.child_9 (Cell113_high_first_bottom.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell113_high_first_bottom
