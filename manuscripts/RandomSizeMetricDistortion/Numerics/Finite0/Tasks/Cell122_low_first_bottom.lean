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
namespace Cell122_low_first_bottom
private noncomputable def qValues : Fin 2 → ℚ := ![(43956361335054991035054497201740176967/8308785745345758523486681049347789173 : ℚ),(-33780141597749334838940000000000000000/8308785745345758523486681049347789173 : ℚ)]
private noncomputable abbrev e2 : PolyExpr := SharedFiniteSemantics28.e2 qValues
private noncomputable abbrev e7 : PolyExpr := SharedFiniteSemantics28.e7 qValues
private noncomputable abbrev e12 : PolyExpr := SharedFiniteSemantics28.e12 qValues
private noncomputable abbrev e16 : PolyExpr := SharedFiniteSemantics28.e16 qValues
private noncomputable abbrev e89 : PolyExpr := SharedFiniteSemantics28.e89 qValues
private noncomputable abbrev node_1 := SharedFiniteSemantics28.node_1 qValues
private noncomputable abbrev node_2 := SharedFiniteSemantics28.node_2 qValues
private noncomputable abbrev node_3 := SharedFiniteSemantics28.node_3 qValues
private noncomputable abbrev node_4 := SharedFiniteSemantics28.node_4 qValues
private noncomputable abbrev node_6 := SharedFiniteSemantics28.node_6 qValues
private noncomputable abbrev node_7 := SharedFiniteSemantics28.node_7 qValues
private noncomputable abbrev node_10 := SharedFiniteSemantics28.node_10 qValues
private noncomputable abbrev node_11 := SharedFiniteSemantics28.node_11 qValues
private noncomputable abbrev node_12 := SharedFiniteSemantics28.node_12 qValues
private noncomputable abbrev node_14 := SharedFiniteSemantics28.node_14 qValues
private noncomputable abbrev node_15 := SharedFiniteSemantics28.node_15 qValues
private noncomputable abbrev node_16 := SharedFiniteSemantics28.node_16 qValues
private noncomputable abbrev node_54 := SharedFiniteSemantics28.node_54 qValues
private noncomputable abbrev node_55 := SharedFiniteSemantics28.node_55 qValues
private noncomputable abbrev node_56 := SharedFiniteSemantics28.node_56 qValues
private noncomputable abbrev node_57 := SharedFiniteSemantics28.node_57 qValues
private noncomputable abbrev node_58 := SharedFiniteSemantics28.node_58 qValues
private noncomputable abbrev node_59 := SharedFiniteSemantics28.node_59 qValues
private noncomputable abbrev node_60 := SharedFiniteSemantics28.node_60 qValues
private noncomputable abbrev node_61 := SharedFiniteSemantics28.node_61 qValues
private noncomputable abbrev node_63 := SharedFiniteSemantics28.node_63 qValues
private noncomputable abbrev node_64 := SharedFiniteSemantics28.node_64 qValues
private noncomputable abbrev node_65 := SharedFiniteSemantics28.node_65 qValues
private noncomputable abbrev node_66 := SharedFiniteSemantics28.node_66 qValues
private noncomputable abbrev node_67 := SharedFiniteSemantics28.node_67 qValues
private noncomputable abbrev node_68 := SharedFiniteSemantics28.node_68 qValues
private noncomputable abbrev node_69 := SharedFiniteSemantics28.node_69 qValues
private noncomputable abbrev node_70 := SharedFiniteSemantics28.node_70 qValues
private noncomputable abbrev node_71 := SharedFiniteSemantics28.node_71 qValues
private noncomputable abbrev node_88 := SharedFiniteSemantics28.node_88 qValues
private noncomputable abbrev node_89 := SharedFiniteSemantics28.node_89 qValues
private noncomputable abbrev semantic_H_37 := SharedFiniteSemantics28.semantic_H_37 qValues
private noncomputable abbrev semantic_H_53 := SharedFiniteSemantics28.semantic_H_53 qValues
private noncomputable abbrev semantic_psi_87 := SharedFiniteSemantics28.semantic_psi_87 qValues
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
private theorem point_16 (x : Fin 4 → ℝ) : eval e16 x = yPoint x := by
  simp only [node_1,node_2,node_3,node_6,node_7,node_14,node_15,node_16] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem price_lambda_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceLambda 122 p = ((43956361335054991035054497201740176967/8308785745345758523486681049347789173 : ℝ)+(-33780141597749334838940000000000000000/8308785745345758523486681049347789173 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell122,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 122 p = ((145513/100000 : ℝ)*(1/1 : ℝ)-((43956361335054991035054497201740176967/8308785745345758523486681049347789173 : ℝ)+(-33780141597749334838940000000000000000/8308785745345758523486681049347789173 : ℝ)*p)/p)/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell122,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e89 x = (x 0*(1-x 0))*(aPoint x+priceLambda 122 (x 0)*(HStar (yPoint x)-HStar (aPoint x))+priceTau 122 (x 0)*psiStar (rPoint x)+(0)-(cStar)) := by
  have hp0 : x 0 ≠ 0 := ne_of_gt hp.1
  have hp1 : x 0 ≠ 1 := ne_of_lt hp.2
  have heps : 1-x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  rw [price_lambda_normal _ hp,price_tau_normal _ hp]
  simp only [node_1,node_14,node_15,node_54,node_55,node_56,node_57,node_58,node_59,node_60,node_61,node_63,node_64,node_65,node_66,node_67,node_68,node_69,node_70,node_71,node_88,node_89,semantic_H_37,semantic_H_53,semantic_psi_87,point_7,point_12,point_2,point_16]
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
    (hL : lambdaStar (x 0) = priceLambda 122 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 122 (x 0)) :
    (1)*eval e89 x = (x 0*(1-x 0))*(firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (4395636133505499103505449720174017696700000/4587050499937430843922117419533744845930749 : ℚ) (4791666666666667/5000000000000000 : ℚ)) x → eval e89 x ≤ 0)
    (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((4395636133505499103505449720174017696700000/4587050499937430843922117419533744845930749 : ℚ) : ℝ) < p ∧ p ≤ ((4791666666666667/5000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 122 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 122 p)
    (hk0 : ((4791666666666667/5000000000000000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((4395636133505499103505449720174017696700000/4587050499937430843922117419533744845930749 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : a ≤ ((49/100 : ℚ) : ℝ)) :
    firstResidual (0 : Fin 9) a p r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨x,hx,hxp,hxa,hxr⟩ := h1 (4395636133505499103505449720174017696700000/4587050499937430843922117419533744845930749 : ℚ) (4791666666666667/5000000000000000 : ℚ) ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ) p a r hpcell hk0 hr ha hap hcase
  have hcut : ¬(((4791666666666667/5000000000000000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ)) := by norm_num [bStar]
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,if_neg hcut] using hxa
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,if_neg hcut] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 122 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 122 (x 0) := by simpa only [hxp] using hT
  have hrootb : ((2840189/5000000 : ℚ) : ℝ) ≤ bStar := by norm_num [bStar]
  have hflag : aPoint x ≤ bStar := by rw [hax]; exact (hap.trans (min_le_right _ _)).trans (hr.2.trans hrootb)
  have hb := hbound x hx
  have hv : (1 : ℝ)*eval e89 x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 1) hb
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
.mul 4 2,
.const (390189/5000000 : ℚ),
.mul 6 3,
.add 4 7,
.neg 1,
.add 0 9,
.add 5 10,
.const (1085/4818 : ℚ),
.mul 12 11,
.mul 11 11,
.const (19/146 : ℚ),
.mul 15 14,
.mul 11 14,
.const (35/438 : ℚ),
.mul 18 17,
.add 16 19,
.mul 14 14,
.mul 21 21,
.mul 22 22,
.mul 23 23,
.mul 11 24,
.const (1/66 : ℚ),
.mul 26 25,
.add 20 27,
.neg 28,
.add 13 29,
.const (4818/3733 : ℚ),
.mul 31 30,
.mul 12 5,
.mul 5 5,
.mul 15 34,
.mul 5 34,
.mul 18 36,
.add 35 37,
.mul 34 34,
.mul 39 39,
.mul 40 40,
.mul 41 41,
.mul 5 42,
.mul 26 43,
.add 38 44,
.neg 45,
.add 33 46,
.mul 31 47,
.neg 48,
.add 32 49,
.const (43956361335054991035054497201740176967/8308785745345758523486681049347789173 : ℚ),
.const (-33780141597749334838940000000000000000/8308785745345758523486681049347789173 : ℚ),
.mul 52 1,
.add 51 53,
.const (145513/100000 : ℚ),
.mul 1 10,
.mul 55 1,
.neg 54,
.add 57 58,
.mul 59 10,
.const (-113609/200000 : ℚ),
.add 5 61,
.mul 62 56,
.mul 54 50,
.add 63 64,
.const (19/73 : ℚ),
.mul 66 8,
.mul 8 8,
.const (35/146 : ℚ),
.mul 69 68,
.add 67 70,
.mul 68 68,
.mul 72 72,
.mul 73 73,
.mul 74 74,
.const (1/2 : ℚ),
.mul 76 75,
.add 71 77,
.neg 78,
.add 12 79,
.mul 31 80,
.mul 60 81,
.add 65 82]
private noncomputable def ssaQVals : Fin 15 → ℚ := ![(1/1 : ℚ),(49/100 : ℚ),(390189/5000000 : ℚ),(1085/4818 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(4818/3733 : ℚ),(43956361335054991035054497201740176967/8308785745345758523486681049347789173 : ℚ),(-33780141597749334838940000000000000000/8308785745345758523486681049347789173 : ℚ),(145513/100000 : ℚ),(-113609/200000 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ)]
private theorem ssa_tape : MetricDistortion.OptimizedSSAFinite0.S_6caa2853b3095343.p84 ssaQVals = tape := by rfl
private noncomputable def computed (D : Int) (B : Fin 4 → FixedTape.I) : FixedTape.Row :=
  MetricDistortion.OptimizedSSAFinite0.S_6caa2853b3095343.computed ssaQVals D B
private theorem ssa_matches (D : Int) (B : Fin 4 → FixedTape.I) :
    (FixedTape.rowsAux D B [] tape).getD 83 FixedTape.zeroRow = computed D B := by
  rw [←ssa_tape]
  exact MetricDistortion.OptimizedSSAFinite0.S_6caa2853b3095343.ssa_matches ssaQVals D B

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
private noncomputable def denominator : Int := 452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000
private theorem denominator_positive : 0 < denominator := by decide +kernel
private noncomputable def candidateRows (B : Fin 4 → FixedTape.I) : List TapeBounds :=
  (FixedTape.rowsAux denominator B [] tape).map (FixedTape.decodeRow denominator)
private theorem root_in_range : 83 < tape.length := by decide +kernel
private theorem references_valid : tapeRefsValidAux 0 tape = true := by decide +kernel
private theorem candidate_valid (h : Needs) (B : Fin 4 → FixedTape.I) :
    tapeCheck (FixedTape.decodeBox denominator B) tape (candidateRows B) = true :=
  h.child_10.1 denominator denominator_positive B tape references_valid
private theorem candidate_root (B : Fin 4 → FixedTape.I) :
    (candidateRows B).getD 83 zeroTapeBounds = FixedTape.decodeRow denominator (computed denominator B) := by
  unfold candidateRows
  rw [←decode_zeroRow denominator,List.getD_map,ssa_matches]
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨433693005712322553572673038577993307042402380286824545194770310297618996716061008867791003969162222716971909120000000000000000000000000000,433721348284955374448407116868082672775260172532509378542810650200688528733165068110922429438989663651864793847150467470575020277760000000⟩,⟨0,452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000⟩,⟨0,452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000⟩,⟨0,452578798210388185331986681226647287627284964267154994842239685972544910522281046895229629168959865012058625304166400000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := faceI ibox0 2 false
private noncomputable def ibox2 : Fin 4 → FixedTape.I := faceI ibox1 3 true
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 1 226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 1 113144699552597046332996670306661821906821241066788748710559921493136227630570261723807407292239966253014656326041600000000000000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox4 1 56572349776298523166498335153330910953410620533394374355279960746568113815285130861903703646119983126507328163020800000000000000000000000 false
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox4 1 56572349776298523166498335153330910953410620533394374355279960746568113815285130861903703646119983126507328163020800000000000000000000000 true
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox3 1 113144699552597046332996670306661821906821241066788748710559921493136227630570261723807407292239966253014656326041600000000000000000000000 true
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox7 1 169717049328895569499495005459992732860231861600183123065839882239704341445855392585711110938359949379521984489062400000000000000000000000 false
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox7 1 169717049328895569499495005459992732860231861600183123065839882239704341445855392585711110938359949379521984489062400000000000000000000000 true
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox2 1 226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 true
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox10 1 339434098657791138998990010919985465720463723200366246131679764479408682891710785171422221876719898759043968978124800000000000000000000000 false
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox11 1 282861748881492615832491675766654554767053102666971871776399803732840569076425654309518518230599915632536640815104000000000000000000000000 false
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox11 1 282861748881492615832491675766654554767053102666971871776399803732840569076425654309518518230599915632536640815104000000000000000000000000 true
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox13 1 311147923769641877415740843343320010243758412933669058954039784106124625984068219740470370053659907195790304896614400000000000000000000000 false
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox13 1 311147923769641877415740843343320010243758412933669058954039784106124625984068219740470370053659907195790304896614400000000000000000000000 true
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox10 1 339434098657791138998990010919985465720463723200366246131679764479408682891710785171422221876719898759043968978124800000000000000000000000 true
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox16 1 396006448434089662165488346073316376673874343733760620486959725225976796706995916033325925522839881885551297141145600000000000000000000000 false
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox17 1 367720273545940400582239178496650921197169033467063433309319744852692739799353350602374073699779890322297633059635200000000000000000000000 false
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox17 1 367720273545940400582239178496650921197169033467063433309319744852692739799353350602374073699779890322297633059635200000000000000000000000 true
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox16 1 396006448434089662165488346073316376673874343733760620486959725225976796706995916033325925522839881885551297141145600000000000000000000000 true
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox20 1 424292623322238923748737513649981832150579654000457807664599705599260853614638481464277777345899873448804961222656000000000000000000000000 false
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox20 1 424292623322238923748737513649981832150579654000457807664599705599260853614638481464277777345899873448804961222656000000000000000000000000 true
private noncomputable def tree22 : TapeTree := .centered (candidateRows ibox22) (candidateRows (FixedTape.midBox ibox22))
attribute [irreducible] tree22
private theorem sign_22 : 2*denominator*(computed denominator (FixedTape.midBox ibox22)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox22).gradient k).lo.natAbs ((computed denominator ibox22).gradient k).hi.natAbs : Int)*((ibox22 k).hi-(ibox22 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox22
    (computed denominator ibox22) (computed denominator (FixedTape.midBox ibox22))
    (by decide +kernel)
private theorem midpoint_even_22 : ∀ k, 2 ∣ (ibox22 k).lo+(ibox22 k).hi := by decide +kernel
private theorem accepted_22 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox22) tree22 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox22 midpoint_even_22
  simp only [tree22,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox22,candidate_valid h (FixedTape.midBox ibox22),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox22 83 (FixedTape.rowsAux denominator ibox22 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox22) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_22
private noncomputable def tree21 : TapeTree := .centered (candidateRows ibox21) (candidateRows (FixedTape.midBox ibox21))
attribute [irreducible] tree21
private theorem sign_21 : 2*denominator*(computed denominator (FixedTape.midBox ibox21)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox21).gradient k).lo.natAbs ((computed denominator ibox21).gradient k).hi.natAbs : Int)*((ibox21 k).hi-(ibox21 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox21
    (computed denominator ibox21) (computed denominator (FixedTape.midBox ibox21))
    (by decide +kernel)
private theorem midpoint_even_21 : ∀ k, 2 ∣ (ibox21 k).lo+(ibox21 k).hi := by decide +kernel
private theorem accepted_21 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox21) tree21 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox21 midpoint_even_21
  simp only [tree21,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox21,candidate_valid h (FixedTape.midBox ibox21),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox21 83 (FixedTape.rowsAux denominator ibox21 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox21) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_21
private noncomputable def tree20 : TapeTree := .split 1 (((424292623322238923748737513649981832150579654000457807664599705599260853614638481464277777345899873448804961222656000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree21 tree22
attribute [irreducible] tree20
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox20 1 (424292623322238923748737513649981832150579654000457807664599705599260853614638481464277777345899873448804961222656000000000000000000000000 : Int) false,decode_split denominator ibox20 1 (424292623322238923748737513649981832150579654000457807664599705599260853614638481464277777345899873448804961222656000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_21 h,accepted_22 h⟩
private noncomputable def tree19 : TapeTree := .centered (candidateRows ibox19) (candidateRows (FixedTape.midBox ibox19))
attribute [irreducible] tree19
private theorem sign_19 : 2*denominator*(computed denominator (FixedTape.midBox ibox19)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox19).gradient k).lo.natAbs ((computed denominator ibox19).gradient k).hi.natAbs : Int)*((ibox19 k).hi-(ibox19 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox19
    (computed denominator ibox19) (computed denominator (FixedTape.midBox ibox19))
    (by decide +kernel)
private theorem midpoint_even_19 : ∀ k, 2 ∣ (ibox19 k).lo+(ibox19 k).hi := by decide +kernel
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox19 midpoint_even_19
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox19,candidate_valid h (FixedTape.midBox ibox19),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox19 83 (FixedTape.rowsAux denominator ibox19 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox19) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_19
private noncomputable def tree18 : TapeTree := .centered (candidateRows ibox18) (candidateRows (FixedTape.midBox ibox18))
attribute [irreducible] tree18
private theorem sign_18 : 2*denominator*(computed denominator (FixedTape.midBox ibox18)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox18).gradient k).lo.natAbs ((computed denominator ibox18).gradient k).hi.natAbs : Int)*((ibox18 k).hi-(ibox18 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox18
    (computed denominator ibox18) (computed denominator (FixedTape.midBox ibox18))
    (by decide +kernel)
private theorem midpoint_even_18 : ∀ k, 2 ∣ (ibox18 k).lo+(ibox18 k).hi := by decide +kernel
private theorem accepted_18 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox18) tree18 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox18 midpoint_even_18
  simp only [tree18,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox18,candidate_valid h (FixedTape.midBox ibox18),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox18 83 (FixedTape.rowsAux denominator ibox18 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox18) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_18
private noncomputable def tree17 : TapeTree := .split 1 (((367720273545940400582239178496650921197169033467063433309319744852692739799353350602374073699779890322297633059635200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree18 tree19
attribute [irreducible] tree17
private theorem accepted_17 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox17) tree17 = true := by
  simp only [tree17,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox17 1 (367720273545940400582239178496650921197169033467063433309319744852692739799353350602374073699779890322297633059635200000000000000000000000 : Int) false,decode_split denominator ibox17 1 (367720273545940400582239178496650921197169033467063433309319744852692739799353350602374073699779890322297633059635200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_18 h,accepted_19 h⟩
private noncomputable def tree16 : TapeTree := .split 1 (((396006448434089662165488346073316376673874343733760620486959725225976796706995916033325925522839881885551297141145600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree17 tree20
attribute [irreducible] tree16
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox16 1 (396006448434089662165488346073316376673874343733760620486959725225976796706995916033325925522839881885551297141145600000000000000000000000 : Int) false,decode_split denominator ibox16 1 (396006448434089662165488346073316376673874343733760620486959725225976796706995916033325925522839881885551297141145600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_17 h,accepted_20 h⟩
private noncomputable def tree15 : TapeTree := .centered (candidateRows ibox15) (candidateRows (FixedTape.midBox ibox15))
attribute [irreducible] tree15
private theorem sign_15 : 2*denominator*(computed denominator (FixedTape.midBox ibox15)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox15).gradient k).lo.natAbs ((computed denominator ibox15).gradient k).hi.natAbs : Int)*((ibox15 k).hi-(ibox15 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox15
    (computed denominator ibox15) (computed denominator (FixedTape.midBox ibox15))
    (by decide +kernel)
private theorem midpoint_even_15 : ∀ k, 2 ∣ (ibox15 k).lo+(ibox15 k).hi := by decide +kernel
private theorem accepted_15 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox15) tree15 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox15 midpoint_even_15
  simp only [tree15,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox15,candidate_valid h (FixedTape.midBox ibox15),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox15 83 (FixedTape.rowsAux denominator ibox15 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox15) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_15
private noncomputable def tree14 : TapeTree := .centered (candidateRows ibox14) (candidateRows (FixedTape.midBox ibox14))
attribute [irreducible] tree14
private theorem sign_14 : 2*denominator*(computed denominator (FixedTape.midBox ibox14)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox14).gradient k).lo.natAbs ((computed denominator ibox14).gradient k).hi.natAbs : Int)*((ibox14 k).hi-(ibox14 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox14
    (computed denominator ibox14) (computed denominator (FixedTape.midBox ibox14))
    (by decide +kernel)
private theorem midpoint_even_14 : ∀ k, 2 ∣ (ibox14 k).lo+(ibox14 k).hi := by decide +kernel
private theorem accepted_14 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox14) tree14 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox14 midpoint_even_14
  simp only [tree14,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox14,candidate_valid h (FixedTape.midBox ibox14),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox14 83 (FixedTape.rowsAux denominator ibox14 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox14) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_14
private noncomputable def tree13 : TapeTree := .split 1 (((311147923769641877415740843343320010243758412933669058954039784106124625984068219740470370053659907195790304896614400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree14 tree15
attribute [irreducible] tree13
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox13 1 (311147923769641877415740843343320010243758412933669058954039784106124625984068219740470370053659907195790304896614400000000000000000000000 : Int) false,decode_split denominator ibox13 1 (311147923769641877415740843343320010243758412933669058954039784106124625984068219740470370053659907195790304896614400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_14 h,accepted_15 h⟩
private noncomputable def tree12 : TapeTree := .centered (candidateRows ibox12) (candidateRows (FixedTape.midBox ibox12))
attribute [irreducible] tree12
private theorem sign_12 : 2*denominator*(computed denominator (FixedTape.midBox ibox12)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox12).gradient k).lo.natAbs ((computed denominator ibox12).gradient k).hi.natAbs : Int)*((ibox12 k).hi-(ibox12 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox12
    (computed denominator ibox12) (computed denominator (FixedTape.midBox ibox12))
    (by decide +kernel)
private theorem midpoint_even_12 : ∀ k, 2 ∣ (ibox12 k).lo+(ibox12 k).hi := by decide +kernel
private theorem accepted_12 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox12) tree12 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox12 midpoint_even_12
  simp only [tree12,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox12,candidate_valid h (FixedTape.midBox ibox12),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox12 83 (FixedTape.rowsAux denominator ibox12 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox12) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_12
private noncomputable def tree11 : TapeTree := .split 1 (((282861748881492615832491675766654554767053102666971871776399803732840569076425654309518518230599915632536640815104000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree12 tree13
attribute [irreducible] tree11
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox11 1 (282861748881492615832491675766654554767053102666971871776399803732840569076425654309518518230599915632536640815104000000000000000000000000 : Int) false,decode_split denominator ibox11 1 (282861748881492615832491675766654554767053102666971871776399803732840569076425654309518518230599915632536640815104000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_12 h,accepted_13 h⟩
private noncomputable def tree10 : TapeTree := .split 1 (((339434098657791138998990010919985465720463723200366246131679764479408682891710785171422221876719898759043968978124800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree11 tree16
attribute [irreducible] tree10
private theorem accepted_10 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox10) tree10 = true := by
  simp only [tree10,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox10 1 (339434098657791138998990010919985465720463723200366246131679764479408682891710785171422221876719898759043968978124800000000000000000000000 : Int) false,decode_split denominator ibox10 1 (339434098657791138998990010919985465720463723200366246131679764479408682891710785171422221876719898759043968978124800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_11 h,accepted_16 h⟩
private noncomputable def tree9 : TapeTree := .centered (candidateRows ibox9) (candidateRows (FixedTape.midBox ibox9))
attribute [irreducible] tree9
private theorem sign_9 : 2*denominator*(computed denominator (FixedTape.midBox ibox9)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox9).gradient k).lo.natAbs ((computed denominator ibox9).gradient k).hi.natAbs : Int)*((ibox9 k).hi-(ibox9 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox9
    (computed denominator ibox9) (computed denominator (FixedTape.midBox ibox9))
    (by decide +kernel)
private theorem midpoint_even_9 : ∀ k, 2 ∣ (ibox9 k).lo+(ibox9 k).hi := by decide +kernel
private theorem accepted_9 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox9) tree9 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox9 midpoint_even_9
  simp only [tree9,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox9,candidate_valid h (FixedTape.midBox ibox9),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox9 83 (FixedTape.rowsAux denominator ibox9 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox9) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_9
private noncomputable def tree8 : TapeTree := .centered (candidateRows ibox8) (candidateRows (FixedTape.midBox ibox8))
attribute [irreducible] tree8
private theorem sign_8 : 2*denominator*(computed denominator (FixedTape.midBox ibox8)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox8).gradient k).lo.natAbs ((computed denominator ibox8).gradient k).hi.natAbs : Int)*((ibox8 k).hi-(ibox8 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox8
    (computed denominator ibox8) (computed denominator (FixedTape.midBox ibox8))
    (by decide +kernel)
private theorem midpoint_even_8 : ∀ k, 2 ∣ (ibox8 k).lo+(ibox8 k).hi := by decide +kernel
private theorem accepted_8 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox8) tree8 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox8 midpoint_even_8
  simp only [tree8,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox8,candidate_valid h (FixedTape.midBox ibox8),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox8 83 (FixedTape.rowsAux denominator ibox8 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox8) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_8
private noncomputable def tree7 : TapeTree := .split 1 (((169717049328895569499495005459992732860231861600183123065839882239704341445855392585711110938359949379521984489062400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree8 tree9
attribute [irreducible] tree7
private theorem accepted_7 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox7) tree7 = true := by
  simp only [tree7,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox7 1 (169717049328895569499495005459992732860231861600183123065839882239704341445855392585711110938359949379521984489062400000000000000000000000 : Int) false,decode_split denominator ibox7 1 (169717049328895569499495005459992732860231861600183123065839882239704341445855392585711110938359949379521984489062400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_8 h,accepted_9 h⟩
private noncomputable def tree6 : TapeTree := .centered (candidateRows ibox6) (candidateRows (FixedTape.midBox ibox6))
attribute [irreducible] tree6
private theorem sign_6 : 2*denominator*(computed denominator (FixedTape.midBox ibox6)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox6).gradient k).lo.natAbs ((computed denominator ibox6).gradient k).hi.natAbs : Int)*((ibox6 k).hi-(ibox6 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox6
    (computed denominator ibox6) (computed denominator (FixedTape.midBox ibox6))
    (by decide +kernel)
private theorem midpoint_even_6 : ∀ k, 2 ∣ (ibox6 k).lo+(ibox6 k).hi := by decide +kernel
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox6 midpoint_even_6
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox6,candidate_valid h (FixedTape.midBox ibox6),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox6 83 (FixedTape.rowsAux denominator ibox6 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox6) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_6
private noncomputable def tree5 : TapeTree := .centered (candidateRows ibox5) (candidateRows (FixedTape.midBox ibox5))
attribute [irreducible] tree5
private theorem sign_5 : 2*denominator*(computed denominator (FixedTape.midBox ibox5)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox5).gradient k).lo.natAbs ((computed denominator ibox5).gradient k).hi.natAbs : Int)*((ibox5 k).hi-(ibox5 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox5
    (computed denominator ibox5) (computed denominator (FixedTape.midBox ibox5))
    (by decide +kernel)
private theorem midpoint_even_5 : ∀ k, 2 ∣ (ibox5 k).lo+(ibox5 k).hi := by decide +kernel
private theorem accepted_5 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox5) tree5 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox5 midpoint_even_5
  simp only [tree5,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox5,candidate_valid h (FixedTape.midBox ibox5),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox5 83 (FixedTape.rowsAux denominator ibox5 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox5) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_5
private noncomputable def tree4 : TapeTree := .split 1 (((56572349776298523166498335153330910953410620533394374355279960746568113815285130861903703646119983126507328163020800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree5 tree6
attribute [irreducible] tree4
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox4 1 (56572349776298523166498335153330910953410620533394374355279960746568113815285130861903703646119983126507328163020800000000000000000000000 : Int) false,decode_split denominator ibox4 1 (56572349776298523166498335153330910953410620533394374355279960746568113815285130861903703646119983126507328163020800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_5 h,accepted_6 h⟩
private noncomputable def tree3 : TapeTree := .split 1 (((113144699552597046332996670306661821906821241066788748710559921493136227630570261723807407292239966253014656326041600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree7
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 1 (113144699552597046332996670306661821906821241066788748710559921493136227630570261723807407292239966253014656326041600000000000000000000000 : Int) false,decode_split denominator ibox3 1 (113144699552597046332996670306661821906821241066788748710559921493136227630570261723807407292239966253014656326041600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_7 h⟩
private noncomputable def tree2 : TapeTree := .split 1 (((226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree10
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 1 (226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 : Int) false,decode_split denominator ibox2 1 (226289399105194092665993340613323643813642482133577497421119842986272455261140523447614814584479932506029312652083200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_3 h,accepted_10 h⟩
private noncomputable def tree1 : TapeTree := .face 3 true (candidateRows ibox1) tree2
attribute [irreducible] tree1
private theorem sign_1 : 0 ≤ ((computed denominator ibox1).gradient 3).lo := by decide +kernel
private theorem accepted_1 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox1) tree1 = true := by
  simp only [tree1,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox1,?_,accepted_2 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox1)).gradient 3).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox1).gradient 3).lo) denominator_positive).2 sign_1
private noncomputable def tree0 : TapeTree := .face 2 false (candidateRows ibox0) tree1
attribute [irreducible] tree0
private theorem sign_0 : ((computed denominator ibox0).gradient 2).hi ≤ 0 := by decide +kernel
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 83 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox0,?_,accepted_1 h⟩
  rw [candidate_root]
  change decide (((FixedTape.decodeRow denominator (computed denominator ibox0)).gradient 2).hi ≤ 0) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox0).gradient 2).hi) denominator_positive).1 sign_0
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (4395636133505499103505449720174017696700000/4587050499937430843922117419533744845930749 : ℚ) (4791666666666667/5000000000000000 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 83 = e89 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (4395636133505499103505449720174017696700000/4587050499937430843922117419533744845930749 : ℚ) (4791666666666667/5000000000000000 : ℚ)) x → eval e89 x ≤ 0 := by
  have hb := h.child_4 tape 83 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell122_low_first_bottom

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell122_low_first_bottom
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((4395636133505499103505449720174017696700000/4587050499937430843922117419533744845930749 : ℚ) : ℝ) < p ∧ p ≤ ((4791666666666667/5000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 122 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 122 p)
    (hk0 : ((4791666666666667/5000000000000000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((4395636133505499103505449720174017696700000/4587050499937430843922117419533744845930749 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : a ≤ ((49/100 : ℚ) : ℝ)), firstResidual (0 : Fin 9) a p r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell122_low_first_bottom.cell_bound h.child_8 h.child_9 (Cell122_low_first_bottom.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell122_low_first_bottom
