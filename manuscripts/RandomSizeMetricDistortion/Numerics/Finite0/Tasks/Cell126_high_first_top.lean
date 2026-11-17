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
namespace Cell126_high_first_top
private noncomputable def qValues : Fin 2 → ℚ := ![(-531820724229059449651324237017/538282753306461493807090000000 : ℚ),(132046403355525500000000/53828275330646149380709 : ℚ)]
private noncomputable abbrev e2 : PolyExpr := SharedFiniteSemantics31.e2 qValues
private noncomputable abbrev e10 : PolyExpr := SharedFiniteSemantics31.e10 qValues
private noncomputable abbrev e14 : PolyExpr := SharedFiniteSemantics31.e14 qValues
private noncomputable abbrev e41 : PolyExpr := SharedFiniteSemantics31.e41 qValues
private noncomputable abbrev e104 : PolyExpr := SharedFiniteSemantics31.e104 qValues
private noncomputable abbrev node_1 := SharedFiniteSemantics31.node_1 qValues
private noncomputable abbrev node_2 := SharedFiniteSemantics31.node_2 qValues
private noncomputable abbrev node_3 := SharedFiniteSemantics31.node_3 qValues
private noncomputable abbrev node_4 := SharedFiniteSemantics31.node_4 qValues
private noncomputable abbrev node_6 := SharedFiniteSemantics31.node_6 qValues
private noncomputable abbrev node_7 := SharedFiniteSemantics31.node_7 qValues
private noncomputable abbrev node_8 := SharedFiniteSemantics31.node_8 qValues
private noncomputable abbrev node_9 := SharedFiniteSemantics31.node_9 qValues
private noncomputable abbrev node_10 := SharedFiniteSemantics31.node_10 qValues
private noncomputable abbrev node_11 := SharedFiniteSemantics31.node_11 qValues
private noncomputable abbrev node_12 := SharedFiniteSemantics31.node_12 qValues
private noncomputable abbrev node_13 := SharedFiniteSemantics31.node_13 qValues
private noncomputable abbrev node_14 := SharedFiniteSemantics31.node_14 qValues
private noncomputable abbrev node_15 := SharedFiniteSemantics31.node_15 qValues
private noncomputable abbrev node_16 := SharedFiniteSemantics31.node_16 qValues
private noncomputable abbrev node_35 := SharedFiniteSemantics31.node_35 qValues
private noncomputable abbrev node_36 := SharedFiniteSemantics31.node_36 qValues
private noncomputable abbrev node_37 := SharedFiniteSemantics31.node_37 qValues
private noncomputable abbrev node_38 := SharedFiniteSemantics31.node_38 qValues
private noncomputable abbrev node_39 := SharedFiniteSemantics31.node_39 qValues
private noncomputable abbrev node_40 := SharedFiniteSemantics31.node_40 qValues
private noncomputable abbrev node_41 := SharedFiniteSemantics31.node_41 qValues
private noncomputable abbrev node_72 := SharedFiniteSemantics31.node_72 qValues
private noncomputable abbrev node_73 := SharedFiniteSemantics31.node_73 qValues
private noncomputable abbrev node_74 := SharedFiniteSemantics31.node_74 qValues
private noncomputable abbrev node_75 := SharedFiniteSemantics31.node_75 qValues
private noncomputable abbrev node_76 := SharedFiniteSemantics31.node_76 qValues
private noncomputable abbrev node_77 := SharedFiniteSemantics31.node_77 qValues
private noncomputable abbrev node_78 := SharedFiniteSemantics31.node_78 qValues
private noncomputable abbrev node_80 := SharedFiniteSemantics31.node_80 qValues
private noncomputable abbrev node_81 := SharedFiniteSemantics31.node_81 qValues
private noncomputable abbrev node_82 := SharedFiniteSemantics31.node_82 qValues
private noncomputable abbrev node_83 := SharedFiniteSemantics31.node_83 qValues
private noncomputable abbrev node_84 := SharedFiniteSemantics31.node_84 qValues
private noncomputable abbrev node_85 := SharedFiniteSemantics31.node_85 qValues
private noncomputable abbrev node_86 := SharedFiniteSemantics31.node_86 qValues
private noncomputable abbrev node_87 := SharedFiniteSemantics31.node_87 qValues
private noncomputable abbrev node_88 := SharedFiniteSemantics31.node_88 qValues
private noncomputable abbrev node_89 := SharedFiniteSemantics31.node_89 qValues
private noncomputable abbrev node_103 := SharedFiniteSemantics31.node_103 qValues
private noncomputable abbrev node_104 := SharedFiniteSemantics31.node_104 qValues
private noncomputable abbrev semantic_H_60 := SharedFiniteSemantics31.semantic_H_60 qValues
private noncomputable abbrev semantic_H_71 := SharedFiniteSemantics31.semantic_H_71 qValues
private noncomputable abbrev semantic_psi_34 := SharedFiniteSemantics31.semantic_psi_34 qValues
private noncomputable abbrev semantic_psi_102 := SharedFiniteSemantics31.semantic_psi_102 qValues
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
private theorem point_41 (x : Fin 4 → ℝ) : eval e41 x = yPoint x := by
  simp only [node_1,node_2,node_3,node_6,node_7,node_8,node_9,node_10,node_39,node_40,node_41] <;>
    norm_num [qValues,aPoint,rPoint,yPoint,bStar] <;> ring <;> simp
private theorem price_lambda_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceLambda 126 p = ((-531820724229059449651324237017/538282753306461493807090000000 : ℝ)+(132046403355525500000000/53828275330646149380709 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell126,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 126 p = ((145513/100000 : ℝ)*(1/1 : ℝ)-((-531820724229059449651324237017/538282753306461493807090000000 : ℝ)+(132046403355525500000000/53828275330646149380709 : ℝ)*p)/p)/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell126,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e104 x = (x 0*(1-x 0))*(aPoint x+priceLambda 126 (x 0)*(HStar (yPoint x)-HStar (aPoint x))+priceTau 126 (x 0)*psiStar (rPoint x)+(cStar-aPoint x-eta (0 : Fin 9)*psiStar (aPoint x))-(cStar)) := by
  have hp0 : x 0 ≠ 0 := ne_of_gt hp.1
  have hp1 : x 0 ≠ 1 := ne_of_lt hp.2
  have heps : 1-x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  rw [price_lambda_normal _ hp,price_tau_normal _ hp]
  simp only [node_1,node_11,node_15,node_16,node_35,node_36,node_37,node_38,node_39,node_40,node_72,node_73,node_74,node_75,node_76,node_77,node_78,node_80,node_81,node_82,node_83,node_84,node_85,node_86,node_87,node_88,node_89,node_103,node_104,semantic_H_60,semantic_H_71,semantic_psi_34,semantic_psi_102,point_10,point_14,point_2,point_41]
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
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) (ha : bStar < aPoint x)
    (hL : lambdaStar (x 0) = priceLambda 126 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 126 (x 0)) :
    (1)*eval e104 x = (x 0*(1-x 0))*(firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_neg (not_le.mpr ha),hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (4947916666666667/5000000000000000 : ℚ) (99/100 : ℚ)) x → eval e104 x ≤ 0)
    (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((4947916666666667/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((99/100 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 126 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 126 p)
    (hkb : ((99/100 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((4947916666666667/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : bStar < a) :
    firstResidual (0 : Fin 9) a p r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxr⟩ := h5 (4947916666666667/5000000000000000 : ℚ) (99/100 : ℚ) bStar p a r hpcell hkb hr.2 hap hcase
  have hax : aPoint x = a := by simpa only [aPoint,rPoint] using hxa
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 126 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 126 (x 0) := by simpa only [hxp] using hT
  have hflag : bStar < aPoint x := by simpa only [hax] using hcase
  have hb := hbound x hx
  have hv : (1 : ℝ)*eval e104 x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 1) hb
  rw [actual_identity hs x hpx hflag hLx hTx] at hv
  have hscale : 0 < x 0*(1-x 0) := mul_pos hpx.1 (sub_pos.mpr hpx.2)
  have hv : firstResidual (0 : Fin 9) (aPoint x) (x 0) (rPoint x) ≤ 0 := le_of_not_gt (fun hpos => (not_lt_of_ge hv) (mul_pos hscale hpos))
  simpa only [hxp,hax,hrx] using hv
private noncomputable def tape : List TapeOp := [
.const (1/1 : ℚ),
.var 0,
.var 1,
.var 2,
.const (2840189/5000000 : ℚ),
.const (-2840189/5000000 : ℚ),
.add 1 5,
.mul 6 2,
.add 4 7,
.neg 8,
.add 0 9,
.mul 10 3,
.add 8 11,
.const (113609/200000 : ℚ),
.add 13 9,
.const (1085/4818 : ℚ),
.const (19/73 : ℚ),
.mul 16 8,
.mul 8 8,
.const (35/146 : ℚ),
.mul 19 18,
.add 17 20,
.mul 18 18,
.mul 22 22,
.mul 23 23,
.mul 24 24,
.const (1/2 : ℚ),
.mul 26 25,
.add 21 27,
.neg 28,
.add 15 29,
.const (4818/3733 : ℚ),
.mul 31 30,
.const (145513/100000 : ℚ),
.mul 33 32,
.neg 34,
.add 14 35,
.neg 1,
.add 0 37,
.add 8 38,
.mul 15 39,
.mul 39 39,
.const (19/146 : ℚ),
.mul 42 41,
.mul 39 41,
.const (35/438 : ℚ),
.mul 45 44,
.add 43 46,
.mul 41 41,
.mul 48 48,
.mul 49 49,
.mul 50 50,
.mul 39 51,
.const (1/66 : ℚ),
.mul 53 52,
.add 47 54,
.neg 55,
.add 40 56,
.mul 31 57,
.mul 15 8,
.mul 42 18,
.mul 8 18,
.mul 45 61,
.add 60 62,
.mul 8 25,
.mul 53 64,
.add 63 65,
.neg 66,
.add 59 67,
.mul 31 68,
.neg 69,
.add 58 70,
.const (-531820724229059449651324237017/538282753306461493807090000000 : ℚ),
.const (132046403355525500000000/53828275330646149380709 : ℚ),
.mul 73 1,
.add 72 74,
.mul 1 38,
.mul 33 1,
.neg 75,
.add 77 78,
.mul 79 38,
.add 8 36,
.const (-113609/200000 : ℚ),
.add 81 82,
.mul 83 76,
.mul 75 71,
.add 84 85,
.mul 16 12,
.mul 12 12,
.mul 19 88,
.add 87 89,
.mul 88 88,
.mul 91 91,
.mul 92 92,
.mul 93 93,
.mul 26 94,
.add 90 95,
.neg 96,
.add 15 97,
.mul 31 98,
.mul 80 99,
.add 86 100]
private noncomputable def ssaQVals : Fin 16 → ℚ := ![(1/1 : ℚ),(2840189/5000000 : ℚ),(-2840189/5000000 : ℚ),(113609/200000 : ℚ),(1085/4818 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ),(4818/3733 : ℚ),(145513/100000 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(-531820724229059449651324237017/538282753306461493807090000000 : ℚ),(132046403355525500000000/53828275330646149380709 : ℚ),(-113609/200000 : ℚ)]
private theorem ssa_tape : MetricDistortion.OptimizedSSAFinite0.S_0e6d9b8e9220e7e3.p102 ssaQVals = tape := by rfl
private noncomputable def computed (D : Int) (B : Fin 4 → FixedTape.I) : FixedTape.Row :=
  MetricDistortion.OptimizedSSAFinite0.S_0e6d9b8e9220e7e3.computed ssaQVals D B
private theorem ssa_matches (D : Int) (B : Fin 4 → FixedTape.I) :
    (FixedTape.rowsAux D B [] tape).getD 101 FixedTape.zeroRow = computed D B := by
  rw [←ssa_tape]
  exact MetricDistortion.OptimizedSSAFinite0.S_0e6d9b8e9220e7e3.ssa_matches ssaQVals D B

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
private noncomputable def denominator : Int := 3835171936719548933064017577478507181007542093873668738252800000000000000000000000
private theorem denominator_positive : 0 < denominator := by decide +kernel
private noncomputable def candidateRows (B : Fin 4 → FixedTape.I) : List TapeBounds :=
  (FixedTape.rowsAux denominator B [] tape).map (FixedTape.decodeRow denominator)
private theorem root_in_range : 101 < tape.length := by decide +kernel
private theorem references_valid : tapeRefsValidAux 0 tape = true := by decide +kernel
private theorem candidate_valid (h : Needs) (B : Fin 4 → FixedTape.I) :
    tapeCheck (FixedTape.decodeBox denominator B) tape (candidateRows B) = true :=
  h.child_10.1 denominator denominator_positive B tape references_valid
private theorem candidate_root (B : Fin 4 → FixedTape.I) :
    (candidateRows B).getD 101 zeroTapeBounds = FixedTape.decodeRow denominator (computed denominator B) := by
  unfold candidateRows
  rw [←decode_zeroRow denominator,List.getD_map,ssa_matches]
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨3795222229045387220689396509016368268806552028962963422732139591577915883520000000,3796820217352353443733377401703722109197466672934932050870272000000000000000000000⟩,⟨0,3835171936719548933064017577478507181007542093873668738252800000000000000000000000⟩,⟨0,3835171936719548933064017577478507181007542093873668738252800000000000000000000000⟩,⟨0,3835171936719548933064017577478507181007542093873668738252800000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := faceI ibox0 3 true
private noncomputable def ibox2 : Fin 4 → FixedTape.I := splitI ibox1 1 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 1 958792984179887233266004394369626795251885523468417184563200000000000000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox3 1 479396492089943616633002197184813397625942761734208592281600000000000000000000000 false
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox4 1 239698246044971808316501098592406698812971380867104296140800000000000000000000000 false
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox5 1 119849123022485904158250549296203349406485690433552148070400000000000000000000000 false
private noncomputable def ibox7 : Fin 4 → FixedTape.I := splitI ibox6 1 59924561511242952079125274648101674703242845216776074035200000000000000000000000 false
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox7 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox7 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox9 2 2876378952539661699798013183108880385755656570405251553689600000000000000000000000 false
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox9 2 2876378952539661699798013183108880385755656570405251553689600000000000000000000000 true
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox11 1 29962280755621476039562637324050837351621422608388037017600000000000000000000000 false
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox11 1 29962280755621476039562637324050837351621422608388037017600000000000000000000000 true
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox6 1 59924561511242952079125274648101674703242845216776074035200000000000000000000000 true
private noncomputable def ibox15 : Fin 4 → FixedTape.I := splitI ibox14 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox14 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox16 2 2876378952539661699798013183108880385755656570405251553689600000000000000000000000 false
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox16 2 2876378952539661699798013183108880385755656570405251553689600000000000000000000000 true
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox18 1 89886842266864428118687911972152512054864267825164111052800000000000000000000000 false
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox18 1 89886842266864428118687911972152512054864267825164111052800000000000000000000000 true
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox5 1 119849123022485904158250549296203349406485690433552148070400000000000000000000000 true
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox21 1 179773684533728856237375823944305024109728535650328222105600000000000000000000000 false
private noncomputable def ibox23 : Fin 4 → FixedTape.I := splitI ibox22 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox22 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox24 2 2876378952539661699798013183108880385755656570405251553689600000000000000000000000 false
private noncomputable def ibox26 : Fin 4 → FixedTape.I := splitI ibox24 2 2876378952539661699798013183108880385755656570405251553689600000000000000000000000 true
private noncomputable def ibox27 : Fin 4 → FixedTape.I := splitI ibox26 1 149811403778107380197813186620254186758107113041940185088000000000000000000000000 false
private noncomputable def ibox28 : Fin 4 → FixedTape.I := splitI ibox26 1 149811403778107380197813186620254186758107113041940185088000000000000000000000000 true
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox21 1 179773684533728856237375823944305024109728535650328222105600000000000000000000000 true
private noncomputable def ibox30 : Fin 4 → FixedTape.I := splitI ibox29 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox31 : Fin 4 → FixedTape.I := splitI ibox29 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox32 : Fin 4 → FixedTape.I := splitI ibox31 2 2876378952539661699798013183108880385755656570405251553689600000000000000000000000 false
private noncomputable def ibox33 : Fin 4 → FixedTape.I := splitI ibox31 2 2876378952539661699798013183108880385755656570405251553689600000000000000000000000 true
private noncomputable def ibox34 : Fin 4 → FixedTape.I := splitI ibox33 1 209735965289350332276938461268355861461349958258716259123200000000000000000000000 false
private noncomputable def ibox35 : Fin 4 → FixedTape.I := splitI ibox33 1 209735965289350332276938461268355861461349958258716259123200000000000000000000000 true
private noncomputable def ibox36 : Fin 4 → FixedTape.I := splitI ibox4 1 239698246044971808316501098592406698812971380867104296140800000000000000000000000 true
private noncomputable def ibox37 : Fin 4 → FixedTape.I := splitI ibox36 1 359547369067457712474751647888610048219457071300656444211200000000000000000000000 false
private noncomputable def ibox38 : Fin 4 → FixedTape.I := splitI ibox37 1 299622807556214760395626373240508373516214226083880370176000000000000000000000000 false
private noncomputable def ibox39 : Fin 4 → FixedTape.I := splitI ibox38 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox40 : Fin 4 → FixedTape.I := splitI ibox38 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox41 : Fin 4 → FixedTape.I := splitI ibox40 2 2876378952539661699798013183108880385755656570405251553689600000000000000000000000 false
private noncomputable def ibox42 : Fin 4 → FixedTape.I := splitI ibox40 2 2876378952539661699798013183108880385755656570405251553689600000000000000000000000 true
private noncomputable def ibox43 : Fin 4 → FixedTape.I := splitI ibox37 1 299622807556214760395626373240508373516214226083880370176000000000000000000000000 true
private noncomputable def ibox44 : Fin 4 → FixedTape.I := splitI ibox43 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox45 : Fin 4 → FixedTape.I := splitI ibox43 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox46 : Fin 4 → FixedTape.I := splitI ibox45 2 2876378952539661699798013183108880385755656570405251553689600000000000000000000000 false
private noncomputable def ibox47 : Fin 4 → FixedTape.I := splitI ibox45 2 2876378952539661699798013183108880385755656570405251553689600000000000000000000000 true
private noncomputable def ibox48 : Fin 4 → FixedTape.I := splitI ibox36 1 359547369067457712474751647888610048219457071300656444211200000000000000000000000 true
private noncomputable def ibox49 : Fin 4 → FixedTape.I := splitI ibox48 1 419471930578700664553876922536711722922699916517432518246400000000000000000000000 false
private noncomputable def ibox50 : Fin 4 → FixedTape.I := splitI ibox49 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox51 : Fin 4 → FixedTape.I := splitI ibox49 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox52 : Fin 4 → FixedTape.I := splitI ibox51 1 389509649823079188514314285212660885571078493909044481228800000000000000000000000 false
private noncomputable def ibox53 : Fin 4 → FixedTape.I := splitI ibox51 1 389509649823079188514314285212660885571078493909044481228800000000000000000000000 true
private noncomputable def ibox54 : Fin 4 → FixedTape.I := splitI ibox48 1 419471930578700664553876922536711722922699916517432518246400000000000000000000000 true
private noncomputable def ibox55 : Fin 4 → FixedTape.I := splitI ibox54 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox56 : Fin 4 → FixedTape.I := splitI ibox54 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox57 : Fin 4 → FixedTape.I := splitI ibox56 1 449434211334322140593439559860762560274321339125820555264000000000000000000000000 false
private noncomputable def ibox58 : Fin 4 → FixedTape.I := splitI ibox56 1 449434211334322140593439559860762560274321339125820555264000000000000000000000000 true
private noncomputable def ibox59 : Fin 4 → FixedTape.I := splitI ibox3 1 479396492089943616633002197184813397625942761734208592281600000000000000000000000 true
private noncomputable def ibox60 : Fin 4 → FixedTape.I := splitI ibox59 1 719094738134915424949503295777220096438914142601312888422400000000000000000000000 false
private noncomputable def ibox61 : Fin 4 → FixedTape.I := splitI ibox60 1 599245615112429520791252746481016747032428452167760740352000000000000000000000000 false
private noncomputable def ibox62 : Fin 4 → FixedTape.I := splitI ibox61 1 539321053601186568712127471832915072329185606950984666316800000000000000000000000 false
private noncomputable def ibox63 : Fin 4 → FixedTape.I := splitI ibox62 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox64 : Fin 4 → FixedTape.I := splitI ibox62 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox65 : Fin 4 → FixedTape.I := splitI ibox64 1 509358772845565092672564834508864234977564184342596629299200000000000000000000000 false
private noncomputable def ibox66 : Fin 4 → FixedTape.I := splitI ibox64 1 509358772845565092672564834508864234977564184342596629299200000000000000000000000 true
private noncomputable def ibox67 : Fin 4 → FixedTape.I := splitI ibox61 1 539321053601186568712127471832915072329185606950984666316800000000000000000000000 true
private noncomputable def ibox68 : Fin 4 → FixedTape.I := splitI ibox67 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox69 : Fin 4 → FixedTape.I := splitI ibox67 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox70 : Fin 4 → FixedTape.I := splitI ibox69 1 569283334356808044751690109156965909680807029559372703334400000000000000000000000 false
private noncomputable def ibox71 : Fin 4 → FixedTape.I := splitI ibox69 1 569283334356808044751690109156965909680807029559372703334400000000000000000000000 true
private noncomputable def ibox72 : Fin 4 → FixedTape.I := splitI ibox60 1 599245615112429520791252746481016747032428452167760740352000000000000000000000000 true
private noncomputable def ibox73 : Fin 4 → FixedTape.I := splitI ibox72 1 659170176623672472870378021129118421735671297384536814387200000000000000000000000 false
private noncomputable def ibox74 : Fin 4 → FixedTape.I := splitI ibox73 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox75 : Fin 4 → FixedTape.I := splitI ibox73 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox76 : Fin 4 → FixedTape.I := splitI ibox75 1 629207895868050996830815383805067584384049874776148777369600000000000000000000000 false
private noncomputable def ibox77 : Fin 4 → FixedTape.I := splitI ibox75 1 629207895868050996830815383805067584384049874776148777369600000000000000000000000 true
private noncomputable def ibox78 : Fin 4 → FixedTape.I := splitI ibox72 1 659170176623672472870378021129118421735671297384536814387200000000000000000000000 true
private noncomputable def ibox79 : Fin 4 → FixedTape.I := splitI ibox78 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox80 : Fin 4 → FixedTape.I := splitI ibox78 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox81 : Fin 4 → FixedTape.I := splitI ibox80 1 689132457379293948909940658453169259087292719992924851404800000000000000000000000 false
private noncomputable def ibox82 : Fin 4 → FixedTape.I := splitI ibox80 1 689132457379293948909940658453169259087292719992924851404800000000000000000000000 true
private noncomputable def ibox83 : Fin 4 → FixedTape.I := splitI ibox59 1 719094738134915424949503295777220096438914142601312888422400000000000000000000000 true
private noncomputable def ibox84 : Fin 4 → FixedTape.I := splitI ibox83 1 838943861157401329107753845073423445845399833034865036492800000000000000000000000 false
private noncomputable def ibox85 : Fin 4 → FixedTape.I := splitI ibox84 1 779019299646158377028628570425321771142156987818088962457600000000000000000000000 false
private noncomputable def ibox86 : Fin 4 → FixedTape.I := splitI ibox85 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox87 : Fin 4 → FixedTape.I := splitI ibox85 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox88 : Fin 4 → FixedTape.I := splitI ibox87 1 749057018890536900989065933101270933790535565209700925440000000000000000000000000 false
private noncomputable def ibox89 : Fin 4 → FixedTape.I := splitI ibox87 1 749057018890536900989065933101270933790535565209700925440000000000000000000000000 true
private noncomputable def ibox90 : Fin 4 → FixedTape.I := splitI ibox84 1 779019299646158377028628570425321771142156987818088962457600000000000000000000000 true
private noncomputable def ibox91 : Fin 4 → FixedTape.I := splitI ibox90 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox92 : Fin 4 → FixedTape.I := splitI ibox90 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox93 : Fin 4 → FixedTape.I := splitI ibox92 1 808981580401779853068191207749372608493778410426476999475200000000000000000000000 false
private noncomputable def ibox94 : Fin 4 → FixedTape.I := splitI ibox92 1 808981580401779853068191207749372608493778410426476999475200000000000000000000000 true
private noncomputable def ibox95 : Fin 4 → FixedTape.I := splitI ibox83 1 838943861157401329107753845073423445845399833034865036492800000000000000000000000 true
private noncomputable def ibox96 : Fin 4 → FixedTape.I := splitI ibox95 1 898868422668644281186879119721525120548642678251641110528000000000000000000000000 false
private noncomputable def ibox97 : Fin 4 → FixedTape.I := splitI ibox96 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox98 : Fin 4 → FixedTape.I := splitI ibox96 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox99 : Fin 4 → FixedTape.I := splitI ibox98 1 868906141913022805147316482397474283197021255643253073510400000000000000000000000 false
private noncomputable def ibox100 : Fin 4 → FixedTape.I := splitI ibox98 1 868906141913022805147316482397474283197021255643253073510400000000000000000000000 true
private noncomputable def ibox101 : Fin 4 → FixedTape.I := splitI ibox95 1 898868422668644281186879119721525120548642678251641110528000000000000000000000000 true
private noncomputable def ibox102 : Fin 4 → FixedTape.I := splitI ibox101 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox103 : Fin 4 → FixedTape.I := splitI ibox101 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox104 : Fin 4 → FixedTape.I := splitI ibox103 1 928830703424265757226441757045575957900264100860029147545600000000000000000000000 false
private noncomputable def ibox105 : Fin 4 → FixedTape.I := splitI ibox103 1 928830703424265757226441757045575957900264100860029147545600000000000000000000000 true
private noncomputable def ibox106 : Fin 4 → FixedTape.I := splitI ibox2 1 958792984179887233266004394369626795251885523468417184563200000000000000000000000 true
private noncomputable def ibox107 : Fin 4 → FixedTape.I := splitI ibox106 1 1438189476269830849899006591554440192877828285202625776844800000000000000000000000 false
private noncomputable def ibox108 : Fin 4 → FixedTape.I := splitI ibox107 1 1198491230224859041582505492962033494064856904335521480704000000000000000000000000 false
private noncomputable def ibox109 : Fin 4 → FixedTape.I := splitI ibox108 1 1078642107202373137424254943665830144658371213901969332633600000000000000000000000 false
private noncomputable def ibox110 : Fin 4 → FixedTape.I := splitI ibox109 1 1018717545691130185345129669017728469955128368685193258598400000000000000000000000 false
private noncomputable def ibox111 : Fin 4 → FixedTape.I := splitI ibox110 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox112 : Fin 4 → FixedTape.I := splitI ibox110 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox113 : Fin 4 → FixedTape.I := splitI ibox112 1 988755264935508709305567031693677632603506946076805221580800000000000000000000000 false
private noncomputable def ibox114 : Fin 4 → FixedTape.I := splitI ibox112 1 988755264935508709305567031693677632603506946076805221580800000000000000000000000 true
private noncomputable def ibox115 : Fin 4 → FixedTape.I := splitI ibox109 1 1018717545691130185345129669017728469955128368685193258598400000000000000000000000 true
private noncomputable def ibox116 : Fin 4 → FixedTape.I := splitI ibox115 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox117 : Fin 4 → FixedTape.I := splitI ibox115 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox118 : Fin 4 → FixedTape.I := splitI ibox117 1 1048679826446751661384692306341779307306749791293581295616000000000000000000000000 false
private noncomputable def ibox119 : Fin 4 → FixedTape.I := splitI ibox117 1 1048679826446751661384692306341779307306749791293581295616000000000000000000000000 true
private noncomputable def ibox120 : Fin 4 → FixedTape.I := splitI ibox108 1 1078642107202373137424254943665830144658371213901969332633600000000000000000000000 true
private noncomputable def ibox121 : Fin 4 → FixedTape.I := splitI ibox120 1 1138566668713616089503380218313931819361614059118745406668800000000000000000000000 false
private noncomputable def ibox122 : Fin 4 → FixedTape.I := splitI ibox121 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox123 : Fin 4 → FixedTape.I := splitI ibox121 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox124 : Fin 4 → FixedTape.I := splitI ibox123 1 1108604387957994613463817580989880982009992636510357369651200000000000000000000000 false
private noncomputable def ibox125 : Fin 4 → FixedTape.I := splitI ibox123 1 1108604387957994613463817580989880982009992636510357369651200000000000000000000000 true
private noncomputable def ibox126 : Fin 4 → FixedTape.I := splitI ibox120 1 1138566668713616089503380218313931819361614059118745406668800000000000000000000000 true
private noncomputable def ibox127 : Fin 4 → FixedTape.I := splitI ibox126 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox128 : Fin 4 → FixedTape.I := splitI ibox126 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox129 : Fin 4 → FixedTape.I := splitI ibox128 1 1168528949469237565542942855637982656713235481727133443686400000000000000000000000 false
private noncomputable def ibox130 : Fin 4 → FixedTape.I := splitI ibox128 1 1168528949469237565542942855637982656713235481727133443686400000000000000000000000 true
private noncomputable def ibox131 : Fin 4 → FixedTape.I := splitI ibox107 1 1198491230224859041582505492962033494064856904335521480704000000000000000000000000 true
private noncomputable def ibox132 : Fin 4 → FixedTape.I := splitI ibox131 1 1318340353247344945740756042258236843471342594769073628774400000000000000000000000 false
private noncomputable def ibox133 : Fin 4 → FixedTape.I := splitI ibox132 1 1258415791736101993661630767610135168768099749552297554739200000000000000000000000 false
private noncomputable def ibox134 : Fin 4 → FixedTape.I := splitI ibox133 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox135 : Fin 4 → FixedTape.I := splitI ibox133 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox136 : Fin 4 → FixedTape.I := splitI ibox135 1 1228453510980480517622068130286084331416478326943909517721600000000000000000000000 false
private noncomputable def ibox137 : Fin 4 → FixedTape.I := splitI ibox135 1 1228453510980480517622068130286084331416478326943909517721600000000000000000000000 true
private noncomputable def ibox138 : Fin 4 → FixedTape.I := splitI ibox132 1 1258415791736101993661630767610135168768099749552297554739200000000000000000000000 true
private noncomputable def ibox139 : Fin 4 → FixedTape.I := splitI ibox138 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox140 : Fin 4 → FixedTape.I := splitI ibox138 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox141 : Fin 4 → FixedTape.I := splitI ibox140 1 1288378072491723469701193404934186006119721172160685591756800000000000000000000000 false
private noncomputable def ibox142 : Fin 4 → FixedTape.I := splitI ibox140 1 1288378072491723469701193404934186006119721172160685591756800000000000000000000000 true
private noncomputable def ibox143 : Fin 4 → FixedTape.I := splitI ibox131 1 1318340353247344945740756042258236843471342594769073628774400000000000000000000000 true
private noncomputable def ibox144 : Fin 4 → FixedTape.I := splitI ibox143 1 1378264914758587897819881316906338518174585439985849702809600000000000000000000000 false
private noncomputable def ibox145 : Fin 4 → FixedTape.I := splitI ibox144 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox146 : Fin 4 → FixedTape.I := splitI ibox144 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox147 : Fin 4 → FixedTape.I := splitI ibox146 1 1348302634002966421780318679582287680822964017377461665792000000000000000000000000 false
private noncomputable def ibox148 : Fin 4 → FixedTape.I := splitI ibox146 1 1348302634002966421780318679582287680822964017377461665792000000000000000000000000 true
private noncomputable def ibox149 : Fin 4 → FixedTape.I := splitI ibox143 1 1378264914758587897819881316906338518174585439985849702809600000000000000000000000 true
private noncomputable def ibox150 : Fin 4 → FixedTape.I := splitI ibox149 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox151 : Fin 4 → FixedTape.I := splitI ibox149 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox152 : Fin 4 → FixedTape.I := splitI ibox151 1 1408227195514209373859443954230389355526206862594237739827200000000000000000000000 false
private noncomputable def ibox153 : Fin 4 → FixedTape.I := splitI ibox151 1 1408227195514209373859443954230389355526206862594237739827200000000000000000000000 true
private noncomputable def ibox154 : Fin 4 → FixedTape.I := splitI ibox106 1 1438189476269830849899006591554440192877828285202625776844800000000000000000000000 true
private noncomputable def ibox155 : Fin 4 → FixedTape.I := splitI ibox154 1 1677887722314802658215507690146846891690799666069730072985600000000000000000000000 false
private noncomputable def ibox156 : Fin 4 → FixedTape.I := splitI ibox155 1 1558038599292316754057257140850643542284313975636177924915200000000000000000000000 false
private noncomputable def ibox157 : Fin 4 → FixedTape.I := splitI ibox156 1 1498114037781073801978131866202541867581071130419401850880000000000000000000000000 false
private noncomputable def ibox158 : Fin 4 → FixedTape.I := splitI ibox157 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox159 : Fin 4 → FixedTape.I := splitI ibox157 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox160 : Fin 4 → FixedTape.I := splitI ibox159 1 1468151757025452325938569228878491030229449707811013813862400000000000000000000000 false
private noncomputable def ibox161 : Fin 4 → FixedTape.I := splitI ibox159 1 1468151757025452325938569228878491030229449707811013813862400000000000000000000000 true
private noncomputable def ibox162 : Fin 4 → FixedTape.I := splitI ibox156 1 1498114037781073801978131866202541867581071130419401850880000000000000000000000000 true
private noncomputable def ibox163 : Fin 4 → FixedTape.I := splitI ibox162 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox164 : Fin 4 → FixedTape.I := splitI ibox162 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox165 : Fin 4 → FixedTape.I := splitI ibox164 1 1528076318536695278017694503526592704932692553027789887897600000000000000000000000 false
private noncomputable def ibox166 : Fin 4 → FixedTape.I := splitI ibox164 1 1528076318536695278017694503526592704932692553027789887897600000000000000000000000 true
private noncomputable def ibox167 : Fin 4 → FixedTape.I := splitI ibox155 1 1558038599292316754057257140850643542284313975636177924915200000000000000000000000 true
private noncomputable def ibox168 : Fin 4 → FixedTape.I := splitI ibox167 1 1617963160803559706136382415498745216987556820852953998950400000000000000000000000 false
private noncomputable def ibox169 : Fin 4 → FixedTape.I := splitI ibox168 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox170 : Fin 4 → FixedTape.I := splitI ibox168 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox171 : Fin 4 → FixedTape.I := splitI ibox170 1 1588000880047938230096819778174694379635935398244565961932800000000000000000000000 false
private noncomputable def ibox172 : Fin 4 → FixedTape.I := splitI ibox170 1 1588000880047938230096819778174694379635935398244565961932800000000000000000000000 true
private noncomputable def ibox173 : Fin 4 → FixedTape.I := splitI ibox167 1 1617963160803559706136382415498745216987556820852953998950400000000000000000000000 true
private noncomputable def ibox174 : Fin 4 → FixedTape.I := splitI ibox173 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox175 : Fin 4 → FixedTape.I := splitI ibox173 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox176 : Fin 4 → FixedTape.I := splitI ibox175 1 1647925441559181182175945052822796054339178243461342035968000000000000000000000000 false
private noncomputable def ibox177 : Fin 4 → FixedTape.I := splitI ibox175 1 1647925441559181182175945052822796054339178243461342035968000000000000000000000000 true
private noncomputable def ibox178 : Fin 4 → FixedTape.I := splitI ibox154 1 1677887722314802658215507690146846891690799666069730072985600000000000000000000000 true
private noncomputable def ibox179 : Fin 4 → FixedTape.I := splitI ibox178 1 1797736845337288562373758239443050241097285356503282221056000000000000000000000000 false
private noncomputable def ibox180 : Fin 4 → FixedTape.I := splitI ibox179 1 1737812283826045610294632964794948566394042511286506147020800000000000000000000000 false
private noncomputable def ibox181 : Fin 4 → FixedTape.I := splitI ibox180 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox182 : Fin 4 → FixedTape.I := splitI ibox180 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox183 : Fin 4 → FixedTape.I := splitI ibox182 1 1707850003070424134255070327470897729042421088678118110003200000000000000000000000 false
private noncomputable def ibox184 : Fin 4 → FixedTape.I := splitI ibox182 1 1707850003070424134255070327470897729042421088678118110003200000000000000000000000 true
private noncomputable def ibox185 : Fin 4 → FixedTape.I := splitI ibox179 1 1737812283826045610294632964794948566394042511286506147020800000000000000000000000 true
private noncomputable def ibox186 : Fin 4 → FixedTape.I := splitI ibox185 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox187 : Fin 4 → FixedTape.I := splitI ibox185 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox188 : Fin 4 → FixedTape.I := splitI ibox187 1 1767774564581667086334195602118999403745663933894894184038400000000000000000000000 false
private noncomputable def ibox189 : Fin 4 → FixedTape.I := splitI ibox187 1 1767774564581667086334195602118999403745663933894894184038400000000000000000000000 true
private noncomputable def ibox190 : Fin 4 → FixedTape.I := splitI ibox178 1 1797736845337288562373758239443050241097285356503282221056000000000000000000000000 true
private noncomputable def ibox191 : Fin 4 → FixedTape.I := splitI ibox190 1 1857661406848531514452883514091151915800528201720058295091200000000000000000000000 false
private noncomputable def ibox192 : Fin 4 → FixedTape.I := splitI ibox191 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 false
private noncomputable def ibox193 : Fin 4 → FixedTape.I := splitI ibox191 2 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox194 : Fin 4 → FixedTape.I := splitI ibox193 1 1827699126092910038413320876767101078448906779111670258073600000000000000000000000 false
private noncomputable def ibox195 : Fin 4 → FixedTape.I := splitI ibox193 1 1827699126092910038413320876767101078448906779111670258073600000000000000000000000 true
private noncomputable def ibox196 : Fin 4 → FixedTape.I := splitI ibox190 1 1857661406848531514452883514091151915800528201720058295091200000000000000000000000 true
private noncomputable def ibox197 : Fin 4 → FixedTape.I := splitI ibox196 1 1887623687604152990492446151415202753152149624328446332108800000000000000000000000 false
private noncomputable def ibox198 : Fin 4 → FixedTape.I := splitI ibox196 1 1887623687604152990492446151415202753152149624328446332108800000000000000000000000 true
private noncomputable def ibox199 : Fin 4 → FixedTape.I := splitI ibox1 1 1917585968359774466532008788739253590503771046936834369126400000000000000000000000 true
private noncomputable def ibox200 : Fin 4 → FixedTape.I := splitI ibox199 1 2876378952539661699798013183108880385755656570405251553689600000000000000000000000 false
private noncomputable def ibox201 : Fin 4 → FixedTape.I := splitI ibox200 1 2396982460449718083165010985924066988129713808671042961408000000000000000000000000 false
private noncomputable def ibox202 : Fin 4 → FixedTape.I := splitI ibox201 1 2157284214404746274848509887331660289316742427803938665267200000000000000000000000 false
private noncomputable def ibox203 : Fin 4 → FixedTape.I := splitI ibox202 1 2037435091382260370690259338035456939910256737370386517196800000000000000000000000 false
private noncomputable def ibox204 : Fin 4 → FixedTape.I := splitI ibox203 1 1977510529871017418611134063387355265207013892153610443161600000000000000000000000 false
private noncomputable def ibox205 : Fin 4 → FixedTape.I := splitI ibox204 1 1947548249115395942571571426063304427855392469545222406144000000000000000000000000 false
private noncomputable def ibox206 : Fin 4 → FixedTape.I := splitI ibox204 1 1947548249115395942571571426063304427855392469545222406144000000000000000000000000 true
private noncomputable def ibox207 : Fin 4 → FixedTape.I := splitI ibox203 1 1977510529871017418611134063387355265207013892153610443161600000000000000000000000 true
private noncomputable def ibox208 : Fin 4 → FixedTape.I := splitI ibox207 1 2007472810626638894650696700711406102558635314761998480179200000000000000000000000 false
private noncomputable def ibox209 : Fin 4 → FixedTape.I := splitI ibox207 1 2007472810626638894650696700711406102558635314761998480179200000000000000000000000 true
private noncomputable def ibox210 : Fin 4 → FixedTape.I := splitI ibox202 1 2037435091382260370690259338035456939910256737370386517196800000000000000000000000 true
private noncomputable def ibox211 : Fin 4 → FixedTape.I := splitI ibox210 1 2097359652893503322769384612683558614613499582587162591232000000000000000000000000 false
private noncomputable def ibox212 : Fin 4 → FixedTape.I := splitI ibox211 1 2067397372137881846729821975359507777261878159978774554214400000000000000000000000 false
private noncomputable def ibox213 : Fin 4 → FixedTape.I := splitI ibox211 1 2067397372137881846729821975359507777261878159978774554214400000000000000000000000 true
private noncomputable def ibox214 : Fin 4 → FixedTape.I := splitI ibox210 1 2097359652893503322769384612683558614613499582587162591232000000000000000000000000 true
private noncomputable def ibox215 : Fin 4 → FixedTape.I := splitI ibox214 1 2127321933649124798808947250007609451965121005195550628249600000000000000000000000 false
private noncomputable def ibox216 : Fin 4 → FixedTape.I := splitI ibox214 1 2127321933649124798808947250007609451965121005195550628249600000000000000000000000 true
private noncomputable def ibox217 : Fin 4 → FixedTape.I := splitI ibox201 1 2157284214404746274848509887331660289316742427803938665267200000000000000000000000 true
private noncomputable def ibox218 : Fin 4 → FixedTape.I := splitI ibox217 1 2277133337427232179006760436627863638723228118237490813337600000000000000000000000 false
private noncomputable def ibox219 : Fin 4 → FixedTape.I := splitI ibox218 1 2217208775915989226927635161979761964019985273020714739302400000000000000000000000 false
private noncomputable def ibox220 : Fin 4 → FixedTape.I := splitI ibox219 1 2187246495160367750888072524655711126668363850412326702284800000000000000000000000 false
private noncomputable def ibox221 : Fin 4 → FixedTape.I := splitI ibox219 1 2187246495160367750888072524655711126668363850412326702284800000000000000000000000 true
private noncomputable def ibox222 : Fin 4 → FixedTape.I := splitI ibox218 1 2217208775915989226927635161979761964019985273020714739302400000000000000000000000 true
private noncomputable def ibox223 : Fin 4 → FixedTape.I := splitI ibox222 1 2247171056671610702967197799303812801371606695629102776320000000000000000000000000 false
private noncomputable def ibox224 : Fin 4 → FixedTape.I := splitI ibox222 1 2247171056671610702967197799303812801371606695629102776320000000000000000000000000 true
private noncomputable def ibox225 : Fin 4 → FixedTape.I := splitI ibox217 1 2277133337427232179006760436627863638723228118237490813337600000000000000000000000 true
private noncomputable def ibox226 : Fin 4 → FixedTape.I := splitI ibox225 1 2337057898938475131085885711275965313426470963454266887372800000000000000000000000 false
private noncomputable def ibox227 : Fin 4 → FixedTape.I := splitI ibox226 1 2307095618182853655046323073951914476074849540845878850355200000000000000000000000 false
private noncomputable def ibox228 : Fin 4 → FixedTape.I := splitI ibox226 1 2307095618182853655046323073951914476074849540845878850355200000000000000000000000 true
private noncomputable def ibox229 : Fin 4 → FixedTape.I := splitI ibox225 1 2337057898938475131085885711275965313426470963454266887372800000000000000000000000 true
private noncomputable def ibox230 : Fin 4 → FixedTape.I := splitI ibox229 1 2367020179694096607125448348600016150778092386062654924390400000000000000000000000 false
private noncomputable def ibox231 : Fin 4 → FixedTape.I := splitI ibox229 1 2367020179694096607125448348600016150778092386062654924390400000000000000000000000 true
private noncomputable def ibox232 : Fin 4 → FixedTape.I := splitI ibox200 1 2396982460449718083165010985924066988129713808671042961408000000000000000000000000 true
private noncomputable def ibox233 : Fin 4 → FixedTape.I := splitI ibox232 1 2636680706494689891481512084516473686942685189538147257548800000000000000000000000 false
private noncomputable def ibox234 : Fin 4 → FixedTape.I := splitI ibox233 1 2516831583472203987323261535220270337536199499104595109478400000000000000000000000 false
private noncomputable def ibox235 : Fin 4 → FixedTape.I := splitI ibox234 1 2456907021960961035244136260572168662832956653887819035443200000000000000000000000 false
private noncomputable def ibox236 : Fin 4 → FixedTape.I := splitI ibox235 1 2426944741205339559204573623248117825481335231279430998425600000000000000000000000 false
private noncomputable def ibox237 : Fin 4 → FixedTape.I := splitI ibox235 1 2426944741205339559204573623248117825481335231279430998425600000000000000000000000 true
private noncomputable def ibox238 : Fin 4 → FixedTape.I := splitI ibox234 1 2456907021960961035244136260572168662832956653887819035443200000000000000000000000 true
private noncomputable def ibox239 : Fin 4 → FixedTape.I := splitI ibox238 1 2486869302716582511283698897896219500184578076496207072460800000000000000000000000 false
private noncomputable def ibox240 : Fin 4 → FixedTape.I := splitI ibox238 1 2486869302716582511283698897896219500184578076496207072460800000000000000000000000 true
private noncomputable def ibox241 : Fin 4 → FixedTape.I := splitI ibox233 1 2516831583472203987323261535220270337536199499104595109478400000000000000000000000 true
private noncomputable def ibox242 : Fin 4 → FixedTape.I := splitI ibox241 1 2576756144983446939402386809868372012239442344321371183513600000000000000000000000 false
private noncomputable def ibox243 : Fin 4 → FixedTape.I := splitI ibox242 1 2546793864227825463362824172544321174887820921712983146496000000000000000000000000 false
private noncomputable def ibox244 : Fin 4 → FixedTape.I := splitI ibox242 1 2546793864227825463362824172544321174887820921712983146496000000000000000000000000 true
private noncomputable def ibox245 : Fin 4 → FixedTape.I := splitI ibox241 1 2576756144983446939402386809868372012239442344321371183513600000000000000000000000 true
private noncomputable def ibox246 : Fin 4 → FixedTape.I := splitI ibox245 1 2606718425739068415441949447192422849591063766929759220531200000000000000000000000 false
private noncomputable def ibox247 : Fin 4 → FixedTape.I := splitI ibox245 1 2606718425739068415441949447192422849591063766929759220531200000000000000000000000 true
private noncomputable def ibox248 : Fin 4 → FixedTape.I := splitI ibox232 1 2636680706494689891481512084516473686942685189538147257548800000000000000000000000 true
private noncomputable def ibox249 : Fin 4 → FixedTape.I := splitI ibox248 1 2756529829517175795639762633812677036349170879971699405619200000000000000000000000 false
private noncomputable def ibox250 : Fin 4 → FixedTape.I := splitI ibox249 1 2696605268005932843560637359164575361645928034754923331584000000000000000000000000 false
private noncomputable def ibox251 : Fin 4 → FixedTape.I := splitI ibox250 1 2666642987250311367521074721840524524294306612146535294566400000000000000000000000 false
private noncomputable def ibox252 : Fin 4 → FixedTape.I := splitI ibox250 1 2666642987250311367521074721840524524294306612146535294566400000000000000000000000 true
private noncomputable def ibox253 : Fin 4 → FixedTape.I := splitI ibox249 1 2696605268005932843560637359164575361645928034754923331584000000000000000000000000 true
private noncomputable def ibox254 : Fin 4 → FixedTape.I := splitI ibox248 1 2756529829517175795639762633812677036349170879971699405619200000000000000000000000 true
private noncomputable def ibox255 : Fin 4 → FixedTape.I := splitI ibox254 1 2816454391028418747718887908460778711052413725188475479654400000000000000000000000 false
private noncomputable def ibox256 : Fin 4 → FixedTape.I := splitI ibox254 1 2816454391028418747718887908460778711052413725188475479654400000000000000000000000 true
private noncomputable def ibox257 : Fin 4 → FixedTape.I := splitI ibox199 1 2876378952539661699798013183108880385755656570405251553689600000000000000000000000 true
private noncomputable def ibox258 : Fin 4 → FixedTape.I := splitI ibox257 1 3355775444629605316431015380293693783381599332139460145971200000000000000000000000 false
private noncomputable def ibox259 : Fin 4 → FixedTape.I := splitI ibox258 1 3116077198584633508114514281701287084568627951272355849830400000000000000000000000 false
private noncomputable def ibox260 : Fin 4 → FixedTape.I := splitI ibox259 1 2996228075562147603956263732405083735162142260838803701760000000000000000000000000 false
private noncomputable def ibox261 : Fin 4 → FixedTape.I := splitI ibox260 1 2936303514050904651877138457756982060458899415622027627724800000000000000000000000 false
private noncomputable def ibox262 : Fin 4 → FixedTape.I := splitI ibox260 1 2936303514050904651877138457756982060458899415622027627724800000000000000000000000 true
private noncomputable def ibox263 : Fin 4 → FixedTape.I := splitI ibox259 1 2996228075562147603956263732405083735162142260838803701760000000000000000000000000 true
private noncomputable def ibox264 : Fin 4 → FixedTape.I := splitI ibox263 1 3056152637073390556035389007053185409865385106055579775795200000000000000000000000 false
private noncomputable def ibox265 : Fin 4 → FixedTape.I := splitI ibox263 1 3056152637073390556035389007053185409865385106055579775795200000000000000000000000 true
private noncomputable def ibox266 : Fin 4 → FixedTape.I := splitI ibox258 1 3116077198584633508114514281701287084568627951272355849830400000000000000000000000 true
private noncomputable def ibox267 : Fin 4 → FixedTape.I := splitI ibox266 1 3235926321607119412272764830997490433975113641705907997900800000000000000000000000 false
private noncomputable def ibox268 : Fin 4 → FixedTape.I := splitI ibox267 1 3176001760095876460193639556349388759271870796489131923865600000000000000000000000 false
private noncomputable def ibox269 : Fin 4 → FixedTape.I := splitI ibox267 1 3176001760095876460193639556349388759271870796489131923865600000000000000000000000 true
private noncomputable def ibox270 : Fin 4 → FixedTape.I := splitI ibox266 1 3235926321607119412272764830997490433975113641705907997900800000000000000000000000 true
private noncomputable def ibox271 : Fin 4 → FixedTape.I := splitI ibox270 1 3295850883118362364351890105645592108678356486922684071936000000000000000000000000 false
private noncomputable def ibox272 : Fin 4 → FixedTape.I := splitI ibox270 1 3295850883118362364351890105645592108678356486922684071936000000000000000000000000 true
private noncomputable def ibox273 : Fin 4 → FixedTape.I := splitI ibox257 1 3355775444629605316431015380293693783381599332139460145971200000000000000000000000 true
private noncomputable def ibox274 : Fin 4 → FixedTape.I := splitI ibox273 1 3595473690674577124747516478886100482194570713006564442112000000000000000000000000 false
private noncomputable def ibox275 : Fin 4 → FixedTape.I := splitI ibox274 1 3475624567652091220589265929589897132788085022573012294041600000000000000000000000 false
private noncomputable def ibox276 : Fin 4 → FixedTape.I := splitI ibox275 1 3415700006140848268510140654941795458084842177356236220006400000000000000000000000 false
private noncomputable def ibox277 : Fin 4 → FixedTape.I := splitI ibox275 1 3415700006140848268510140654941795458084842177356236220006400000000000000000000000 true
private noncomputable def ibox278 : Fin 4 → FixedTape.I := splitI ibox274 1 3475624567652091220589265929589897132788085022573012294041600000000000000000000000 true
private noncomputable def ibox279 : Fin 4 → FixedTape.I := splitI ibox278 1 3535549129163334172668391204237998807491327867789788368076800000000000000000000000 false
private noncomputable def ibox280 : Fin 4 → FixedTape.I := splitI ibox278 1 3535549129163334172668391204237998807491327867789788368076800000000000000000000000 true
private noncomputable def ibox281 : Fin 4 → FixedTape.I := splitI ibox273 1 3595473690674577124747516478886100482194570713006564442112000000000000000000000000 true
private noncomputable def ibox282 : Fin 4 → FixedTape.I := splitI ibox281 1 3715322813697063028905767028182303831601056403440116590182400000000000000000000000 false
private noncomputable def ibox283 : Fin 4 → FixedTape.I := splitI ibox282 1 3655398252185820076826641753534202156897813558223340516147200000000000000000000000 false
private noncomputable def ibox284 : Fin 4 → FixedTape.I := splitI ibox282 1 3655398252185820076826641753534202156897813558223340516147200000000000000000000000 true
private noncomputable def ibox285 : Fin 4 → FixedTape.I := splitI ibox281 1 3715322813697063028905767028182303831601056403440116590182400000000000000000000000 true
private noncomputable def ibox286 : Fin 4 → FixedTape.I := splitI ibox285 1 3775247375208305980984892302830405506304299248656892664217600000000000000000000000 false
private noncomputable def ibox287 : Fin 4 → FixedTape.I := splitI ibox285 1 3775247375208305980984892302830405506304299248656892664217600000000000000000000000 true
private noncomputable def tree287 : TapeTree := .centered (candidateRows ibox287) (candidateRows (FixedTape.midBox ibox287))
attribute [irreducible] tree287
private theorem sign_287 : 2*denominator*(computed denominator (FixedTape.midBox ibox287)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox287).gradient k).lo.natAbs ((computed denominator ibox287).gradient k).hi.natAbs : Int)*((ibox287 k).hi-(ibox287 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox287
    (computed denominator ibox287) (computed denominator (FixedTape.midBox ibox287))
    (by decide +kernel)
private theorem midpoint_even_287 : ∀ k, 2 ∣ (ibox287 k).lo+(ibox287 k).hi := by decide +kernel
private theorem accepted_287 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox287) tree287 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox287 midpoint_even_287
  simp only [tree287,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox287,candidate_valid h (FixedTape.midBox ibox287),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox287 101 (FixedTape.rowsAux denominator ibox287 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox287) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_287
private noncomputable def tree286 : TapeTree := .centered (candidateRows ibox286) (candidateRows (FixedTape.midBox ibox286))
attribute [irreducible] tree286
private theorem sign_286 : 2*denominator*(computed denominator (FixedTape.midBox ibox286)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox286).gradient k).lo.natAbs ((computed denominator ibox286).gradient k).hi.natAbs : Int)*((ibox286 k).hi-(ibox286 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox286
    (computed denominator ibox286) (computed denominator (FixedTape.midBox ibox286))
    (by decide +kernel)
private theorem midpoint_even_286 : ∀ k, 2 ∣ (ibox286 k).lo+(ibox286 k).hi := by decide +kernel
private theorem accepted_286 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox286) tree286 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox286 midpoint_even_286
  simp only [tree286,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox286,candidate_valid h (FixedTape.midBox ibox286),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox286 101 (FixedTape.rowsAux denominator ibox286 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox286) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_286
private noncomputable def tree285 : TapeTree := .split 1 (((3775247375208305980984892302830405506304299248656892664217600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree286 tree287
attribute [irreducible] tree285
private theorem accepted_285 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox285) tree285 = true := by
  simp only [tree285,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox285 1 (3775247375208305980984892302830405506304299248656892664217600000000000000000000000 : Int) false,decode_split denominator ibox285 1 (3775247375208305980984892302830405506304299248656892664217600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_286 h,accepted_287 h⟩
private noncomputable def tree284 : TapeTree := .centered (candidateRows ibox284) (candidateRows (FixedTape.midBox ibox284))
attribute [irreducible] tree284
private theorem sign_284 : 2*denominator*(computed denominator (FixedTape.midBox ibox284)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox284).gradient k).lo.natAbs ((computed denominator ibox284).gradient k).hi.natAbs : Int)*((ibox284 k).hi-(ibox284 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox284
    (computed denominator ibox284) (computed denominator (FixedTape.midBox ibox284))
    (by decide +kernel)
private theorem midpoint_even_284 : ∀ k, 2 ∣ (ibox284 k).lo+(ibox284 k).hi := by decide +kernel
private theorem accepted_284 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox284) tree284 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox284 midpoint_even_284
  simp only [tree284,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox284,candidate_valid h (FixedTape.midBox ibox284),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox284 101 (FixedTape.rowsAux denominator ibox284 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox284) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_284
private noncomputable def tree283 : TapeTree := .centered (candidateRows ibox283) (candidateRows (FixedTape.midBox ibox283))
attribute [irreducible] tree283
private theorem sign_283 : 2*denominator*(computed denominator (FixedTape.midBox ibox283)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox283).gradient k).lo.natAbs ((computed denominator ibox283).gradient k).hi.natAbs : Int)*((ibox283 k).hi-(ibox283 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox283
    (computed denominator ibox283) (computed denominator (FixedTape.midBox ibox283))
    (by decide +kernel)
private theorem midpoint_even_283 : ∀ k, 2 ∣ (ibox283 k).lo+(ibox283 k).hi := by decide +kernel
private theorem accepted_283 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox283) tree283 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox283 midpoint_even_283
  simp only [tree283,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox283,candidate_valid h (FixedTape.midBox ibox283),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox283 101 (FixedTape.rowsAux denominator ibox283 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox283) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_283
private noncomputable def tree282 : TapeTree := .split 1 (((3655398252185820076826641753534202156897813558223340516147200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree283 tree284
attribute [irreducible] tree282
private theorem accepted_282 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox282) tree282 = true := by
  simp only [tree282,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox282 1 (3655398252185820076826641753534202156897813558223340516147200000000000000000000000 : Int) false,decode_split denominator ibox282 1 (3655398252185820076826641753534202156897813558223340516147200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_283 h,accepted_284 h⟩
private noncomputable def tree281 : TapeTree := .split 1 (((3715322813697063028905767028182303831601056403440116590182400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree282 tree285
attribute [irreducible] tree281
private theorem accepted_281 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox281) tree281 = true := by
  simp only [tree281,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox281 1 (3715322813697063028905767028182303831601056403440116590182400000000000000000000000 : Int) false,decode_split denominator ibox281 1 (3715322813697063028905767028182303831601056403440116590182400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_282 h,accepted_285 h⟩
private noncomputable def tree280 : TapeTree := .centered (candidateRows ibox280) (candidateRows (FixedTape.midBox ibox280))
attribute [irreducible] tree280
private theorem sign_280 : 2*denominator*(computed denominator (FixedTape.midBox ibox280)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox280).gradient k).lo.natAbs ((computed denominator ibox280).gradient k).hi.natAbs : Int)*((ibox280 k).hi-(ibox280 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox280
    (computed denominator ibox280) (computed denominator (FixedTape.midBox ibox280))
    (by decide +kernel)
private theorem midpoint_even_280 : ∀ k, 2 ∣ (ibox280 k).lo+(ibox280 k).hi := by decide +kernel
private theorem accepted_280 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox280) tree280 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox280 midpoint_even_280
  simp only [tree280,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox280,candidate_valid h (FixedTape.midBox ibox280),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox280 101 (FixedTape.rowsAux denominator ibox280 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox280) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_280
private noncomputable def tree279 : TapeTree := .centered (candidateRows ibox279) (candidateRows (FixedTape.midBox ibox279))
attribute [irreducible] tree279
private theorem sign_279 : 2*denominator*(computed denominator (FixedTape.midBox ibox279)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox279).gradient k).lo.natAbs ((computed denominator ibox279).gradient k).hi.natAbs : Int)*((ibox279 k).hi-(ibox279 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox279
    (computed denominator ibox279) (computed denominator (FixedTape.midBox ibox279))
    (by decide +kernel)
private theorem midpoint_even_279 : ∀ k, 2 ∣ (ibox279 k).lo+(ibox279 k).hi := by decide +kernel
private theorem accepted_279 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox279) tree279 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox279 midpoint_even_279
  simp only [tree279,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox279,candidate_valid h (FixedTape.midBox ibox279),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox279 101 (FixedTape.rowsAux denominator ibox279 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox279) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_279
private noncomputable def tree278 : TapeTree := .split 1 (((3535549129163334172668391204237998807491327867789788368076800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree279 tree280
attribute [irreducible] tree278
private theorem accepted_278 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox278) tree278 = true := by
  simp only [tree278,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox278 1 (3535549129163334172668391204237998807491327867789788368076800000000000000000000000 : Int) false,decode_split denominator ibox278 1 (3535549129163334172668391204237998807491327867789788368076800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_279 h,accepted_280 h⟩
private noncomputable def tree277 : TapeTree := .centered (candidateRows ibox277) (candidateRows (FixedTape.midBox ibox277))
attribute [irreducible] tree277
private theorem sign_277 : 2*denominator*(computed denominator (FixedTape.midBox ibox277)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox277).gradient k).lo.natAbs ((computed denominator ibox277).gradient k).hi.natAbs : Int)*((ibox277 k).hi-(ibox277 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox277
    (computed denominator ibox277) (computed denominator (FixedTape.midBox ibox277))
    (by decide +kernel)
private theorem midpoint_even_277 : ∀ k, 2 ∣ (ibox277 k).lo+(ibox277 k).hi := by decide +kernel
private theorem accepted_277 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox277) tree277 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox277 midpoint_even_277
  simp only [tree277,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox277,candidate_valid h (FixedTape.midBox ibox277),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox277 101 (FixedTape.rowsAux denominator ibox277 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox277) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_277
private noncomputable def tree276 : TapeTree := .centered (candidateRows ibox276) (candidateRows (FixedTape.midBox ibox276))
attribute [irreducible] tree276
private theorem sign_276 : 2*denominator*(computed denominator (FixedTape.midBox ibox276)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox276).gradient k).lo.natAbs ((computed denominator ibox276).gradient k).hi.natAbs : Int)*((ibox276 k).hi-(ibox276 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox276
    (computed denominator ibox276) (computed denominator (FixedTape.midBox ibox276))
    (by decide +kernel)
private theorem midpoint_even_276 : ∀ k, 2 ∣ (ibox276 k).lo+(ibox276 k).hi := by decide +kernel
private theorem accepted_276 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox276) tree276 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox276 midpoint_even_276
  simp only [tree276,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox276,candidate_valid h (FixedTape.midBox ibox276),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox276 101 (FixedTape.rowsAux denominator ibox276 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox276) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_276
private noncomputable def tree275 : TapeTree := .split 1 (((3415700006140848268510140654941795458084842177356236220006400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree276 tree277
attribute [irreducible] tree275
private theorem accepted_275 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox275) tree275 = true := by
  simp only [tree275,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox275 1 (3415700006140848268510140654941795458084842177356236220006400000000000000000000000 : Int) false,decode_split denominator ibox275 1 (3415700006140848268510140654941795458084842177356236220006400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_276 h,accepted_277 h⟩
private noncomputable def tree274 : TapeTree := .split 1 (((3475624567652091220589265929589897132788085022573012294041600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree275 tree278
attribute [irreducible] tree274
private theorem accepted_274 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox274) tree274 = true := by
  simp only [tree274,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox274 1 (3475624567652091220589265929589897132788085022573012294041600000000000000000000000 : Int) false,decode_split denominator ibox274 1 (3475624567652091220589265929589897132788085022573012294041600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_275 h,accepted_278 h⟩
private noncomputable def tree273 : TapeTree := .split 1 (((3595473690674577124747516478886100482194570713006564442112000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree274 tree281
attribute [irreducible] tree273
private theorem accepted_273 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox273) tree273 = true := by
  simp only [tree273,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox273 1 (3595473690674577124747516478886100482194570713006564442112000000000000000000000000 : Int) false,decode_split denominator ibox273 1 (3595473690674577124747516478886100482194570713006564442112000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_274 h,accepted_281 h⟩
private noncomputable def tree272 : TapeTree := .centered (candidateRows ibox272) (candidateRows (FixedTape.midBox ibox272))
attribute [irreducible] tree272
private theorem sign_272 : 2*denominator*(computed denominator (FixedTape.midBox ibox272)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox272).gradient k).lo.natAbs ((computed denominator ibox272).gradient k).hi.natAbs : Int)*((ibox272 k).hi-(ibox272 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox272
    (computed denominator ibox272) (computed denominator (FixedTape.midBox ibox272))
    (by decide +kernel)
private theorem midpoint_even_272 : ∀ k, 2 ∣ (ibox272 k).lo+(ibox272 k).hi := by decide +kernel
private theorem accepted_272 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox272) tree272 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox272 midpoint_even_272
  simp only [tree272,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox272,candidate_valid h (FixedTape.midBox ibox272),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox272 101 (FixedTape.rowsAux denominator ibox272 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox272) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_272
private noncomputable def tree271 : TapeTree := .centered (candidateRows ibox271) (candidateRows (FixedTape.midBox ibox271))
attribute [irreducible] tree271
private theorem sign_271 : 2*denominator*(computed denominator (FixedTape.midBox ibox271)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox271).gradient k).lo.natAbs ((computed denominator ibox271).gradient k).hi.natAbs : Int)*((ibox271 k).hi-(ibox271 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox271
    (computed denominator ibox271) (computed denominator (FixedTape.midBox ibox271))
    (by decide +kernel)
private theorem midpoint_even_271 : ∀ k, 2 ∣ (ibox271 k).lo+(ibox271 k).hi := by decide +kernel
private theorem accepted_271 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox271) tree271 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox271 midpoint_even_271
  simp only [tree271,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox271,candidate_valid h (FixedTape.midBox ibox271),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox271 101 (FixedTape.rowsAux denominator ibox271 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox271) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_271
private noncomputable def tree270 : TapeTree := .split 1 (((3295850883118362364351890105645592108678356486922684071936000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree271 tree272
attribute [irreducible] tree270
private theorem accepted_270 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox270) tree270 = true := by
  simp only [tree270,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox270 1 (3295850883118362364351890105645592108678356486922684071936000000000000000000000000 : Int) false,decode_split denominator ibox270 1 (3295850883118362364351890105645592108678356486922684071936000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_271 h,accepted_272 h⟩
private noncomputable def tree269 : TapeTree := .centered (candidateRows ibox269) (candidateRows (FixedTape.midBox ibox269))
attribute [irreducible] tree269
private theorem sign_269 : 2*denominator*(computed denominator (FixedTape.midBox ibox269)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox269).gradient k).lo.natAbs ((computed denominator ibox269).gradient k).hi.natAbs : Int)*((ibox269 k).hi-(ibox269 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox269
    (computed denominator ibox269) (computed denominator (FixedTape.midBox ibox269))
    (by decide +kernel)
private theorem midpoint_even_269 : ∀ k, 2 ∣ (ibox269 k).lo+(ibox269 k).hi := by decide +kernel
private theorem accepted_269 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox269) tree269 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox269 midpoint_even_269
  simp only [tree269,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox269,candidate_valid h (FixedTape.midBox ibox269),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox269 101 (FixedTape.rowsAux denominator ibox269 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox269) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_269
private noncomputable def tree268 : TapeTree := .centered (candidateRows ibox268) (candidateRows (FixedTape.midBox ibox268))
attribute [irreducible] tree268
private theorem sign_268 : 2*denominator*(computed denominator (FixedTape.midBox ibox268)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox268).gradient k).lo.natAbs ((computed denominator ibox268).gradient k).hi.natAbs : Int)*((ibox268 k).hi-(ibox268 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox268
    (computed denominator ibox268) (computed denominator (FixedTape.midBox ibox268))
    (by decide +kernel)
private theorem midpoint_even_268 : ∀ k, 2 ∣ (ibox268 k).lo+(ibox268 k).hi := by decide +kernel
private theorem accepted_268 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox268) tree268 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox268 midpoint_even_268
  simp only [tree268,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox268,candidate_valid h (FixedTape.midBox ibox268),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox268 101 (FixedTape.rowsAux denominator ibox268 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox268) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_268
private noncomputable def tree267 : TapeTree := .split 1 (((3176001760095876460193639556349388759271870796489131923865600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree268 tree269
attribute [irreducible] tree267
private theorem accepted_267 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox267) tree267 = true := by
  simp only [tree267,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox267 1 (3176001760095876460193639556349388759271870796489131923865600000000000000000000000 : Int) false,decode_split denominator ibox267 1 (3176001760095876460193639556349388759271870796489131923865600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_268 h,accepted_269 h⟩
private noncomputable def tree266 : TapeTree := .split 1 (((3235926321607119412272764830997490433975113641705907997900800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree267 tree270
attribute [irreducible] tree266
private theorem accepted_266 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox266) tree266 = true := by
  simp only [tree266,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox266 1 (3235926321607119412272764830997490433975113641705907997900800000000000000000000000 : Int) false,decode_split denominator ibox266 1 (3235926321607119412272764830997490433975113641705907997900800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_267 h,accepted_270 h⟩
private noncomputable def tree265 : TapeTree := .centered (candidateRows ibox265) (candidateRows (FixedTape.midBox ibox265))
attribute [irreducible] tree265
private theorem sign_265 : 2*denominator*(computed denominator (FixedTape.midBox ibox265)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox265).gradient k).lo.natAbs ((computed denominator ibox265).gradient k).hi.natAbs : Int)*((ibox265 k).hi-(ibox265 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox265
    (computed denominator ibox265) (computed denominator (FixedTape.midBox ibox265))
    (by decide +kernel)
private theorem midpoint_even_265 : ∀ k, 2 ∣ (ibox265 k).lo+(ibox265 k).hi := by decide +kernel
private theorem accepted_265 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox265) tree265 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox265 midpoint_even_265
  simp only [tree265,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox265,candidate_valid h (FixedTape.midBox ibox265),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox265 101 (FixedTape.rowsAux denominator ibox265 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox265) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_265
private noncomputable def tree264 : TapeTree := .centered (candidateRows ibox264) (candidateRows (FixedTape.midBox ibox264))
attribute [irreducible] tree264
private theorem sign_264 : 2*denominator*(computed denominator (FixedTape.midBox ibox264)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox264).gradient k).lo.natAbs ((computed denominator ibox264).gradient k).hi.natAbs : Int)*((ibox264 k).hi-(ibox264 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox264
    (computed denominator ibox264) (computed denominator (FixedTape.midBox ibox264))
    (by decide +kernel)
private theorem midpoint_even_264 : ∀ k, 2 ∣ (ibox264 k).lo+(ibox264 k).hi := by decide +kernel
private theorem accepted_264 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox264) tree264 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox264 midpoint_even_264
  simp only [tree264,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox264,candidate_valid h (FixedTape.midBox ibox264),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox264 101 (FixedTape.rowsAux denominator ibox264 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox264) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_264
private noncomputable def tree263 : TapeTree := .split 1 (((3056152637073390556035389007053185409865385106055579775795200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree264 tree265
attribute [irreducible] tree263
private theorem accepted_263 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox263) tree263 = true := by
  simp only [tree263,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox263 1 (3056152637073390556035389007053185409865385106055579775795200000000000000000000000 : Int) false,decode_split denominator ibox263 1 (3056152637073390556035389007053185409865385106055579775795200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_264 h,accepted_265 h⟩
private noncomputable def tree262 : TapeTree := .centered (candidateRows ibox262) (candidateRows (FixedTape.midBox ibox262))
attribute [irreducible] tree262
private theorem sign_262 : 2*denominator*(computed denominator (FixedTape.midBox ibox262)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox262).gradient k).lo.natAbs ((computed denominator ibox262).gradient k).hi.natAbs : Int)*((ibox262 k).hi-(ibox262 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox262
    (computed denominator ibox262) (computed denominator (FixedTape.midBox ibox262))
    (by decide +kernel)
private theorem midpoint_even_262 : ∀ k, 2 ∣ (ibox262 k).lo+(ibox262 k).hi := by decide +kernel
private theorem accepted_262 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox262) tree262 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox262 midpoint_even_262
  simp only [tree262,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox262,candidate_valid h (FixedTape.midBox ibox262),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox262 101 (FixedTape.rowsAux denominator ibox262 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox262) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_262
private noncomputable def tree261 : TapeTree := .centered (candidateRows ibox261) (candidateRows (FixedTape.midBox ibox261))
attribute [irreducible] tree261
private theorem sign_261 : 2*denominator*(computed denominator (FixedTape.midBox ibox261)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox261).gradient k).lo.natAbs ((computed denominator ibox261).gradient k).hi.natAbs : Int)*((ibox261 k).hi-(ibox261 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox261
    (computed denominator ibox261) (computed denominator (FixedTape.midBox ibox261))
    (by decide +kernel)
private theorem midpoint_even_261 : ∀ k, 2 ∣ (ibox261 k).lo+(ibox261 k).hi := by decide +kernel
private theorem accepted_261 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox261) tree261 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox261 midpoint_even_261
  simp only [tree261,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox261,candidate_valid h (FixedTape.midBox ibox261),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox261 101 (FixedTape.rowsAux denominator ibox261 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox261) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_261
private noncomputable def tree260 : TapeTree := .split 1 (((2936303514050904651877138457756982060458899415622027627724800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree261 tree262
attribute [irreducible] tree260
private theorem accepted_260 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox260) tree260 = true := by
  simp only [tree260,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox260 1 (2936303514050904651877138457756982060458899415622027627724800000000000000000000000 : Int) false,decode_split denominator ibox260 1 (2936303514050904651877138457756982060458899415622027627724800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_261 h,accepted_262 h⟩
private noncomputable def tree259 : TapeTree := .split 1 (((2996228075562147603956263732405083735162142260838803701760000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree260 tree263
attribute [irreducible] tree259
private theorem accepted_259 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox259) tree259 = true := by
  simp only [tree259,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox259 1 (2996228075562147603956263732405083735162142260838803701760000000000000000000000000 : Int) false,decode_split denominator ibox259 1 (2996228075562147603956263732405083735162142260838803701760000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_260 h,accepted_263 h⟩
private noncomputable def tree258 : TapeTree := .split 1 (((3116077198584633508114514281701287084568627951272355849830400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree259 tree266
attribute [irreducible] tree258
private theorem accepted_258 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox258) tree258 = true := by
  simp only [tree258,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox258 1 (3116077198584633508114514281701287084568627951272355849830400000000000000000000000 : Int) false,decode_split denominator ibox258 1 (3116077198584633508114514281701287084568627951272355849830400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_259 h,accepted_266 h⟩
private noncomputable def tree257 : TapeTree := .split 1 (((3355775444629605316431015380293693783381599332139460145971200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree258 tree273
attribute [irreducible] tree257
private theorem accepted_257 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox257) tree257 = true := by
  simp only [tree257,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox257 1 (3355775444629605316431015380293693783381599332139460145971200000000000000000000000 : Int) false,decode_split denominator ibox257 1 (3355775444629605316431015380293693783381599332139460145971200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_258 h,accepted_273 h⟩
private noncomputable def tree256 : TapeTree := .centered (candidateRows ibox256) (candidateRows (FixedTape.midBox ibox256))
attribute [irreducible] tree256
private theorem sign_256 : 2*denominator*(computed denominator (FixedTape.midBox ibox256)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox256).gradient k).lo.natAbs ((computed denominator ibox256).gradient k).hi.natAbs : Int)*((ibox256 k).hi-(ibox256 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox256
    (computed denominator ibox256) (computed denominator (FixedTape.midBox ibox256))
    (by decide +kernel)
private theorem midpoint_even_256 : ∀ k, 2 ∣ (ibox256 k).lo+(ibox256 k).hi := by decide +kernel
private theorem accepted_256 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox256) tree256 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox256 midpoint_even_256
  simp only [tree256,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox256,candidate_valid h (FixedTape.midBox ibox256),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox256 101 (FixedTape.rowsAux denominator ibox256 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox256) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_256
private noncomputable def tree255 : TapeTree := .centered (candidateRows ibox255) (candidateRows (FixedTape.midBox ibox255))
attribute [irreducible] tree255
private theorem sign_255 : 2*denominator*(computed denominator (FixedTape.midBox ibox255)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox255).gradient k).lo.natAbs ((computed denominator ibox255).gradient k).hi.natAbs : Int)*((ibox255 k).hi-(ibox255 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox255
    (computed denominator ibox255) (computed denominator (FixedTape.midBox ibox255))
    (by decide +kernel)
private theorem midpoint_even_255 : ∀ k, 2 ∣ (ibox255 k).lo+(ibox255 k).hi := by decide +kernel
private theorem accepted_255 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox255) tree255 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox255 midpoint_even_255
  simp only [tree255,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox255,candidate_valid h (FixedTape.midBox ibox255),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox255 101 (FixedTape.rowsAux denominator ibox255 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox255) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_255
private noncomputable def tree254 : TapeTree := .split 1 (((2816454391028418747718887908460778711052413725188475479654400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree255 tree256
attribute [irreducible] tree254
private theorem accepted_254 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox254) tree254 = true := by
  simp only [tree254,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox254 1 (2816454391028418747718887908460778711052413725188475479654400000000000000000000000 : Int) false,decode_split denominator ibox254 1 (2816454391028418747718887908460778711052413725188475479654400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_255 h,accepted_256 h⟩
private noncomputable def tree253 : TapeTree := .centered (candidateRows ibox253) (candidateRows (FixedTape.midBox ibox253))
attribute [irreducible] tree253
private theorem sign_253 : 2*denominator*(computed denominator (FixedTape.midBox ibox253)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox253).gradient k).lo.natAbs ((computed denominator ibox253).gradient k).hi.natAbs : Int)*((ibox253 k).hi-(ibox253 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox253
    (computed denominator ibox253) (computed denominator (FixedTape.midBox ibox253))
    (by decide +kernel)
private theorem midpoint_even_253 : ∀ k, 2 ∣ (ibox253 k).lo+(ibox253 k).hi := by decide +kernel
private theorem accepted_253 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox253) tree253 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox253 midpoint_even_253
  simp only [tree253,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox253,candidate_valid h (FixedTape.midBox ibox253),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox253 101 (FixedTape.rowsAux denominator ibox253 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox253) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_253
private noncomputable def tree252 : TapeTree := .centered (candidateRows ibox252) (candidateRows (FixedTape.midBox ibox252))
attribute [irreducible] tree252
private theorem sign_252 : 2*denominator*(computed denominator (FixedTape.midBox ibox252)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox252).gradient k).lo.natAbs ((computed denominator ibox252).gradient k).hi.natAbs : Int)*((ibox252 k).hi-(ibox252 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox252
    (computed denominator ibox252) (computed denominator (FixedTape.midBox ibox252))
    (by decide +kernel)
private theorem midpoint_even_252 : ∀ k, 2 ∣ (ibox252 k).lo+(ibox252 k).hi := by decide +kernel
private theorem accepted_252 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox252) tree252 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox252 midpoint_even_252
  simp only [tree252,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox252,candidate_valid h (FixedTape.midBox ibox252),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox252 101 (FixedTape.rowsAux denominator ibox252 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox252) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_252
private noncomputable def tree251 : TapeTree := .centered (candidateRows ibox251) (candidateRows (FixedTape.midBox ibox251))
attribute [irreducible] tree251
private theorem sign_251 : 2*denominator*(computed denominator (FixedTape.midBox ibox251)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox251).gradient k).lo.natAbs ((computed denominator ibox251).gradient k).hi.natAbs : Int)*((ibox251 k).hi-(ibox251 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox251
    (computed denominator ibox251) (computed denominator (FixedTape.midBox ibox251))
    (by decide +kernel)
private theorem midpoint_even_251 : ∀ k, 2 ∣ (ibox251 k).lo+(ibox251 k).hi := by decide +kernel
private theorem accepted_251 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox251) tree251 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox251 midpoint_even_251
  simp only [tree251,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox251,candidate_valid h (FixedTape.midBox ibox251),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox251 101 (FixedTape.rowsAux denominator ibox251 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox251) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_251
private noncomputable def tree250 : TapeTree := .split 1 (((2666642987250311367521074721840524524294306612146535294566400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree251 tree252
attribute [irreducible] tree250
private theorem accepted_250 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox250) tree250 = true := by
  simp only [tree250,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox250 1 (2666642987250311367521074721840524524294306612146535294566400000000000000000000000 : Int) false,decode_split denominator ibox250 1 (2666642987250311367521074721840524524294306612146535294566400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_251 h,accepted_252 h⟩
private noncomputable def tree249 : TapeTree := .split 1 (((2696605268005932843560637359164575361645928034754923331584000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree250 tree253
attribute [irreducible] tree249
private theorem accepted_249 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox249) tree249 = true := by
  simp only [tree249,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox249 1 (2696605268005932843560637359164575361645928034754923331584000000000000000000000000 : Int) false,decode_split denominator ibox249 1 (2696605268005932843560637359164575361645928034754923331584000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_250 h,accepted_253 h⟩
private noncomputable def tree248 : TapeTree := .split 1 (((2756529829517175795639762633812677036349170879971699405619200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree249 tree254
attribute [irreducible] tree248
private theorem accepted_248 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox248) tree248 = true := by
  simp only [tree248,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox248 1 (2756529829517175795639762633812677036349170879971699405619200000000000000000000000 : Int) false,decode_split denominator ibox248 1 (2756529829517175795639762633812677036349170879971699405619200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_249 h,accepted_254 h⟩
private noncomputable def tree247 : TapeTree := .centered (candidateRows ibox247) (candidateRows (FixedTape.midBox ibox247))
attribute [irreducible] tree247
private theorem sign_247 : 2*denominator*(computed denominator (FixedTape.midBox ibox247)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox247).gradient k).lo.natAbs ((computed denominator ibox247).gradient k).hi.natAbs : Int)*((ibox247 k).hi-(ibox247 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox247
    (computed denominator ibox247) (computed denominator (FixedTape.midBox ibox247))
    (by decide +kernel)
private theorem midpoint_even_247 : ∀ k, 2 ∣ (ibox247 k).lo+(ibox247 k).hi := by decide +kernel
private theorem accepted_247 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox247) tree247 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox247 midpoint_even_247
  simp only [tree247,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox247,candidate_valid h (FixedTape.midBox ibox247),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox247 101 (FixedTape.rowsAux denominator ibox247 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox247) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_247
private noncomputable def tree246 : TapeTree := .centered (candidateRows ibox246) (candidateRows (FixedTape.midBox ibox246))
attribute [irreducible] tree246
private theorem sign_246 : 2*denominator*(computed denominator (FixedTape.midBox ibox246)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox246).gradient k).lo.natAbs ((computed denominator ibox246).gradient k).hi.natAbs : Int)*((ibox246 k).hi-(ibox246 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox246
    (computed denominator ibox246) (computed denominator (FixedTape.midBox ibox246))
    (by decide +kernel)
private theorem midpoint_even_246 : ∀ k, 2 ∣ (ibox246 k).lo+(ibox246 k).hi := by decide +kernel
private theorem accepted_246 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox246) tree246 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox246 midpoint_even_246
  simp only [tree246,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox246,candidate_valid h (FixedTape.midBox ibox246),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox246 101 (FixedTape.rowsAux denominator ibox246 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox246) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_246
private noncomputable def tree245 : TapeTree := .split 1 (((2606718425739068415441949447192422849591063766929759220531200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree246 tree247
attribute [irreducible] tree245
private theorem accepted_245 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox245) tree245 = true := by
  simp only [tree245,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox245 1 (2606718425739068415441949447192422849591063766929759220531200000000000000000000000 : Int) false,decode_split denominator ibox245 1 (2606718425739068415441949447192422849591063766929759220531200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_246 h,accepted_247 h⟩
private noncomputable def tree244 : TapeTree := .centered (candidateRows ibox244) (candidateRows (FixedTape.midBox ibox244))
attribute [irreducible] tree244
private theorem sign_244 : 2*denominator*(computed denominator (FixedTape.midBox ibox244)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox244).gradient k).lo.natAbs ((computed denominator ibox244).gradient k).hi.natAbs : Int)*((ibox244 k).hi-(ibox244 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox244
    (computed denominator ibox244) (computed denominator (FixedTape.midBox ibox244))
    (by decide +kernel)
private theorem midpoint_even_244 : ∀ k, 2 ∣ (ibox244 k).lo+(ibox244 k).hi := by decide +kernel
private theorem accepted_244 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox244) tree244 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox244 midpoint_even_244
  simp only [tree244,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox244,candidate_valid h (FixedTape.midBox ibox244),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox244 101 (FixedTape.rowsAux denominator ibox244 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox244) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_244
private noncomputable def tree243 : TapeTree := .centered (candidateRows ibox243) (candidateRows (FixedTape.midBox ibox243))
attribute [irreducible] tree243
private theorem sign_243 : 2*denominator*(computed denominator (FixedTape.midBox ibox243)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox243).gradient k).lo.natAbs ((computed denominator ibox243).gradient k).hi.natAbs : Int)*((ibox243 k).hi-(ibox243 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox243
    (computed denominator ibox243) (computed denominator (FixedTape.midBox ibox243))
    (by decide +kernel)
private theorem midpoint_even_243 : ∀ k, 2 ∣ (ibox243 k).lo+(ibox243 k).hi := by decide +kernel
private theorem accepted_243 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox243) tree243 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox243 midpoint_even_243
  simp only [tree243,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox243,candidate_valid h (FixedTape.midBox ibox243),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox243 101 (FixedTape.rowsAux denominator ibox243 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox243) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_243
private noncomputable def tree242 : TapeTree := .split 1 (((2546793864227825463362824172544321174887820921712983146496000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree243 tree244
attribute [irreducible] tree242
private theorem accepted_242 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox242) tree242 = true := by
  simp only [tree242,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox242 1 (2546793864227825463362824172544321174887820921712983146496000000000000000000000000 : Int) false,decode_split denominator ibox242 1 (2546793864227825463362824172544321174887820921712983146496000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_243 h,accepted_244 h⟩
private noncomputable def tree241 : TapeTree := .split 1 (((2576756144983446939402386809868372012239442344321371183513600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree242 tree245
attribute [irreducible] tree241
private theorem accepted_241 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox241) tree241 = true := by
  simp only [tree241,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox241 1 (2576756144983446939402386809868372012239442344321371183513600000000000000000000000 : Int) false,decode_split denominator ibox241 1 (2576756144983446939402386809868372012239442344321371183513600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_242 h,accepted_245 h⟩
private noncomputable def tree240 : TapeTree := .centered (candidateRows ibox240) (candidateRows (FixedTape.midBox ibox240))
attribute [irreducible] tree240
private theorem sign_240 : 2*denominator*(computed denominator (FixedTape.midBox ibox240)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox240).gradient k).lo.natAbs ((computed denominator ibox240).gradient k).hi.natAbs : Int)*((ibox240 k).hi-(ibox240 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox240
    (computed denominator ibox240) (computed denominator (FixedTape.midBox ibox240))
    (by decide +kernel)
private theorem midpoint_even_240 : ∀ k, 2 ∣ (ibox240 k).lo+(ibox240 k).hi := by decide +kernel
private theorem accepted_240 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox240) tree240 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox240 midpoint_even_240
  simp only [tree240,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox240,candidate_valid h (FixedTape.midBox ibox240),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox240 101 (FixedTape.rowsAux denominator ibox240 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox240) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_240
private noncomputable def tree239 : TapeTree := .centered (candidateRows ibox239) (candidateRows (FixedTape.midBox ibox239))
attribute [irreducible] tree239
private theorem sign_239 : 2*denominator*(computed denominator (FixedTape.midBox ibox239)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox239).gradient k).lo.natAbs ((computed denominator ibox239).gradient k).hi.natAbs : Int)*((ibox239 k).hi-(ibox239 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox239
    (computed denominator ibox239) (computed denominator (FixedTape.midBox ibox239))
    (by decide +kernel)
private theorem midpoint_even_239 : ∀ k, 2 ∣ (ibox239 k).lo+(ibox239 k).hi := by decide +kernel
private theorem accepted_239 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox239) tree239 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox239 midpoint_even_239
  simp only [tree239,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox239,candidate_valid h (FixedTape.midBox ibox239),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox239 101 (FixedTape.rowsAux denominator ibox239 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox239) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_239
private noncomputable def tree238 : TapeTree := .split 1 (((2486869302716582511283698897896219500184578076496207072460800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree239 tree240
attribute [irreducible] tree238
private theorem accepted_238 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox238) tree238 = true := by
  simp only [tree238,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox238 1 (2486869302716582511283698897896219500184578076496207072460800000000000000000000000 : Int) false,decode_split denominator ibox238 1 (2486869302716582511283698897896219500184578076496207072460800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_239 h,accepted_240 h⟩
private noncomputable def tree237 : TapeTree := .centered (candidateRows ibox237) (candidateRows (FixedTape.midBox ibox237))
attribute [irreducible] tree237
private theorem sign_237 : 2*denominator*(computed denominator (FixedTape.midBox ibox237)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox237).gradient k).lo.natAbs ((computed denominator ibox237).gradient k).hi.natAbs : Int)*((ibox237 k).hi-(ibox237 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox237
    (computed denominator ibox237) (computed denominator (FixedTape.midBox ibox237))
    (by decide +kernel)
private theorem midpoint_even_237 : ∀ k, 2 ∣ (ibox237 k).lo+(ibox237 k).hi := by decide +kernel
private theorem accepted_237 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox237) tree237 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox237 midpoint_even_237
  simp only [tree237,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox237,candidate_valid h (FixedTape.midBox ibox237),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox237 101 (FixedTape.rowsAux denominator ibox237 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox237) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_237
private noncomputable def tree236 : TapeTree := .centered (candidateRows ibox236) (candidateRows (FixedTape.midBox ibox236))
attribute [irreducible] tree236
private theorem sign_236 : 2*denominator*(computed denominator (FixedTape.midBox ibox236)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox236).gradient k).lo.natAbs ((computed denominator ibox236).gradient k).hi.natAbs : Int)*((ibox236 k).hi-(ibox236 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox236
    (computed denominator ibox236) (computed denominator (FixedTape.midBox ibox236))
    (by decide +kernel)
private theorem midpoint_even_236 : ∀ k, 2 ∣ (ibox236 k).lo+(ibox236 k).hi := by decide +kernel
private theorem accepted_236 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox236) tree236 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox236 midpoint_even_236
  simp only [tree236,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox236,candidate_valid h (FixedTape.midBox ibox236),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox236 101 (FixedTape.rowsAux denominator ibox236 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox236) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_236
private noncomputable def tree235 : TapeTree := .split 1 (((2426944741205339559204573623248117825481335231279430998425600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree236 tree237
attribute [irreducible] tree235
private theorem accepted_235 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox235) tree235 = true := by
  simp only [tree235,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox235 1 (2426944741205339559204573623248117825481335231279430998425600000000000000000000000 : Int) false,decode_split denominator ibox235 1 (2426944741205339559204573623248117825481335231279430998425600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_236 h,accepted_237 h⟩
private noncomputable def tree234 : TapeTree := .split 1 (((2456907021960961035244136260572168662832956653887819035443200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree235 tree238
attribute [irreducible] tree234
private theorem accepted_234 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox234) tree234 = true := by
  simp only [tree234,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox234 1 (2456907021960961035244136260572168662832956653887819035443200000000000000000000000 : Int) false,decode_split denominator ibox234 1 (2456907021960961035244136260572168662832956653887819035443200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_235 h,accepted_238 h⟩
private noncomputable def tree233 : TapeTree := .split 1 (((2516831583472203987323261535220270337536199499104595109478400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree234 tree241
attribute [irreducible] tree233
private theorem accepted_233 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox233) tree233 = true := by
  simp only [tree233,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox233 1 (2516831583472203987323261535220270337536199499104595109478400000000000000000000000 : Int) false,decode_split denominator ibox233 1 (2516831583472203987323261535220270337536199499104595109478400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_234 h,accepted_241 h⟩
private noncomputable def tree232 : TapeTree := .split 1 (((2636680706494689891481512084516473686942685189538147257548800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree233 tree248
attribute [irreducible] tree232
private theorem accepted_232 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox232) tree232 = true := by
  simp only [tree232,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox232 1 (2636680706494689891481512084516473686942685189538147257548800000000000000000000000 : Int) false,decode_split denominator ibox232 1 (2636680706494689891481512084516473686942685189538147257548800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_233 h,accepted_248 h⟩
private noncomputable def tree231 : TapeTree := .centered (candidateRows ibox231) (candidateRows (FixedTape.midBox ibox231))
attribute [irreducible] tree231
private theorem sign_231 : 2*denominator*(computed denominator (FixedTape.midBox ibox231)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox231).gradient k).lo.natAbs ((computed denominator ibox231).gradient k).hi.natAbs : Int)*((ibox231 k).hi-(ibox231 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox231
    (computed denominator ibox231) (computed denominator (FixedTape.midBox ibox231))
    (by decide +kernel)
private theorem midpoint_even_231 : ∀ k, 2 ∣ (ibox231 k).lo+(ibox231 k).hi := by decide +kernel
private theorem accepted_231 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox231) tree231 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox231 midpoint_even_231
  simp only [tree231,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox231,candidate_valid h (FixedTape.midBox ibox231),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox231 101 (FixedTape.rowsAux denominator ibox231 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox231) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_231
private noncomputable def tree230 : TapeTree := .centered (candidateRows ibox230) (candidateRows (FixedTape.midBox ibox230))
attribute [irreducible] tree230
private theorem sign_230 : 2*denominator*(computed denominator (FixedTape.midBox ibox230)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox230).gradient k).lo.natAbs ((computed denominator ibox230).gradient k).hi.natAbs : Int)*((ibox230 k).hi-(ibox230 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox230
    (computed denominator ibox230) (computed denominator (FixedTape.midBox ibox230))
    (by decide +kernel)
private theorem midpoint_even_230 : ∀ k, 2 ∣ (ibox230 k).lo+(ibox230 k).hi := by decide +kernel
private theorem accepted_230 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox230) tree230 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox230 midpoint_even_230
  simp only [tree230,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox230,candidate_valid h (FixedTape.midBox ibox230),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox230 101 (FixedTape.rowsAux denominator ibox230 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox230) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_230
private noncomputable def tree229 : TapeTree := .split 1 (((2367020179694096607125448348600016150778092386062654924390400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree230 tree231
attribute [irreducible] tree229
private theorem accepted_229 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox229) tree229 = true := by
  simp only [tree229,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox229 1 (2367020179694096607125448348600016150778092386062654924390400000000000000000000000 : Int) false,decode_split denominator ibox229 1 (2367020179694096607125448348600016150778092386062654924390400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_230 h,accepted_231 h⟩
private noncomputable def tree228 : TapeTree := .centered (candidateRows ibox228) (candidateRows (FixedTape.midBox ibox228))
attribute [irreducible] tree228
private theorem sign_228 : 2*denominator*(computed denominator (FixedTape.midBox ibox228)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox228).gradient k).lo.natAbs ((computed denominator ibox228).gradient k).hi.natAbs : Int)*((ibox228 k).hi-(ibox228 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox228
    (computed denominator ibox228) (computed denominator (FixedTape.midBox ibox228))
    (by decide +kernel)
private theorem midpoint_even_228 : ∀ k, 2 ∣ (ibox228 k).lo+(ibox228 k).hi := by decide +kernel
private theorem accepted_228 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox228) tree228 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox228 midpoint_even_228
  simp only [tree228,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox228,candidate_valid h (FixedTape.midBox ibox228),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox228 101 (FixedTape.rowsAux denominator ibox228 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox228) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_228
private noncomputable def tree227 : TapeTree := .centered (candidateRows ibox227) (candidateRows (FixedTape.midBox ibox227))
attribute [irreducible] tree227
private theorem sign_227 : 2*denominator*(computed denominator (FixedTape.midBox ibox227)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox227).gradient k).lo.natAbs ((computed denominator ibox227).gradient k).hi.natAbs : Int)*((ibox227 k).hi-(ibox227 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox227
    (computed denominator ibox227) (computed denominator (FixedTape.midBox ibox227))
    (by decide +kernel)
private theorem midpoint_even_227 : ∀ k, 2 ∣ (ibox227 k).lo+(ibox227 k).hi := by decide +kernel
private theorem accepted_227 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox227) tree227 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox227 midpoint_even_227
  simp only [tree227,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox227,candidate_valid h (FixedTape.midBox ibox227),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox227 101 (FixedTape.rowsAux denominator ibox227 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox227) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_227
private noncomputable def tree226 : TapeTree := .split 1 (((2307095618182853655046323073951914476074849540845878850355200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree227 tree228
attribute [irreducible] tree226
private theorem accepted_226 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox226) tree226 = true := by
  simp only [tree226,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox226 1 (2307095618182853655046323073951914476074849540845878850355200000000000000000000000 : Int) false,decode_split denominator ibox226 1 (2307095618182853655046323073951914476074849540845878850355200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_227 h,accepted_228 h⟩
private noncomputable def tree225 : TapeTree := .split 1 (((2337057898938475131085885711275965313426470963454266887372800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree226 tree229
attribute [irreducible] tree225
private theorem accepted_225 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox225) tree225 = true := by
  simp only [tree225,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox225 1 (2337057898938475131085885711275965313426470963454266887372800000000000000000000000 : Int) false,decode_split denominator ibox225 1 (2337057898938475131085885711275965313426470963454266887372800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_226 h,accepted_229 h⟩
private noncomputable def tree224 : TapeTree := .centered (candidateRows ibox224) (candidateRows (FixedTape.midBox ibox224))
attribute [irreducible] tree224
private theorem sign_224 : 2*denominator*(computed denominator (FixedTape.midBox ibox224)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox224).gradient k).lo.natAbs ((computed denominator ibox224).gradient k).hi.natAbs : Int)*((ibox224 k).hi-(ibox224 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox224
    (computed denominator ibox224) (computed denominator (FixedTape.midBox ibox224))
    (by decide +kernel)
private theorem midpoint_even_224 : ∀ k, 2 ∣ (ibox224 k).lo+(ibox224 k).hi := by decide +kernel
private theorem accepted_224 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox224) tree224 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox224 midpoint_even_224
  simp only [tree224,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox224,candidate_valid h (FixedTape.midBox ibox224),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox224 101 (FixedTape.rowsAux denominator ibox224 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox224) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_224
private noncomputable def tree223 : TapeTree := .centered (candidateRows ibox223) (candidateRows (FixedTape.midBox ibox223))
attribute [irreducible] tree223
private theorem sign_223 : 2*denominator*(computed denominator (FixedTape.midBox ibox223)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox223).gradient k).lo.natAbs ((computed denominator ibox223).gradient k).hi.natAbs : Int)*((ibox223 k).hi-(ibox223 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox223
    (computed denominator ibox223) (computed denominator (FixedTape.midBox ibox223))
    (by decide +kernel)
private theorem midpoint_even_223 : ∀ k, 2 ∣ (ibox223 k).lo+(ibox223 k).hi := by decide +kernel
private theorem accepted_223 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox223) tree223 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox223 midpoint_even_223
  simp only [tree223,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox223,candidate_valid h (FixedTape.midBox ibox223),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox223 101 (FixedTape.rowsAux denominator ibox223 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox223) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_223
private noncomputable def tree222 : TapeTree := .split 1 (((2247171056671610702967197799303812801371606695629102776320000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree223 tree224
attribute [irreducible] tree222
private theorem accepted_222 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox222) tree222 = true := by
  simp only [tree222,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox222 1 (2247171056671610702967197799303812801371606695629102776320000000000000000000000000 : Int) false,decode_split denominator ibox222 1 (2247171056671610702967197799303812801371606695629102776320000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_223 h,accepted_224 h⟩
private noncomputable def tree221 : TapeTree := .centered (candidateRows ibox221) (candidateRows (FixedTape.midBox ibox221))
attribute [irreducible] tree221
private theorem sign_221 : 2*denominator*(computed denominator (FixedTape.midBox ibox221)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox221).gradient k).lo.natAbs ((computed denominator ibox221).gradient k).hi.natAbs : Int)*((ibox221 k).hi-(ibox221 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox221
    (computed denominator ibox221) (computed denominator (FixedTape.midBox ibox221))
    (by decide +kernel)
private theorem midpoint_even_221 : ∀ k, 2 ∣ (ibox221 k).lo+(ibox221 k).hi := by decide +kernel
private theorem accepted_221 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox221) tree221 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox221 midpoint_even_221
  simp only [tree221,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox221,candidate_valid h (FixedTape.midBox ibox221),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox221 101 (FixedTape.rowsAux denominator ibox221 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox221) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_221
private noncomputable def tree220 : TapeTree := .centered (candidateRows ibox220) (candidateRows (FixedTape.midBox ibox220))
attribute [irreducible] tree220
private theorem sign_220 : 2*denominator*(computed denominator (FixedTape.midBox ibox220)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox220).gradient k).lo.natAbs ((computed denominator ibox220).gradient k).hi.natAbs : Int)*((ibox220 k).hi-(ibox220 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox220
    (computed denominator ibox220) (computed denominator (FixedTape.midBox ibox220))
    (by decide +kernel)
private theorem midpoint_even_220 : ∀ k, 2 ∣ (ibox220 k).lo+(ibox220 k).hi := by decide +kernel
private theorem accepted_220 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox220) tree220 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox220 midpoint_even_220
  simp only [tree220,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox220,candidate_valid h (FixedTape.midBox ibox220),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox220 101 (FixedTape.rowsAux denominator ibox220 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox220) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_220
private noncomputable def tree219 : TapeTree := .split 1 (((2187246495160367750888072524655711126668363850412326702284800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree220 tree221
attribute [irreducible] tree219
private theorem accepted_219 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox219) tree219 = true := by
  simp only [tree219,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox219 1 (2187246495160367750888072524655711126668363850412326702284800000000000000000000000 : Int) false,decode_split denominator ibox219 1 (2187246495160367750888072524655711126668363850412326702284800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_220 h,accepted_221 h⟩
private noncomputable def tree218 : TapeTree := .split 1 (((2217208775915989226927635161979761964019985273020714739302400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree219 tree222
attribute [irreducible] tree218
private theorem accepted_218 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox218) tree218 = true := by
  simp only [tree218,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox218 1 (2217208775915989226927635161979761964019985273020714739302400000000000000000000000 : Int) false,decode_split denominator ibox218 1 (2217208775915989226927635161979761964019985273020714739302400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_219 h,accepted_222 h⟩
private noncomputable def tree217 : TapeTree := .split 1 (((2277133337427232179006760436627863638723228118237490813337600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree218 tree225
attribute [irreducible] tree217
private theorem accepted_217 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox217) tree217 = true := by
  simp only [tree217,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox217 1 (2277133337427232179006760436627863638723228118237490813337600000000000000000000000 : Int) false,decode_split denominator ibox217 1 (2277133337427232179006760436627863638723228118237490813337600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_218 h,accepted_225 h⟩
private noncomputable def tree216 : TapeTree := .centered (candidateRows ibox216) (candidateRows (FixedTape.midBox ibox216))
attribute [irreducible] tree216
private theorem sign_216 : 2*denominator*(computed denominator (FixedTape.midBox ibox216)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox216).gradient k).lo.natAbs ((computed denominator ibox216).gradient k).hi.natAbs : Int)*((ibox216 k).hi-(ibox216 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox216
    (computed denominator ibox216) (computed denominator (FixedTape.midBox ibox216))
    (by decide +kernel)
private theorem midpoint_even_216 : ∀ k, 2 ∣ (ibox216 k).lo+(ibox216 k).hi := by decide +kernel
private theorem accepted_216 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox216) tree216 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox216 midpoint_even_216
  simp only [tree216,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox216,candidate_valid h (FixedTape.midBox ibox216),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox216 101 (FixedTape.rowsAux denominator ibox216 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox216) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_216
private noncomputable def tree215 : TapeTree := .centered (candidateRows ibox215) (candidateRows (FixedTape.midBox ibox215))
attribute [irreducible] tree215
private theorem sign_215 : 2*denominator*(computed denominator (FixedTape.midBox ibox215)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox215).gradient k).lo.natAbs ((computed denominator ibox215).gradient k).hi.natAbs : Int)*((ibox215 k).hi-(ibox215 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox215
    (computed denominator ibox215) (computed denominator (FixedTape.midBox ibox215))
    (by decide +kernel)
private theorem midpoint_even_215 : ∀ k, 2 ∣ (ibox215 k).lo+(ibox215 k).hi := by decide +kernel
private theorem accepted_215 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox215) tree215 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox215 midpoint_even_215
  simp only [tree215,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox215,candidate_valid h (FixedTape.midBox ibox215),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox215 101 (FixedTape.rowsAux denominator ibox215 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox215) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_215
private noncomputable def tree214 : TapeTree := .split 1 (((2127321933649124798808947250007609451965121005195550628249600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree215 tree216
attribute [irreducible] tree214
private theorem accepted_214 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox214) tree214 = true := by
  simp only [tree214,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox214 1 (2127321933649124798808947250007609451965121005195550628249600000000000000000000000 : Int) false,decode_split denominator ibox214 1 (2127321933649124798808947250007609451965121005195550628249600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_215 h,accepted_216 h⟩
private noncomputable def tree213 : TapeTree := .centered (candidateRows ibox213) (candidateRows (FixedTape.midBox ibox213))
attribute [irreducible] tree213
private theorem sign_213 : 2*denominator*(computed denominator (FixedTape.midBox ibox213)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox213).gradient k).lo.natAbs ((computed denominator ibox213).gradient k).hi.natAbs : Int)*((ibox213 k).hi-(ibox213 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox213
    (computed denominator ibox213) (computed denominator (FixedTape.midBox ibox213))
    (by decide +kernel)
private theorem midpoint_even_213 : ∀ k, 2 ∣ (ibox213 k).lo+(ibox213 k).hi := by decide +kernel
private theorem accepted_213 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox213) tree213 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox213 midpoint_even_213
  simp only [tree213,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox213,candidate_valid h (FixedTape.midBox ibox213),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox213 101 (FixedTape.rowsAux denominator ibox213 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox213) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_213
private noncomputable def tree212 : TapeTree := .centered (candidateRows ibox212) (candidateRows (FixedTape.midBox ibox212))
attribute [irreducible] tree212
private theorem sign_212 : 2*denominator*(computed denominator (FixedTape.midBox ibox212)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox212).gradient k).lo.natAbs ((computed denominator ibox212).gradient k).hi.natAbs : Int)*((ibox212 k).hi-(ibox212 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox212
    (computed denominator ibox212) (computed denominator (FixedTape.midBox ibox212))
    (by decide +kernel)
private theorem midpoint_even_212 : ∀ k, 2 ∣ (ibox212 k).lo+(ibox212 k).hi := by decide +kernel
private theorem accepted_212 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox212) tree212 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox212 midpoint_even_212
  simp only [tree212,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox212,candidate_valid h (FixedTape.midBox ibox212),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox212 101 (FixedTape.rowsAux denominator ibox212 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox212) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_212
private noncomputable def tree211 : TapeTree := .split 1 (((2067397372137881846729821975359507777261878159978774554214400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree212 tree213
attribute [irreducible] tree211
private theorem accepted_211 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox211) tree211 = true := by
  simp only [tree211,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox211 1 (2067397372137881846729821975359507777261878159978774554214400000000000000000000000 : Int) false,decode_split denominator ibox211 1 (2067397372137881846729821975359507777261878159978774554214400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_212 h,accepted_213 h⟩
private noncomputable def tree210 : TapeTree := .split 1 (((2097359652893503322769384612683558614613499582587162591232000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree211 tree214
attribute [irreducible] tree210
private theorem accepted_210 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox210) tree210 = true := by
  simp only [tree210,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox210 1 (2097359652893503322769384612683558614613499582587162591232000000000000000000000000 : Int) false,decode_split denominator ibox210 1 (2097359652893503322769384612683558614613499582587162591232000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_211 h,accepted_214 h⟩
private noncomputable def tree209 : TapeTree := .centered (candidateRows ibox209) (candidateRows (FixedTape.midBox ibox209))
attribute [irreducible] tree209
private theorem sign_209 : 2*denominator*(computed denominator (FixedTape.midBox ibox209)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox209).gradient k).lo.natAbs ((computed denominator ibox209).gradient k).hi.natAbs : Int)*((ibox209 k).hi-(ibox209 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox209
    (computed denominator ibox209) (computed denominator (FixedTape.midBox ibox209))
    (by decide +kernel)
private theorem midpoint_even_209 : ∀ k, 2 ∣ (ibox209 k).lo+(ibox209 k).hi := by decide +kernel
private theorem accepted_209 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox209) tree209 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox209 midpoint_even_209
  simp only [tree209,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox209,candidate_valid h (FixedTape.midBox ibox209),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox209 101 (FixedTape.rowsAux denominator ibox209 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox209) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_209
private noncomputable def tree208 : TapeTree := .centered (candidateRows ibox208) (candidateRows (FixedTape.midBox ibox208))
attribute [irreducible] tree208
private theorem sign_208 : 2*denominator*(computed denominator (FixedTape.midBox ibox208)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox208).gradient k).lo.natAbs ((computed denominator ibox208).gradient k).hi.natAbs : Int)*((ibox208 k).hi-(ibox208 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox208
    (computed denominator ibox208) (computed denominator (FixedTape.midBox ibox208))
    (by decide +kernel)
private theorem midpoint_even_208 : ∀ k, 2 ∣ (ibox208 k).lo+(ibox208 k).hi := by decide +kernel
private theorem accepted_208 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox208) tree208 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox208 midpoint_even_208
  simp only [tree208,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox208,candidate_valid h (FixedTape.midBox ibox208),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox208 101 (FixedTape.rowsAux denominator ibox208 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox208) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_208
private noncomputable def tree207 : TapeTree := .split 1 (((2007472810626638894650696700711406102558635314761998480179200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree208 tree209
attribute [irreducible] tree207
private theorem accepted_207 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox207) tree207 = true := by
  simp only [tree207,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox207 1 (2007472810626638894650696700711406102558635314761998480179200000000000000000000000 : Int) false,decode_split denominator ibox207 1 (2007472810626638894650696700711406102558635314761998480179200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_208 h,accepted_209 h⟩
private noncomputable def tree206 : TapeTree := .centered (candidateRows ibox206) (candidateRows (FixedTape.midBox ibox206))
attribute [irreducible] tree206
private theorem sign_206 : 2*denominator*(computed denominator (FixedTape.midBox ibox206)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox206).gradient k).lo.natAbs ((computed denominator ibox206).gradient k).hi.natAbs : Int)*((ibox206 k).hi-(ibox206 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox206
    (computed denominator ibox206) (computed denominator (FixedTape.midBox ibox206))
    (by decide +kernel)
private theorem midpoint_even_206 : ∀ k, 2 ∣ (ibox206 k).lo+(ibox206 k).hi := by decide +kernel
private theorem accepted_206 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox206) tree206 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox206 midpoint_even_206
  simp only [tree206,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox206,candidate_valid h (FixedTape.midBox ibox206),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox206 101 (FixedTape.rowsAux denominator ibox206 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox206) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_206
private noncomputable def tree205 : TapeTree := .centered (candidateRows ibox205) (candidateRows (FixedTape.midBox ibox205))
attribute [irreducible] tree205
private theorem sign_205 : 2*denominator*(computed denominator (FixedTape.midBox ibox205)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox205).gradient k).lo.natAbs ((computed denominator ibox205).gradient k).hi.natAbs : Int)*((ibox205 k).hi-(ibox205 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox205
    (computed denominator ibox205) (computed denominator (FixedTape.midBox ibox205))
    (by decide +kernel)
private theorem midpoint_even_205 : ∀ k, 2 ∣ (ibox205 k).lo+(ibox205 k).hi := by decide +kernel
private theorem accepted_205 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox205) tree205 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox205 midpoint_even_205
  simp only [tree205,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox205,candidate_valid h (FixedTape.midBox ibox205),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox205 101 (FixedTape.rowsAux denominator ibox205 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox205) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_205
private noncomputable def tree204 : TapeTree := .split 1 (((1947548249115395942571571426063304427855392469545222406144000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree205 tree206
attribute [irreducible] tree204
private theorem accepted_204 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox204) tree204 = true := by
  simp only [tree204,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox204 1 (1947548249115395942571571426063304427855392469545222406144000000000000000000000000 : Int) false,decode_split denominator ibox204 1 (1947548249115395942571571426063304427855392469545222406144000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_205 h,accepted_206 h⟩
private noncomputable def tree203 : TapeTree := .split 1 (((1977510529871017418611134063387355265207013892153610443161600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree204 tree207
attribute [irreducible] tree203
private theorem accepted_203 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox203) tree203 = true := by
  simp only [tree203,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox203 1 (1977510529871017418611134063387355265207013892153610443161600000000000000000000000 : Int) false,decode_split denominator ibox203 1 (1977510529871017418611134063387355265207013892153610443161600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_204 h,accepted_207 h⟩
private noncomputable def tree202 : TapeTree := .split 1 (((2037435091382260370690259338035456939910256737370386517196800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree203 tree210
attribute [irreducible] tree202
private theorem accepted_202 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox202) tree202 = true := by
  simp only [tree202,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox202 1 (2037435091382260370690259338035456939910256737370386517196800000000000000000000000 : Int) false,decode_split denominator ibox202 1 (2037435091382260370690259338035456939910256737370386517196800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_203 h,accepted_210 h⟩
private noncomputable def tree201 : TapeTree := .split 1 (((2157284214404746274848509887331660289316742427803938665267200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree202 tree217
attribute [irreducible] tree201
private theorem accepted_201 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox201) tree201 = true := by
  simp only [tree201,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox201 1 (2157284214404746274848509887331660289316742427803938665267200000000000000000000000 : Int) false,decode_split denominator ibox201 1 (2157284214404746274848509887331660289316742427803938665267200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_202 h,accepted_217 h⟩
private noncomputable def tree200 : TapeTree := .split 1 (((2396982460449718083165010985924066988129713808671042961408000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree201 tree232
attribute [irreducible] tree200
private theorem accepted_200 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox200) tree200 = true := by
  simp only [tree200,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox200 1 (2396982460449718083165010985924066988129713808671042961408000000000000000000000000 : Int) false,decode_split denominator ibox200 1 (2396982460449718083165010985924066988129713808671042961408000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_201 h,accepted_232 h⟩
private noncomputable def tree199 : TapeTree := .split 1 (((2876378952539661699798013183108880385755656570405251553689600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree200 tree257
attribute [irreducible] tree199
private theorem accepted_199 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox199) tree199 = true := by
  simp only [tree199,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox199 1 (2876378952539661699798013183108880385755656570405251553689600000000000000000000000 : Int) false,decode_split denominator ibox199 1 (2876378952539661699798013183108880385755656570405251553689600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_200 h,accepted_257 h⟩
private noncomputable def tree198 : TapeTree := .centered (candidateRows ibox198) (candidateRows (FixedTape.midBox ibox198))
attribute [irreducible] tree198
private theorem sign_198 : 2*denominator*(computed denominator (FixedTape.midBox ibox198)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox198).gradient k).lo.natAbs ((computed denominator ibox198).gradient k).hi.natAbs : Int)*((ibox198 k).hi-(ibox198 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox198
    (computed denominator ibox198) (computed denominator (FixedTape.midBox ibox198))
    (by decide +kernel)
private theorem midpoint_even_198 : ∀ k, 2 ∣ (ibox198 k).lo+(ibox198 k).hi := by decide +kernel
private theorem accepted_198 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox198) tree198 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox198 midpoint_even_198
  simp only [tree198,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox198,candidate_valid h (FixedTape.midBox ibox198),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox198 101 (FixedTape.rowsAux denominator ibox198 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox198) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_198
private noncomputable def tree197 : TapeTree := .centered (candidateRows ibox197) (candidateRows (FixedTape.midBox ibox197))
attribute [irreducible] tree197
private theorem sign_197 : 2*denominator*(computed denominator (FixedTape.midBox ibox197)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox197).gradient k).lo.natAbs ((computed denominator ibox197).gradient k).hi.natAbs : Int)*((ibox197 k).hi-(ibox197 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox197
    (computed denominator ibox197) (computed denominator (FixedTape.midBox ibox197))
    (by decide +kernel)
private theorem midpoint_even_197 : ∀ k, 2 ∣ (ibox197 k).lo+(ibox197 k).hi := by decide +kernel
private theorem accepted_197 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox197) tree197 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox197 midpoint_even_197
  simp only [tree197,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox197,candidate_valid h (FixedTape.midBox ibox197),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox197 101 (FixedTape.rowsAux denominator ibox197 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox197) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_197
private noncomputable def tree196 : TapeTree := .split 1 (((1887623687604152990492446151415202753152149624328446332108800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree197 tree198
attribute [irreducible] tree196
private theorem accepted_196 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox196) tree196 = true := by
  simp only [tree196,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox196 1 (1887623687604152990492446151415202753152149624328446332108800000000000000000000000 : Int) false,decode_split denominator ibox196 1 (1887623687604152990492446151415202753152149624328446332108800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_197 h,accepted_198 h⟩
private noncomputable def tree195 : TapeTree := .centered (candidateRows ibox195) (candidateRows (FixedTape.midBox ibox195))
attribute [irreducible] tree195
private theorem sign_195 : 2*denominator*(computed denominator (FixedTape.midBox ibox195)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox195).gradient k).lo.natAbs ((computed denominator ibox195).gradient k).hi.natAbs : Int)*((ibox195 k).hi-(ibox195 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox195
    (computed denominator ibox195) (computed denominator (FixedTape.midBox ibox195))
    (by decide +kernel)
private theorem midpoint_even_195 : ∀ k, 2 ∣ (ibox195 k).lo+(ibox195 k).hi := by decide +kernel
private theorem accepted_195 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox195) tree195 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox195 midpoint_even_195
  simp only [tree195,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox195,candidate_valid h (FixedTape.midBox ibox195),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox195 101 (FixedTape.rowsAux denominator ibox195 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox195) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_195
private noncomputable def tree194 : TapeTree := .centered (candidateRows ibox194) (candidateRows (FixedTape.midBox ibox194))
attribute [irreducible] tree194
private theorem sign_194 : 2*denominator*(computed denominator (FixedTape.midBox ibox194)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox194).gradient k).lo.natAbs ((computed denominator ibox194).gradient k).hi.natAbs : Int)*((ibox194 k).hi-(ibox194 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox194
    (computed denominator ibox194) (computed denominator (FixedTape.midBox ibox194))
    (by decide +kernel)
private theorem midpoint_even_194 : ∀ k, 2 ∣ (ibox194 k).lo+(ibox194 k).hi := by decide +kernel
private theorem accepted_194 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox194) tree194 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox194 midpoint_even_194
  simp only [tree194,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox194,candidate_valid h (FixedTape.midBox ibox194),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox194 101 (FixedTape.rowsAux denominator ibox194 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox194) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_194
private noncomputable def tree193 : TapeTree := .split 1 (((1827699126092910038413320876767101078448906779111670258073600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree194 tree195
attribute [irreducible] tree193
private theorem accepted_193 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox193) tree193 = true := by
  simp only [tree193,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox193 1 (1827699126092910038413320876767101078448906779111670258073600000000000000000000000 : Int) false,decode_split denominator ibox193 1 (1827699126092910038413320876767101078448906779111670258073600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_194 h,accepted_195 h⟩
private noncomputable def tree192 : TapeTree := .centered (candidateRows ibox192) (candidateRows (FixedTape.midBox ibox192))
attribute [irreducible] tree192
private theorem sign_192 : 2*denominator*(computed denominator (FixedTape.midBox ibox192)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox192).gradient k).lo.natAbs ((computed denominator ibox192).gradient k).hi.natAbs : Int)*((ibox192 k).hi-(ibox192 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox192
    (computed denominator ibox192) (computed denominator (FixedTape.midBox ibox192))
    (by decide +kernel)
private theorem midpoint_even_192 : ∀ k, 2 ∣ (ibox192 k).lo+(ibox192 k).hi := by decide +kernel
private theorem accepted_192 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox192) tree192 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox192 midpoint_even_192
  simp only [tree192,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox192,candidate_valid h (FixedTape.midBox ibox192),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox192 101 (FixedTape.rowsAux denominator ibox192 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox192) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_192
private noncomputable def tree191 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree192 tree193
attribute [irreducible] tree191
private theorem accepted_191 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox191) tree191 = true := by
  simp only [tree191,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox191 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox191 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_192 h,accepted_193 h⟩
private noncomputable def tree190 : TapeTree := .split 1 (((1857661406848531514452883514091151915800528201720058295091200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree191 tree196
attribute [irreducible] tree190
private theorem accepted_190 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox190) tree190 = true := by
  simp only [tree190,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox190 1 (1857661406848531514452883514091151915800528201720058295091200000000000000000000000 : Int) false,decode_split denominator ibox190 1 (1857661406848531514452883514091151915800528201720058295091200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_191 h,accepted_196 h⟩
private noncomputable def tree189 : TapeTree := .centered (candidateRows ibox189) (candidateRows (FixedTape.midBox ibox189))
attribute [irreducible] tree189
private theorem sign_189 : 2*denominator*(computed denominator (FixedTape.midBox ibox189)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox189).gradient k).lo.natAbs ((computed denominator ibox189).gradient k).hi.natAbs : Int)*((ibox189 k).hi-(ibox189 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox189
    (computed denominator ibox189) (computed denominator (FixedTape.midBox ibox189))
    (by decide +kernel)
private theorem midpoint_even_189 : ∀ k, 2 ∣ (ibox189 k).lo+(ibox189 k).hi := by decide +kernel
private theorem accepted_189 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox189) tree189 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox189 midpoint_even_189
  simp only [tree189,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox189,candidate_valid h (FixedTape.midBox ibox189),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox189 101 (FixedTape.rowsAux denominator ibox189 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox189) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_189
private noncomputable def tree188 : TapeTree := .centered (candidateRows ibox188) (candidateRows (FixedTape.midBox ibox188))
attribute [irreducible] tree188
private theorem sign_188 : 2*denominator*(computed denominator (FixedTape.midBox ibox188)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox188).gradient k).lo.natAbs ((computed denominator ibox188).gradient k).hi.natAbs : Int)*((ibox188 k).hi-(ibox188 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox188
    (computed denominator ibox188) (computed denominator (FixedTape.midBox ibox188))
    (by decide +kernel)
private theorem midpoint_even_188 : ∀ k, 2 ∣ (ibox188 k).lo+(ibox188 k).hi := by decide +kernel
private theorem accepted_188 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox188) tree188 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox188 midpoint_even_188
  simp only [tree188,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox188,candidate_valid h (FixedTape.midBox ibox188),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox188 101 (FixedTape.rowsAux denominator ibox188 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox188) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_188
private noncomputable def tree187 : TapeTree := .split 1 (((1767774564581667086334195602118999403745663933894894184038400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree188 tree189
attribute [irreducible] tree187
private theorem accepted_187 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox187) tree187 = true := by
  simp only [tree187,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox187 1 (1767774564581667086334195602118999403745663933894894184038400000000000000000000000 : Int) false,decode_split denominator ibox187 1 (1767774564581667086334195602118999403745663933894894184038400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_188 h,accepted_189 h⟩
private noncomputable def tree186 : TapeTree := .centered (candidateRows ibox186) (candidateRows (FixedTape.midBox ibox186))
attribute [irreducible] tree186
private theorem sign_186 : 2*denominator*(computed denominator (FixedTape.midBox ibox186)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox186).gradient k).lo.natAbs ((computed denominator ibox186).gradient k).hi.natAbs : Int)*((ibox186 k).hi-(ibox186 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox186
    (computed denominator ibox186) (computed denominator (FixedTape.midBox ibox186))
    (by decide +kernel)
private theorem midpoint_even_186 : ∀ k, 2 ∣ (ibox186 k).lo+(ibox186 k).hi := by decide +kernel
private theorem accepted_186 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox186) tree186 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox186 midpoint_even_186
  simp only [tree186,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox186,candidate_valid h (FixedTape.midBox ibox186),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox186 101 (FixedTape.rowsAux denominator ibox186 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox186) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_186
private noncomputable def tree185 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree186 tree187
attribute [irreducible] tree185
private theorem accepted_185 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox185) tree185 = true := by
  simp only [tree185,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox185 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox185 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_186 h,accepted_187 h⟩
private noncomputable def tree184 : TapeTree := .centered (candidateRows ibox184) (candidateRows (FixedTape.midBox ibox184))
attribute [irreducible] tree184
private theorem sign_184 : 2*denominator*(computed denominator (FixedTape.midBox ibox184)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox184).gradient k).lo.natAbs ((computed denominator ibox184).gradient k).hi.natAbs : Int)*((ibox184 k).hi-(ibox184 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox184
    (computed denominator ibox184) (computed denominator (FixedTape.midBox ibox184))
    (by decide +kernel)
private theorem midpoint_even_184 : ∀ k, 2 ∣ (ibox184 k).lo+(ibox184 k).hi := by decide +kernel
private theorem accepted_184 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox184) tree184 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox184 midpoint_even_184
  simp only [tree184,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox184,candidate_valid h (FixedTape.midBox ibox184),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox184 101 (FixedTape.rowsAux denominator ibox184 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox184) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_184
private noncomputable def tree183 : TapeTree := .centered (candidateRows ibox183) (candidateRows (FixedTape.midBox ibox183))
attribute [irreducible] tree183
private theorem sign_183 : 2*denominator*(computed denominator (FixedTape.midBox ibox183)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox183).gradient k).lo.natAbs ((computed denominator ibox183).gradient k).hi.natAbs : Int)*((ibox183 k).hi-(ibox183 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox183
    (computed denominator ibox183) (computed denominator (FixedTape.midBox ibox183))
    (by decide +kernel)
private theorem midpoint_even_183 : ∀ k, 2 ∣ (ibox183 k).lo+(ibox183 k).hi := by decide +kernel
private theorem accepted_183 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox183) tree183 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox183 midpoint_even_183
  simp only [tree183,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox183,candidate_valid h (FixedTape.midBox ibox183),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox183 101 (FixedTape.rowsAux denominator ibox183 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox183) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_183
private noncomputable def tree182 : TapeTree := .split 1 (((1707850003070424134255070327470897729042421088678118110003200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree183 tree184
attribute [irreducible] tree182
private theorem accepted_182 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox182) tree182 = true := by
  simp only [tree182,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox182 1 (1707850003070424134255070327470897729042421088678118110003200000000000000000000000 : Int) false,decode_split denominator ibox182 1 (1707850003070424134255070327470897729042421088678118110003200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_183 h,accepted_184 h⟩
private noncomputable def tree181 : TapeTree := .centered (candidateRows ibox181) (candidateRows (FixedTape.midBox ibox181))
attribute [irreducible] tree181
private theorem sign_181 : 2*denominator*(computed denominator (FixedTape.midBox ibox181)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox181).gradient k).lo.natAbs ((computed denominator ibox181).gradient k).hi.natAbs : Int)*((ibox181 k).hi-(ibox181 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox181
    (computed denominator ibox181) (computed denominator (FixedTape.midBox ibox181))
    (by decide +kernel)
private theorem midpoint_even_181 : ∀ k, 2 ∣ (ibox181 k).lo+(ibox181 k).hi := by decide +kernel
private theorem accepted_181 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox181) tree181 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox181 midpoint_even_181
  simp only [tree181,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox181,candidate_valid h (FixedTape.midBox ibox181),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox181 101 (FixedTape.rowsAux denominator ibox181 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox181) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_181
private noncomputable def tree180 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree181 tree182
attribute [irreducible] tree180
private theorem accepted_180 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox180) tree180 = true := by
  simp only [tree180,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox180 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox180 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_181 h,accepted_182 h⟩
private noncomputable def tree179 : TapeTree := .split 1 (((1737812283826045610294632964794948566394042511286506147020800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree180 tree185
attribute [irreducible] tree179
private theorem accepted_179 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox179) tree179 = true := by
  simp only [tree179,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox179 1 (1737812283826045610294632964794948566394042511286506147020800000000000000000000000 : Int) false,decode_split denominator ibox179 1 (1737812283826045610294632964794948566394042511286506147020800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_180 h,accepted_185 h⟩
private noncomputable def tree178 : TapeTree := .split 1 (((1797736845337288562373758239443050241097285356503282221056000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree179 tree190
attribute [irreducible] tree178
private theorem accepted_178 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox178) tree178 = true := by
  simp only [tree178,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox178 1 (1797736845337288562373758239443050241097285356503282221056000000000000000000000000 : Int) false,decode_split denominator ibox178 1 (1797736845337288562373758239443050241097285356503282221056000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_179 h,accepted_190 h⟩
private noncomputable def tree177 : TapeTree := .centered (candidateRows ibox177) (candidateRows (FixedTape.midBox ibox177))
attribute [irreducible] tree177
private theorem sign_177 : 2*denominator*(computed denominator (FixedTape.midBox ibox177)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox177).gradient k).lo.natAbs ((computed denominator ibox177).gradient k).hi.natAbs : Int)*((ibox177 k).hi-(ibox177 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox177
    (computed denominator ibox177) (computed denominator (FixedTape.midBox ibox177))
    (by decide +kernel)
private theorem midpoint_even_177 : ∀ k, 2 ∣ (ibox177 k).lo+(ibox177 k).hi := by decide +kernel
private theorem accepted_177 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox177) tree177 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox177 midpoint_even_177
  simp only [tree177,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox177,candidate_valid h (FixedTape.midBox ibox177),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox177 101 (FixedTape.rowsAux denominator ibox177 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox177) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_177
private noncomputable def tree176 : TapeTree := .centered (candidateRows ibox176) (candidateRows (FixedTape.midBox ibox176))
attribute [irreducible] tree176
private theorem sign_176 : 2*denominator*(computed denominator (FixedTape.midBox ibox176)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox176).gradient k).lo.natAbs ((computed denominator ibox176).gradient k).hi.natAbs : Int)*((ibox176 k).hi-(ibox176 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox176
    (computed denominator ibox176) (computed denominator (FixedTape.midBox ibox176))
    (by decide +kernel)
private theorem midpoint_even_176 : ∀ k, 2 ∣ (ibox176 k).lo+(ibox176 k).hi := by decide +kernel
private theorem accepted_176 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox176) tree176 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox176 midpoint_even_176
  simp only [tree176,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox176,candidate_valid h (FixedTape.midBox ibox176),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox176 101 (FixedTape.rowsAux denominator ibox176 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox176) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_176
private noncomputable def tree175 : TapeTree := .split 1 (((1647925441559181182175945052822796054339178243461342035968000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree176 tree177
attribute [irreducible] tree175
private theorem accepted_175 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox175) tree175 = true := by
  simp only [tree175,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox175 1 (1647925441559181182175945052822796054339178243461342035968000000000000000000000000 : Int) false,decode_split denominator ibox175 1 (1647925441559181182175945052822796054339178243461342035968000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_176 h,accepted_177 h⟩
private noncomputable def tree174 : TapeTree := .centered (candidateRows ibox174) (candidateRows (FixedTape.midBox ibox174))
attribute [irreducible] tree174
private theorem sign_174 : 2*denominator*(computed denominator (FixedTape.midBox ibox174)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox174).gradient k).lo.natAbs ((computed denominator ibox174).gradient k).hi.natAbs : Int)*((ibox174 k).hi-(ibox174 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox174
    (computed denominator ibox174) (computed denominator (FixedTape.midBox ibox174))
    (by decide +kernel)
private theorem midpoint_even_174 : ∀ k, 2 ∣ (ibox174 k).lo+(ibox174 k).hi := by decide +kernel
private theorem accepted_174 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox174) tree174 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox174 midpoint_even_174
  simp only [tree174,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox174,candidate_valid h (FixedTape.midBox ibox174),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox174 101 (FixedTape.rowsAux denominator ibox174 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox174) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_174
private noncomputable def tree173 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree174 tree175
attribute [irreducible] tree173
private theorem accepted_173 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox173) tree173 = true := by
  simp only [tree173,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox173 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox173 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_174 h,accepted_175 h⟩
private noncomputable def tree172 : TapeTree := .centered (candidateRows ibox172) (candidateRows (FixedTape.midBox ibox172))
attribute [irreducible] tree172
private theorem sign_172 : 2*denominator*(computed denominator (FixedTape.midBox ibox172)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox172).gradient k).lo.natAbs ((computed denominator ibox172).gradient k).hi.natAbs : Int)*((ibox172 k).hi-(ibox172 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox172
    (computed denominator ibox172) (computed denominator (FixedTape.midBox ibox172))
    (by decide +kernel)
private theorem midpoint_even_172 : ∀ k, 2 ∣ (ibox172 k).lo+(ibox172 k).hi := by decide +kernel
private theorem accepted_172 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox172) tree172 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox172 midpoint_even_172
  simp only [tree172,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox172,candidate_valid h (FixedTape.midBox ibox172),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox172 101 (FixedTape.rowsAux denominator ibox172 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox172) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_172
private noncomputable def tree171 : TapeTree := .centered (candidateRows ibox171) (candidateRows (FixedTape.midBox ibox171))
attribute [irreducible] tree171
private theorem sign_171 : 2*denominator*(computed denominator (FixedTape.midBox ibox171)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox171).gradient k).lo.natAbs ((computed denominator ibox171).gradient k).hi.natAbs : Int)*((ibox171 k).hi-(ibox171 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox171
    (computed denominator ibox171) (computed denominator (FixedTape.midBox ibox171))
    (by decide +kernel)
private theorem midpoint_even_171 : ∀ k, 2 ∣ (ibox171 k).lo+(ibox171 k).hi := by decide +kernel
private theorem accepted_171 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox171) tree171 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox171 midpoint_even_171
  simp only [tree171,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox171,candidate_valid h (FixedTape.midBox ibox171),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox171 101 (FixedTape.rowsAux denominator ibox171 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox171) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_171
private noncomputable def tree170 : TapeTree := .split 1 (((1588000880047938230096819778174694379635935398244565961932800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree171 tree172
attribute [irreducible] tree170
private theorem accepted_170 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox170) tree170 = true := by
  simp only [tree170,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox170 1 (1588000880047938230096819778174694379635935398244565961932800000000000000000000000 : Int) false,decode_split denominator ibox170 1 (1588000880047938230096819778174694379635935398244565961932800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_171 h,accepted_172 h⟩
private noncomputable def tree169 : TapeTree := .centered (candidateRows ibox169) (candidateRows (FixedTape.midBox ibox169))
attribute [irreducible] tree169
private theorem sign_169 : 2*denominator*(computed denominator (FixedTape.midBox ibox169)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox169).gradient k).lo.natAbs ((computed denominator ibox169).gradient k).hi.natAbs : Int)*((ibox169 k).hi-(ibox169 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox169
    (computed denominator ibox169) (computed denominator (FixedTape.midBox ibox169))
    (by decide +kernel)
private theorem midpoint_even_169 : ∀ k, 2 ∣ (ibox169 k).lo+(ibox169 k).hi := by decide +kernel
private theorem accepted_169 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox169) tree169 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox169 midpoint_even_169
  simp only [tree169,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox169,candidate_valid h (FixedTape.midBox ibox169),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox169 101 (FixedTape.rowsAux denominator ibox169 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox169) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_169
private noncomputable def tree168 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree169 tree170
attribute [irreducible] tree168
private theorem accepted_168 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox168) tree168 = true := by
  simp only [tree168,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox168 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox168 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_169 h,accepted_170 h⟩
private noncomputable def tree167 : TapeTree := .split 1 (((1617963160803559706136382415498745216987556820852953998950400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree168 tree173
attribute [irreducible] tree167
private theorem accepted_167 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox167) tree167 = true := by
  simp only [tree167,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox167 1 (1617963160803559706136382415498745216987556820852953998950400000000000000000000000 : Int) false,decode_split denominator ibox167 1 (1617963160803559706136382415498745216987556820852953998950400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_168 h,accepted_173 h⟩
private noncomputable def tree166 : TapeTree := .centered (candidateRows ibox166) (candidateRows (FixedTape.midBox ibox166))
attribute [irreducible] tree166
private theorem sign_166 : 2*denominator*(computed denominator (FixedTape.midBox ibox166)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox166).gradient k).lo.natAbs ((computed denominator ibox166).gradient k).hi.natAbs : Int)*((ibox166 k).hi-(ibox166 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox166
    (computed denominator ibox166) (computed denominator (FixedTape.midBox ibox166))
    (by decide +kernel)
private theorem midpoint_even_166 : ∀ k, 2 ∣ (ibox166 k).lo+(ibox166 k).hi := by decide +kernel
private theorem accepted_166 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox166) tree166 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox166 midpoint_even_166
  simp only [tree166,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox166,candidate_valid h (FixedTape.midBox ibox166),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox166 101 (FixedTape.rowsAux denominator ibox166 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox166) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_166
private noncomputable def tree165 : TapeTree := .centered (candidateRows ibox165) (candidateRows (FixedTape.midBox ibox165))
attribute [irreducible] tree165
private theorem sign_165 : 2*denominator*(computed denominator (FixedTape.midBox ibox165)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox165).gradient k).lo.natAbs ((computed denominator ibox165).gradient k).hi.natAbs : Int)*((ibox165 k).hi-(ibox165 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox165
    (computed denominator ibox165) (computed denominator (FixedTape.midBox ibox165))
    (by decide +kernel)
private theorem midpoint_even_165 : ∀ k, 2 ∣ (ibox165 k).lo+(ibox165 k).hi := by decide +kernel
private theorem accepted_165 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox165) tree165 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox165 midpoint_even_165
  simp only [tree165,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox165,candidate_valid h (FixedTape.midBox ibox165),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox165 101 (FixedTape.rowsAux denominator ibox165 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox165) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_165
private noncomputable def tree164 : TapeTree := .split 1 (((1528076318536695278017694503526592704932692553027789887897600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree165 tree166
attribute [irreducible] tree164
private theorem accepted_164 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox164) tree164 = true := by
  simp only [tree164,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox164 1 (1528076318536695278017694503526592704932692553027789887897600000000000000000000000 : Int) false,decode_split denominator ibox164 1 (1528076318536695278017694503526592704932692553027789887897600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_165 h,accepted_166 h⟩
private noncomputable def tree163 : TapeTree := .centered (candidateRows ibox163) (candidateRows (FixedTape.midBox ibox163))
attribute [irreducible] tree163
private theorem sign_163 : 2*denominator*(computed denominator (FixedTape.midBox ibox163)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox163).gradient k).lo.natAbs ((computed denominator ibox163).gradient k).hi.natAbs : Int)*((ibox163 k).hi-(ibox163 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox163
    (computed denominator ibox163) (computed denominator (FixedTape.midBox ibox163))
    (by decide +kernel)
private theorem midpoint_even_163 : ∀ k, 2 ∣ (ibox163 k).lo+(ibox163 k).hi := by decide +kernel
private theorem accepted_163 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox163) tree163 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox163 midpoint_even_163
  simp only [tree163,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox163,candidate_valid h (FixedTape.midBox ibox163),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox163 101 (FixedTape.rowsAux denominator ibox163 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox163) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_163
private noncomputable def tree162 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree163 tree164
attribute [irreducible] tree162
private theorem accepted_162 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox162) tree162 = true := by
  simp only [tree162,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox162 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox162 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_163 h,accepted_164 h⟩
private noncomputable def tree161 : TapeTree := .centered (candidateRows ibox161) (candidateRows (FixedTape.midBox ibox161))
attribute [irreducible] tree161
private theorem sign_161 : 2*denominator*(computed denominator (FixedTape.midBox ibox161)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox161).gradient k).lo.natAbs ((computed denominator ibox161).gradient k).hi.natAbs : Int)*((ibox161 k).hi-(ibox161 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox161
    (computed denominator ibox161) (computed denominator (FixedTape.midBox ibox161))
    (by decide +kernel)
private theorem midpoint_even_161 : ∀ k, 2 ∣ (ibox161 k).lo+(ibox161 k).hi := by decide +kernel
private theorem accepted_161 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox161) tree161 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox161 midpoint_even_161
  simp only [tree161,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox161,candidate_valid h (FixedTape.midBox ibox161),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox161 101 (FixedTape.rowsAux denominator ibox161 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox161) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_161
private noncomputable def tree160 : TapeTree := .centered (candidateRows ibox160) (candidateRows (FixedTape.midBox ibox160))
attribute [irreducible] tree160
private theorem sign_160 : 2*denominator*(computed denominator (FixedTape.midBox ibox160)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox160).gradient k).lo.natAbs ((computed denominator ibox160).gradient k).hi.natAbs : Int)*((ibox160 k).hi-(ibox160 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox160
    (computed denominator ibox160) (computed denominator (FixedTape.midBox ibox160))
    (by decide +kernel)
private theorem midpoint_even_160 : ∀ k, 2 ∣ (ibox160 k).lo+(ibox160 k).hi := by decide +kernel
private theorem accepted_160 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox160) tree160 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox160 midpoint_even_160
  simp only [tree160,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox160,candidate_valid h (FixedTape.midBox ibox160),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox160 101 (FixedTape.rowsAux denominator ibox160 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox160) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_160
private noncomputable def tree159 : TapeTree := .split 1 (((1468151757025452325938569228878491030229449707811013813862400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree160 tree161
attribute [irreducible] tree159
private theorem accepted_159 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox159) tree159 = true := by
  simp only [tree159,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox159 1 (1468151757025452325938569228878491030229449707811013813862400000000000000000000000 : Int) false,decode_split denominator ibox159 1 (1468151757025452325938569228878491030229449707811013813862400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_160 h,accepted_161 h⟩
private noncomputable def tree158 : TapeTree := .centered (candidateRows ibox158) (candidateRows (FixedTape.midBox ibox158))
attribute [irreducible] tree158
private theorem sign_158 : 2*denominator*(computed denominator (FixedTape.midBox ibox158)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox158).gradient k).lo.natAbs ((computed denominator ibox158).gradient k).hi.natAbs : Int)*((ibox158 k).hi-(ibox158 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox158
    (computed denominator ibox158) (computed denominator (FixedTape.midBox ibox158))
    (by decide +kernel)
private theorem midpoint_even_158 : ∀ k, 2 ∣ (ibox158 k).lo+(ibox158 k).hi := by decide +kernel
private theorem accepted_158 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox158) tree158 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox158 midpoint_even_158
  simp only [tree158,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox158,candidate_valid h (FixedTape.midBox ibox158),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox158 101 (FixedTape.rowsAux denominator ibox158 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox158) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_158
private noncomputable def tree157 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree158 tree159
attribute [irreducible] tree157
private theorem accepted_157 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox157) tree157 = true := by
  simp only [tree157,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox157 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox157 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_158 h,accepted_159 h⟩
private noncomputable def tree156 : TapeTree := .split 1 (((1498114037781073801978131866202541867581071130419401850880000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree157 tree162
attribute [irreducible] tree156
private theorem accepted_156 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox156) tree156 = true := by
  simp only [tree156,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox156 1 (1498114037781073801978131866202541867581071130419401850880000000000000000000000000 : Int) false,decode_split denominator ibox156 1 (1498114037781073801978131866202541867581071130419401850880000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_157 h,accepted_162 h⟩
private noncomputable def tree155 : TapeTree := .split 1 (((1558038599292316754057257140850643542284313975636177924915200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree156 tree167
attribute [irreducible] tree155
private theorem accepted_155 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox155) tree155 = true := by
  simp only [tree155,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox155 1 (1558038599292316754057257140850643542284313975636177924915200000000000000000000000 : Int) false,decode_split denominator ibox155 1 (1558038599292316754057257140850643542284313975636177924915200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_156 h,accepted_167 h⟩
private noncomputable def tree154 : TapeTree := .split 1 (((1677887722314802658215507690146846891690799666069730072985600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree155 tree178
attribute [irreducible] tree154
private theorem accepted_154 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox154) tree154 = true := by
  simp only [tree154,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox154 1 (1677887722314802658215507690146846891690799666069730072985600000000000000000000000 : Int) false,decode_split denominator ibox154 1 (1677887722314802658215507690146846891690799666069730072985600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_155 h,accepted_178 h⟩
private noncomputable def tree153 : TapeTree := .centered (candidateRows ibox153) (candidateRows (FixedTape.midBox ibox153))
attribute [irreducible] tree153
private theorem sign_153 : 2*denominator*(computed denominator (FixedTape.midBox ibox153)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox153).gradient k).lo.natAbs ((computed denominator ibox153).gradient k).hi.natAbs : Int)*((ibox153 k).hi-(ibox153 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox153
    (computed denominator ibox153) (computed denominator (FixedTape.midBox ibox153))
    (by decide +kernel)
private theorem midpoint_even_153 : ∀ k, 2 ∣ (ibox153 k).lo+(ibox153 k).hi := by decide +kernel
private theorem accepted_153 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox153) tree153 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox153 midpoint_even_153
  simp only [tree153,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox153,candidate_valid h (FixedTape.midBox ibox153),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox153 101 (FixedTape.rowsAux denominator ibox153 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox153) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_153
private noncomputable def tree152 : TapeTree := .centered (candidateRows ibox152) (candidateRows (FixedTape.midBox ibox152))
attribute [irreducible] tree152
private theorem sign_152 : 2*denominator*(computed denominator (FixedTape.midBox ibox152)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox152).gradient k).lo.natAbs ((computed denominator ibox152).gradient k).hi.natAbs : Int)*((ibox152 k).hi-(ibox152 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox152
    (computed denominator ibox152) (computed denominator (FixedTape.midBox ibox152))
    (by decide +kernel)
private theorem midpoint_even_152 : ∀ k, 2 ∣ (ibox152 k).lo+(ibox152 k).hi := by decide +kernel
private theorem accepted_152 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox152) tree152 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox152 midpoint_even_152
  simp only [tree152,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox152,candidate_valid h (FixedTape.midBox ibox152),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox152 101 (FixedTape.rowsAux denominator ibox152 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox152) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_152
private noncomputable def tree151 : TapeTree := .split 1 (((1408227195514209373859443954230389355526206862594237739827200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree152 tree153
attribute [irreducible] tree151
private theorem accepted_151 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox151) tree151 = true := by
  simp only [tree151,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox151 1 (1408227195514209373859443954230389355526206862594237739827200000000000000000000000 : Int) false,decode_split denominator ibox151 1 (1408227195514209373859443954230389355526206862594237739827200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_152 h,accepted_153 h⟩
private noncomputable def tree150 : TapeTree := .centered (candidateRows ibox150) (candidateRows (FixedTape.midBox ibox150))
attribute [irreducible] tree150
private theorem sign_150 : 2*denominator*(computed denominator (FixedTape.midBox ibox150)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox150).gradient k).lo.natAbs ((computed denominator ibox150).gradient k).hi.natAbs : Int)*((ibox150 k).hi-(ibox150 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox150
    (computed denominator ibox150) (computed denominator (FixedTape.midBox ibox150))
    (by decide +kernel)
private theorem midpoint_even_150 : ∀ k, 2 ∣ (ibox150 k).lo+(ibox150 k).hi := by decide +kernel
private theorem accepted_150 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox150) tree150 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox150 midpoint_even_150
  simp only [tree150,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox150,candidate_valid h (FixedTape.midBox ibox150),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox150 101 (FixedTape.rowsAux denominator ibox150 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox150) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_150
private noncomputable def tree149 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree150 tree151
attribute [irreducible] tree149
private theorem accepted_149 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox149) tree149 = true := by
  simp only [tree149,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox149 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox149 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_150 h,accepted_151 h⟩
private noncomputable def tree148 : TapeTree := .centered (candidateRows ibox148) (candidateRows (FixedTape.midBox ibox148))
attribute [irreducible] tree148
private theorem sign_148 : 2*denominator*(computed denominator (FixedTape.midBox ibox148)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox148).gradient k).lo.natAbs ((computed denominator ibox148).gradient k).hi.natAbs : Int)*((ibox148 k).hi-(ibox148 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox148
    (computed denominator ibox148) (computed denominator (FixedTape.midBox ibox148))
    (by decide +kernel)
private theorem midpoint_even_148 : ∀ k, 2 ∣ (ibox148 k).lo+(ibox148 k).hi := by decide +kernel
private theorem accepted_148 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox148) tree148 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox148 midpoint_even_148
  simp only [tree148,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox148,candidate_valid h (FixedTape.midBox ibox148),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox148 101 (FixedTape.rowsAux denominator ibox148 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox148) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_148
private noncomputable def tree147 : TapeTree := .centered (candidateRows ibox147) (candidateRows (FixedTape.midBox ibox147))
attribute [irreducible] tree147
private theorem sign_147 : 2*denominator*(computed denominator (FixedTape.midBox ibox147)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox147).gradient k).lo.natAbs ((computed denominator ibox147).gradient k).hi.natAbs : Int)*((ibox147 k).hi-(ibox147 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox147
    (computed denominator ibox147) (computed denominator (FixedTape.midBox ibox147))
    (by decide +kernel)
private theorem midpoint_even_147 : ∀ k, 2 ∣ (ibox147 k).lo+(ibox147 k).hi := by decide +kernel
private theorem accepted_147 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox147) tree147 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox147 midpoint_even_147
  simp only [tree147,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox147,candidate_valid h (FixedTape.midBox ibox147),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox147 101 (FixedTape.rowsAux denominator ibox147 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox147) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_147
private noncomputable def tree146 : TapeTree := .split 1 (((1348302634002966421780318679582287680822964017377461665792000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree147 tree148
attribute [irreducible] tree146
private theorem accepted_146 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox146) tree146 = true := by
  simp only [tree146,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox146 1 (1348302634002966421780318679582287680822964017377461665792000000000000000000000000 : Int) false,decode_split denominator ibox146 1 (1348302634002966421780318679582287680822964017377461665792000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_147 h,accepted_148 h⟩
private noncomputable def tree145 : TapeTree := .centered (candidateRows ibox145) (candidateRows (FixedTape.midBox ibox145))
attribute [irreducible] tree145
private theorem sign_145 : 2*denominator*(computed denominator (FixedTape.midBox ibox145)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox145).gradient k).lo.natAbs ((computed denominator ibox145).gradient k).hi.natAbs : Int)*((ibox145 k).hi-(ibox145 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox145
    (computed denominator ibox145) (computed denominator (FixedTape.midBox ibox145))
    (by decide +kernel)
private theorem midpoint_even_145 : ∀ k, 2 ∣ (ibox145 k).lo+(ibox145 k).hi := by decide +kernel
private theorem accepted_145 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox145) tree145 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox145 midpoint_even_145
  simp only [tree145,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox145,candidate_valid h (FixedTape.midBox ibox145),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox145 101 (FixedTape.rowsAux denominator ibox145 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox145) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_145
private noncomputable def tree144 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree145 tree146
attribute [irreducible] tree144
private theorem accepted_144 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox144) tree144 = true := by
  simp only [tree144,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox144 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox144 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_145 h,accepted_146 h⟩
private noncomputable def tree143 : TapeTree := .split 1 (((1378264914758587897819881316906338518174585439985849702809600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree144 tree149
attribute [irreducible] tree143
private theorem accepted_143 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox143) tree143 = true := by
  simp only [tree143,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox143 1 (1378264914758587897819881316906338518174585439985849702809600000000000000000000000 : Int) false,decode_split denominator ibox143 1 (1378264914758587897819881316906338518174585439985849702809600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_144 h,accepted_149 h⟩
private noncomputable def tree142 : TapeTree := .centered (candidateRows ibox142) (candidateRows (FixedTape.midBox ibox142))
attribute [irreducible] tree142
private theorem sign_142 : 2*denominator*(computed denominator (FixedTape.midBox ibox142)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox142).gradient k).lo.natAbs ((computed denominator ibox142).gradient k).hi.natAbs : Int)*((ibox142 k).hi-(ibox142 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox142
    (computed denominator ibox142) (computed denominator (FixedTape.midBox ibox142))
    (by decide +kernel)
private theorem midpoint_even_142 : ∀ k, 2 ∣ (ibox142 k).lo+(ibox142 k).hi := by decide +kernel
private theorem accepted_142 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox142) tree142 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox142 midpoint_even_142
  simp only [tree142,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox142,candidate_valid h (FixedTape.midBox ibox142),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox142 101 (FixedTape.rowsAux denominator ibox142 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox142) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_142
private noncomputable def tree141 : TapeTree := .centered (candidateRows ibox141) (candidateRows (FixedTape.midBox ibox141))
attribute [irreducible] tree141
private theorem sign_141 : 2*denominator*(computed denominator (FixedTape.midBox ibox141)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox141).gradient k).lo.natAbs ((computed denominator ibox141).gradient k).hi.natAbs : Int)*((ibox141 k).hi-(ibox141 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox141
    (computed denominator ibox141) (computed denominator (FixedTape.midBox ibox141))
    (by decide +kernel)
private theorem midpoint_even_141 : ∀ k, 2 ∣ (ibox141 k).lo+(ibox141 k).hi := by decide +kernel
private theorem accepted_141 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox141) tree141 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox141 midpoint_even_141
  simp only [tree141,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox141,candidate_valid h (FixedTape.midBox ibox141),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox141 101 (FixedTape.rowsAux denominator ibox141 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox141) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_141
private noncomputable def tree140 : TapeTree := .split 1 (((1288378072491723469701193404934186006119721172160685591756800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree141 tree142
attribute [irreducible] tree140
private theorem accepted_140 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox140) tree140 = true := by
  simp only [tree140,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox140 1 (1288378072491723469701193404934186006119721172160685591756800000000000000000000000 : Int) false,decode_split denominator ibox140 1 (1288378072491723469701193404934186006119721172160685591756800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_141 h,accepted_142 h⟩
private noncomputable def tree139 : TapeTree := .centered (candidateRows ibox139) (candidateRows (FixedTape.midBox ibox139))
attribute [irreducible] tree139
private theorem sign_139 : 2*denominator*(computed denominator (FixedTape.midBox ibox139)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox139).gradient k).lo.natAbs ((computed denominator ibox139).gradient k).hi.natAbs : Int)*((ibox139 k).hi-(ibox139 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox139
    (computed denominator ibox139) (computed denominator (FixedTape.midBox ibox139))
    (by decide +kernel)
private theorem midpoint_even_139 : ∀ k, 2 ∣ (ibox139 k).lo+(ibox139 k).hi := by decide +kernel
private theorem accepted_139 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox139) tree139 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox139 midpoint_even_139
  simp only [tree139,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox139,candidate_valid h (FixedTape.midBox ibox139),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox139 101 (FixedTape.rowsAux denominator ibox139 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox139) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_139
private noncomputable def tree138 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree139 tree140
attribute [irreducible] tree138
private theorem accepted_138 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox138) tree138 = true := by
  simp only [tree138,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox138 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox138 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_139 h,accepted_140 h⟩
private noncomputable def tree137 : TapeTree := .centered (candidateRows ibox137) (candidateRows (FixedTape.midBox ibox137))
attribute [irreducible] tree137
private theorem sign_137 : 2*denominator*(computed denominator (FixedTape.midBox ibox137)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox137).gradient k).lo.natAbs ((computed denominator ibox137).gradient k).hi.natAbs : Int)*((ibox137 k).hi-(ibox137 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox137
    (computed denominator ibox137) (computed denominator (FixedTape.midBox ibox137))
    (by decide +kernel)
private theorem midpoint_even_137 : ∀ k, 2 ∣ (ibox137 k).lo+(ibox137 k).hi := by decide +kernel
private theorem accepted_137 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox137) tree137 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox137 midpoint_even_137
  simp only [tree137,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox137,candidate_valid h (FixedTape.midBox ibox137),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox137 101 (FixedTape.rowsAux denominator ibox137 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox137) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_137
private noncomputable def tree136 : TapeTree := .centered (candidateRows ibox136) (candidateRows (FixedTape.midBox ibox136))
attribute [irreducible] tree136
private theorem sign_136 : 2*denominator*(computed denominator (FixedTape.midBox ibox136)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox136).gradient k).lo.natAbs ((computed denominator ibox136).gradient k).hi.natAbs : Int)*((ibox136 k).hi-(ibox136 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox136
    (computed denominator ibox136) (computed denominator (FixedTape.midBox ibox136))
    (by decide +kernel)
private theorem midpoint_even_136 : ∀ k, 2 ∣ (ibox136 k).lo+(ibox136 k).hi := by decide +kernel
private theorem accepted_136 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox136) tree136 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox136 midpoint_even_136
  simp only [tree136,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox136,candidate_valid h (FixedTape.midBox ibox136),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox136 101 (FixedTape.rowsAux denominator ibox136 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox136) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_136
private noncomputable def tree135 : TapeTree := .split 1 (((1228453510980480517622068130286084331416478326943909517721600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree136 tree137
attribute [irreducible] tree135
private theorem accepted_135 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox135) tree135 = true := by
  simp only [tree135,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox135 1 (1228453510980480517622068130286084331416478326943909517721600000000000000000000000 : Int) false,decode_split denominator ibox135 1 (1228453510980480517622068130286084331416478326943909517721600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_136 h,accepted_137 h⟩
private noncomputable def tree134 : TapeTree := .centered (candidateRows ibox134) (candidateRows (FixedTape.midBox ibox134))
attribute [irreducible] tree134
private theorem sign_134 : 2*denominator*(computed denominator (FixedTape.midBox ibox134)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox134).gradient k).lo.natAbs ((computed denominator ibox134).gradient k).hi.natAbs : Int)*((ibox134 k).hi-(ibox134 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox134
    (computed denominator ibox134) (computed denominator (FixedTape.midBox ibox134))
    (by decide +kernel)
private theorem midpoint_even_134 : ∀ k, 2 ∣ (ibox134 k).lo+(ibox134 k).hi := by decide +kernel
private theorem accepted_134 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox134) tree134 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox134 midpoint_even_134
  simp only [tree134,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox134,candidate_valid h (FixedTape.midBox ibox134),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox134 101 (FixedTape.rowsAux denominator ibox134 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox134) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_134
private noncomputable def tree133 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree134 tree135
attribute [irreducible] tree133
private theorem accepted_133 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox133) tree133 = true := by
  simp only [tree133,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox133 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox133 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_134 h,accepted_135 h⟩
private noncomputable def tree132 : TapeTree := .split 1 (((1258415791736101993661630767610135168768099749552297554739200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree133 tree138
attribute [irreducible] tree132
private theorem accepted_132 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox132) tree132 = true := by
  simp only [tree132,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox132 1 (1258415791736101993661630767610135168768099749552297554739200000000000000000000000 : Int) false,decode_split denominator ibox132 1 (1258415791736101993661630767610135168768099749552297554739200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_133 h,accepted_138 h⟩
private noncomputable def tree131 : TapeTree := .split 1 (((1318340353247344945740756042258236843471342594769073628774400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree132 tree143
attribute [irreducible] tree131
private theorem accepted_131 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox131) tree131 = true := by
  simp only [tree131,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox131 1 (1318340353247344945740756042258236843471342594769073628774400000000000000000000000 : Int) false,decode_split denominator ibox131 1 (1318340353247344945740756042258236843471342594769073628774400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_132 h,accepted_143 h⟩
private noncomputable def tree130 : TapeTree := .centered (candidateRows ibox130) (candidateRows (FixedTape.midBox ibox130))
attribute [irreducible] tree130
private theorem sign_130 : 2*denominator*(computed denominator (FixedTape.midBox ibox130)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox130).gradient k).lo.natAbs ((computed denominator ibox130).gradient k).hi.natAbs : Int)*((ibox130 k).hi-(ibox130 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox130
    (computed denominator ibox130) (computed denominator (FixedTape.midBox ibox130))
    (by decide +kernel)
private theorem midpoint_even_130 : ∀ k, 2 ∣ (ibox130 k).lo+(ibox130 k).hi := by decide +kernel
private theorem accepted_130 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox130) tree130 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox130 midpoint_even_130
  simp only [tree130,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox130,candidate_valid h (FixedTape.midBox ibox130),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox130 101 (FixedTape.rowsAux denominator ibox130 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox130) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_130
private noncomputable def tree129 : TapeTree := .centered (candidateRows ibox129) (candidateRows (FixedTape.midBox ibox129))
attribute [irreducible] tree129
private theorem sign_129 : 2*denominator*(computed denominator (FixedTape.midBox ibox129)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox129).gradient k).lo.natAbs ((computed denominator ibox129).gradient k).hi.natAbs : Int)*((ibox129 k).hi-(ibox129 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox129
    (computed denominator ibox129) (computed denominator (FixedTape.midBox ibox129))
    (by decide +kernel)
private theorem midpoint_even_129 : ∀ k, 2 ∣ (ibox129 k).lo+(ibox129 k).hi := by decide +kernel
private theorem accepted_129 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox129) tree129 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox129 midpoint_even_129
  simp only [tree129,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox129,candidate_valid h (FixedTape.midBox ibox129),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox129 101 (FixedTape.rowsAux denominator ibox129 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox129) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_129
private noncomputable def tree128 : TapeTree := .split 1 (((1168528949469237565542942855637982656713235481727133443686400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree129 tree130
attribute [irreducible] tree128
private theorem accepted_128 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox128) tree128 = true := by
  simp only [tree128,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox128 1 (1168528949469237565542942855637982656713235481727133443686400000000000000000000000 : Int) false,decode_split denominator ibox128 1 (1168528949469237565542942855637982656713235481727133443686400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_129 h,accepted_130 h⟩
private noncomputable def tree127 : TapeTree := .centered (candidateRows ibox127) (candidateRows (FixedTape.midBox ibox127))
attribute [irreducible] tree127
private theorem sign_127 : 2*denominator*(computed denominator (FixedTape.midBox ibox127)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox127).gradient k).lo.natAbs ((computed denominator ibox127).gradient k).hi.natAbs : Int)*((ibox127 k).hi-(ibox127 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox127
    (computed denominator ibox127) (computed denominator (FixedTape.midBox ibox127))
    (by decide +kernel)
private theorem midpoint_even_127 : ∀ k, 2 ∣ (ibox127 k).lo+(ibox127 k).hi := by decide +kernel
private theorem accepted_127 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox127) tree127 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox127 midpoint_even_127
  simp only [tree127,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox127,candidate_valid h (FixedTape.midBox ibox127),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox127 101 (FixedTape.rowsAux denominator ibox127 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox127) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_127
private noncomputable def tree126 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree127 tree128
attribute [irreducible] tree126
private theorem accepted_126 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox126) tree126 = true := by
  simp only [tree126,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox126 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox126 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_127 h,accepted_128 h⟩
private noncomputable def tree125 : TapeTree := .centered (candidateRows ibox125) (candidateRows (FixedTape.midBox ibox125))
attribute [irreducible] tree125
private theorem sign_125 : 2*denominator*(computed denominator (FixedTape.midBox ibox125)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox125).gradient k).lo.natAbs ((computed denominator ibox125).gradient k).hi.natAbs : Int)*((ibox125 k).hi-(ibox125 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox125
    (computed denominator ibox125) (computed denominator (FixedTape.midBox ibox125))
    (by decide +kernel)
private theorem midpoint_even_125 : ∀ k, 2 ∣ (ibox125 k).lo+(ibox125 k).hi := by decide +kernel
private theorem accepted_125 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox125) tree125 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox125 midpoint_even_125
  simp only [tree125,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox125,candidate_valid h (FixedTape.midBox ibox125),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox125 101 (FixedTape.rowsAux denominator ibox125 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox125) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_125
private noncomputable def tree124 : TapeTree := .centered (candidateRows ibox124) (candidateRows (FixedTape.midBox ibox124))
attribute [irreducible] tree124
private theorem sign_124 : 2*denominator*(computed denominator (FixedTape.midBox ibox124)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox124).gradient k).lo.natAbs ((computed denominator ibox124).gradient k).hi.natAbs : Int)*((ibox124 k).hi-(ibox124 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox124
    (computed denominator ibox124) (computed denominator (FixedTape.midBox ibox124))
    (by decide +kernel)
private theorem midpoint_even_124 : ∀ k, 2 ∣ (ibox124 k).lo+(ibox124 k).hi := by decide +kernel
private theorem accepted_124 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox124) tree124 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox124 midpoint_even_124
  simp only [tree124,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox124,candidate_valid h (FixedTape.midBox ibox124),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox124 101 (FixedTape.rowsAux denominator ibox124 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox124) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_124
private noncomputable def tree123 : TapeTree := .split 1 (((1108604387957994613463817580989880982009992636510357369651200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree124 tree125
attribute [irreducible] tree123
private theorem accepted_123 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox123) tree123 = true := by
  simp only [tree123,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox123 1 (1108604387957994613463817580989880982009992636510357369651200000000000000000000000 : Int) false,decode_split denominator ibox123 1 (1108604387957994613463817580989880982009992636510357369651200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_124 h,accepted_125 h⟩
private noncomputable def tree122 : TapeTree := .centered (candidateRows ibox122) (candidateRows (FixedTape.midBox ibox122))
attribute [irreducible] tree122
private theorem sign_122 : 2*denominator*(computed denominator (FixedTape.midBox ibox122)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox122).gradient k).lo.natAbs ((computed denominator ibox122).gradient k).hi.natAbs : Int)*((ibox122 k).hi-(ibox122 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox122
    (computed denominator ibox122) (computed denominator (FixedTape.midBox ibox122))
    (by decide +kernel)
private theorem midpoint_even_122 : ∀ k, 2 ∣ (ibox122 k).lo+(ibox122 k).hi := by decide +kernel
private theorem accepted_122 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox122) tree122 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox122 midpoint_even_122
  simp only [tree122,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox122,candidate_valid h (FixedTape.midBox ibox122),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox122 101 (FixedTape.rowsAux denominator ibox122 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox122) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_122
private noncomputable def tree121 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree122 tree123
attribute [irreducible] tree121
private theorem accepted_121 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox121) tree121 = true := by
  simp only [tree121,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox121 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox121 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_122 h,accepted_123 h⟩
private noncomputable def tree120 : TapeTree := .split 1 (((1138566668713616089503380218313931819361614059118745406668800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree121 tree126
attribute [irreducible] tree120
private theorem accepted_120 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox120) tree120 = true := by
  simp only [tree120,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox120 1 (1138566668713616089503380218313931819361614059118745406668800000000000000000000000 : Int) false,decode_split denominator ibox120 1 (1138566668713616089503380218313931819361614059118745406668800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_121 h,accepted_126 h⟩
private noncomputable def tree119 : TapeTree := .centered (candidateRows ibox119) (candidateRows (FixedTape.midBox ibox119))
attribute [irreducible] tree119
private theorem sign_119 : 2*denominator*(computed denominator (FixedTape.midBox ibox119)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox119).gradient k).lo.natAbs ((computed denominator ibox119).gradient k).hi.natAbs : Int)*((ibox119 k).hi-(ibox119 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox119
    (computed denominator ibox119) (computed denominator (FixedTape.midBox ibox119))
    (by decide +kernel)
private theorem midpoint_even_119 : ∀ k, 2 ∣ (ibox119 k).lo+(ibox119 k).hi := by decide +kernel
private theorem accepted_119 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox119) tree119 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox119 midpoint_even_119
  simp only [tree119,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox119,candidate_valid h (FixedTape.midBox ibox119),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox119 101 (FixedTape.rowsAux denominator ibox119 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox119) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_119
private noncomputable def tree118 : TapeTree := .centered (candidateRows ibox118) (candidateRows (FixedTape.midBox ibox118))
attribute [irreducible] tree118
private theorem sign_118 : 2*denominator*(computed denominator (FixedTape.midBox ibox118)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox118).gradient k).lo.natAbs ((computed denominator ibox118).gradient k).hi.natAbs : Int)*((ibox118 k).hi-(ibox118 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox118
    (computed denominator ibox118) (computed denominator (FixedTape.midBox ibox118))
    (by decide +kernel)
private theorem midpoint_even_118 : ∀ k, 2 ∣ (ibox118 k).lo+(ibox118 k).hi := by decide +kernel
private theorem accepted_118 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox118) tree118 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox118 midpoint_even_118
  simp only [tree118,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox118,candidate_valid h (FixedTape.midBox ibox118),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox118 101 (FixedTape.rowsAux denominator ibox118 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox118) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_118
private noncomputable def tree117 : TapeTree := .split 1 (((1048679826446751661384692306341779307306749791293581295616000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree118 tree119
attribute [irreducible] tree117
private theorem accepted_117 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox117) tree117 = true := by
  simp only [tree117,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox117 1 (1048679826446751661384692306341779307306749791293581295616000000000000000000000000 : Int) false,decode_split denominator ibox117 1 (1048679826446751661384692306341779307306749791293581295616000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_118 h,accepted_119 h⟩
private noncomputable def tree116 : TapeTree := .centered (candidateRows ibox116) (candidateRows (FixedTape.midBox ibox116))
attribute [irreducible] tree116
private theorem sign_116 : 2*denominator*(computed denominator (FixedTape.midBox ibox116)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox116).gradient k).lo.natAbs ((computed denominator ibox116).gradient k).hi.natAbs : Int)*((ibox116 k).hi-(ibox116 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox116
    (computed denominator ibox116) (computed denominator (FixedTape.midBox ibox116))
    (by decide +kernel)
private theorem midpoint_even_116 : ∀ k, 2 ∣ (ibox116 k).lo+(ibox116 k).hi := by decide +kernel
private theorem accepted_116 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox116) tree116 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox116 midpoint_even_116
  simp only [tree116,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox116,candidate_valid h (FixedTape.midBox ibox116),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox116 101 (FixedTape.rowsAux denominator ibox116 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox116) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_116
private noncomputable def tree115 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree116 tree117
attribute [irreducible] tree115
private theorem accepted_115 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox115) tree115 = true := by
  simp only [tree115,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox115 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox115 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_116 h,accepted_117 h⟩
private noncomputable def tree114 : TapeTree := .centered (candidateRows ibox114) (candidateRows (FixedTape.midBox ibox114))
attribute [irreducible] tree114
private theorem sign_114 : 2*denominator*(computed denominator (FixedTape.midBox ibox114)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox114).gradient k).lo.natAbs ((computed denominator ibox114).gradient k).hi.natAbs : Int)*((ibox114 k).hi-(ibox114 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox114
    (computed denominator ibox114) (computed denominator (FixedTape.midBox ibox114))
    (by decide +kernel)
private theorem midpoint_even_114 : ∀ k, 2 ∣ (ibox114 k).lo+(ibox114 k).hi := by decide +kernel
private theorem accepted_114 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox114) tree114 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox114 midpoint_even_114
  simp only [tree114,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox114,candidate_valid h (FixedTape.midBox ibox114),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox114 101 (FixedTape.rowsAux denominator ibox114 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox114) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_114
private noncomputable def tree113 : TapeTree := .centered (candidateRows ibox113) (candidateRows (FixedTape.midBox ibox113))
attribute [irreducible] tree113
private theorem sign_113 : 2*denominator*(computed denominator (FixedTape.midBox ibox113)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox113).gradient k).lo.natAbs ((computed denominator ibox113).gradient k).hi.natAbs : Int)*((ibox113 k).hi-(ibox113 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox113
    (computed denominator ibox113) (computed denominator (FixedTape.midBox ibox113))
    (by decide +kernel)
private theorem midpoint_even_113 : ∀ k, 2 ∣ (ibox113 k).lo+(ibox113 k).hi := by decide +kernel
private theorem accepted_113 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox113) tree113 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox113 midpoint_even_113
  simp only [tree113,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox113,candidate_valid h (FixedTape.midBox ibox113),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox113 101 (FixedTape.rowsAux denominator ibox113 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox113) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_113
private noncomputable def tree112 : TapeTree := .split 1 (((988755264935508709305567031693677632603506946076805221580800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree113 tree114
attribute [irreducible] tree112
private theorem accepted_112 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox112) tree112 = true := by
  simp only [tree112,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox112 1 (988755264935508709305567031693677632603506946076805221580800000000000000000000000 : Int) false,decode_split denominator ibox112 1 (988755264935508709305567031693677632603506946076805221580800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_113 h,accepted_114 h⟩
private noncomputable def tree111 : TapeTree := .centered (candidateRows ibox111) (candidateRows (FixedTape.midBox ibox111))
attribute [irreducible] tree111
private theorem sign_111 : 2*denominator*(computed denominator (FixedTape.midBox ibox111)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox111).gradient k).lo.natAbs ((computed denominator ibox111).gradient k).hi.natAbs : Int)*((ibox111 k).hi-(ibox111 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox111
    (computed denominator ibox111) (computed denominator (FixedTape.midBox ibox111))
    (by decide +kernel)
private theorem midpoint_even_111 : ∀ k, 2 ∣ (ibox111 k).lo+(ibox111 k).hi := by decide +kernel
private theorem accepted_111 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox111) tree111 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox111 midpoint_even_111
  simp only [tree111,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox111,candidate_valid h (FixedTape.midBox ibox111),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox111 101 (FixedTape.rowsAux denominator ibox111 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox111) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_111
private noncomputable def tree110 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree111 tree112
attribute [irreducible] tree110
private theorem accepted_110 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox110) tree110 = true := by
  simp only [tree110,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox110 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox110 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_111 h,accepted_112 h⟩
private noncomputable def tree109 : TapeTree := .split 1 (((1018717545691130185345129669017728469955128368685193258598400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree110 tree115
attribute [irreducible] tree109
private theorem accepted_109 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox109) tree109 = true := by
  simp only [tree109,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox109 1 (1018717545691130185345129669017728469955128368685193258598400000000000000000000000 : Int) false,decode_split denominator ibox109 1 (1018717545691130185345129669017728469955128368685193258598400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_110 h,accepted_115 h⟩
private noncomputable def tree108 : TapeTree := .split 1 (((1078642107202373137424254943665830144658371213901969332633600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree109 tree120
attribute [irreducible] tree108
private theorem accepted_108 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox108) tree108 = true := by
  simp only [tree108,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox108 1 (1078642107202373137424254943665830144658371213901969332633600000000000000000000000 : Int) false,decode_split denominator ibox108 1 (1078642107202373137424254943665830144658371213901969332633600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_109 h,accepted_120 h⟩
private noncomputable def tree107 : TapeTree := .split 1 (((1198491230224859041582505492962033494064856904335521480704000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree108 tree131
attribute [irreducible] tree107
private theorem accepted_107 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox107) tree107 = true := by
  simp only [tree107,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox107 1 (1198491230224859041582505492962033494064856904335521480704000000000000000000000000 : Int) false,decode_split denominator ibox107 1 (1198491230224859041582505492962033494064856904335521480704000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_108 h,accepted_131 h⟩
private noncomputable def tree106 : TapeTree := .split 1 (((1438189476269830849899006591554440192877828285202625776844800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree107 tree154
attribute [irreducible] tree106
private theorem accepted_106 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox106) tree106 = true := by
  simp only [tree106,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox106 1 (1438189476269830849899006591554440192877828285202625776844800000000000000000000000 : Int) false,decode_split denominator ibox106 1 (1438189476269830849899006591554440192877828285202625776844800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_107 h,accepted_154 h⟩
private noncomputable def tree105 : TapeTree := .centered (candidateRows ibox105) (candidateRows (FixedTape.midBox ibox105))
attribute [irreducible] tree105
private theorem sign_105 : 2*denominator*(computed denominator (FixedTape.midBox ibox105)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox105).gradient k).lo.natAbs ((computed denominator ibox105).gradient k).hi.natAbs : Int)*((ibox105 k).hi-(ibox105 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox105
    (computed denominator ibox105) (computed denominator (FixedTape.midBox ibox105))
    (by decide +kernel)
private theorem midpoint_even_105 : ∀ k, 2 ∣ (ibox105 k).lo+(ibox105 k).hi := by decide +kernel
private theorem accepted_105 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox105) tree105 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox105 midpoint_even_105
  simp only [tree105,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox105,candidate_valid h (FixedTape.midBox ibox105),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox105 101 (FixedTape.rowsAux denominator ibox105 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox105) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_105
private noncomputable def tree104 : TapeTree := .centered (candidateRows ibox104) (candidateRows (FixedTape.midBox ibox104))
attribute [irreducible] tree104
private theorem sign_104 : 2*denominator*(computed denominator (FixedTape.midBox ibox104)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox104).gradient k).lo.natAbs ((computed denominator ibox104).gradient k).hi.natAbs : Int)*((ibox104 k).hi-(ibox104 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox104
    (computed denominator ibox104) (computed denominator (FixedTape.midBox ibox104))
    (by decide +kernel)
private theorem midpoint_even_104 : ∀ k, 2 ∣ (ibox104 k).lo+(ibox104 k).hi := by decide +kernel
private theorem accepted_104 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox104) tree104 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox104 midpoint_even_104
  simp only [tree104,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox104,candidate_valid h (FixedTape.midBox ibox104),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox104 101 (FixedTape.rowsAux denominator ibox104 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox104) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_104
private noncomputable def tree103 : TapeTree := .split 1 (((928830703424265757226441757045575957900264100860029147545600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree104 tree105
attribute [irreducible] tree103
private theorem accepted_103 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox103) tree103 = true := by
  simp only [tree103,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox103 1 (928830703424265757226441757045575957900264100860029147545600000000000000000000000 : Int) false,decode_split denominator ibox103 1 (928830703424265757226441757045575957900264100860029147545600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_104 h,accepted_105 h⟩
private noncomputable def tree102 : TapeTree := .centered (candidateRows ibox102) (candidateRows (FixedTape.midBox ibox102))
attribute [irreducible] tree102
private theorem sign_102 : 2*denominator*(computed denominator (FixedTape.midBox ibox102)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox102).gradient k).lo.natAbs ((computed denominator ibox102).gradient k).hi.natAbs : Int)*((ibox102 k).hi-(ibox102 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox102
    (computed denominator ibox102) (computed denominator (FixedTape.midBox ibox102))
    (by decide +kernel)
private theorem midpoint_even_102 : ∀ k, 2 ∣ (ibox102 k).lo+(ibox102 k).hi := by decide +kernel
private theorem accepted_102 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox102) tree102 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox102 midpoint_even_102
  simp only [tree102,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox102,candidate_valid h (FixedTape.midBox ibox102),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox102 101 (FixedTape.rowsAux denominator ibox102 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox102) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_102
private noncomputable def tree101 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree102 tree103
attribute [irreducible] tree101
private theorem accepted_101 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox101) tree101 = true := by
  simp only [tree101,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox101 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox101 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_102 h,accepted_103 h⟩
private noncomputable def tree100 : TapeTree := .centered (candidateRows ibox100) (candidateRows (FixedTape.midBox ibox100))
attribute [irreducible] tree100
private theorem sign_100 : 2*denominator*(computed denominator (FixedTape.midBox ibox100)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox100).gradient k).lo.natAbs ((computed denominator ibox100).gradient k).hi.natAbs : Int)*((ibox100 k).hi-(ibox100 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox100
    (computed denominator ibox100) (computed denominator (FixedTape.midBox ibox100))
    (by decide +kernel)
private theorem midpoint_even_100 : ∀ k, 2 ∣ (ibox100 k).lo+(ibox100 k).hi := by decide +kernel
private theorem accepted_100 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox100) tree100 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox100 midpoint_even_100
  simp only [tree100,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox100,candidate_valid h (FixedTape.midBox ibox100),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox100 101 (FixedTape.rowsAux denominator ibox100 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox100) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_100
private noncomputable def tree99 : TapeTree := .centered (candidateRows ibox99) (candidateRows (FixedTape.midBox ibox99))
attribute [irreducible] tree99
private theorem sign_99 : 2*denominator*(computed denominator (FixedTape.midBox ibox99)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox99).gradient k).lo.natAbs ((computed denominator ibox99).gradient k).hi.natAbs : Int)*((ibox99 k).hi-(ibox99 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox99
    (computed denominator ibox99) (computed denominator (FixedTape.midBox ibox99))
    (by decide +kernel)
private theorem midpoint_even_99 : ∀ k, 2 ∣ (ibox99 k).lo+(ibox99 k).hi := by decide +kernel
private theorem accepted_99 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox99) tree99 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox99 midpoint_even_99
  simp only [tree99,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox99,candidate_valid h (FixedTape.midBox ibox99),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox99 101 (FixedTape.rowsAux denominator ibox99 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox99) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_99
private noncomputable def tree98 : TapeTree := .split 1 (((868906141913022805147316482397474283197021255643253073510400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree99 tree100
attribute [irreducible] tree98
private theorem accepted_98 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox98) tree98 = true := by
  simp only [tree98,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox98 1 (868906141913022805147316482397474283197021255643253073510400000000000000000000000 : Int) false,decode_split denominator ibox98 1 (868906141913022805147316482397474283197021255643253073510400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_99 h,accepted_100 h⟩
private noncomputable def tree97 : TapeTree := .centered (candidateRows ibox97) (candidateRows (FixedTape.midBox ibox97))
attribute [irreducible] tree97
private theorem sign_97 : 2*denominator*(computed denominator (FixedTape.midBox ibox97)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox97).gradient k).lo.natAbs ((computed denominator ibox97).gradient k).hi.natAbs : Int)*((ibox97 k).hi-(ibox97 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox97
    (computed denominator ibox97) (computed denominator (FixedTape.midBox ibox97))
    (by decide +kernel)
private theorem midpoint_even_97 : ∀ k, 2 ∣ (ibox97 k).lo+(ibox97 k).hi := by decide +kernel
private theorem accepted_97 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox97) tree97 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox97 midpoint_even_97
  simp only [tree97,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox97,candidate_valid h (FixedTape.midBox ibox97),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox97 101 (FixedTape.rowsAux denominator ibox97 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox97) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_97
private noncomputable def tree96 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree97 tree98
attribute [irreducible] tree96
private theorem accepted_96 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox96) tree96 = true := by
  simp only [tree96,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox96 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox96 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_97 h,accepted_98 h⟩
private noncomputable def tree95 : TapeTree := .split 1 (((898868422668644281186879119721525120548642678251641110528000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree96 tree101
attribute [irreducible] tree95
private theorem accepted_95 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox95) tree95 = true := by
  simp only [tree95,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox95 1 (898868422668644281186879119721525120548642678251641110528000000000000000000000000 : Int) false,decode_split denominator ibox95 1 (898868422668644281186879119721525120548642678251641110528000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_96 h,accepted_101 h⟩
private noncomputable def tree94 : TapeTree := .centered (candidateRows ibox94) (candidateRows (FixedTape.midBox ibox94))
attribute [irreducible] tree94
private theorem sign_94 : 2*denominator*(computed denominator (FixedTape.midBox ibox94)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox94).gradient k).lo.natAbs ((computed denominator ibox94).gradient k).hi.natAbs : Int)*((ibox94 k).hi-(ibox94 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox94
    (computed denominator ibox94) (computed denominator (FixedTape.midBox ibox94))
    (by decide +kernel)
private theorem midpoint_even_94 : ∀ k, 2 ∣ (ibox94 k).lo+(ibox94 k).hi := by decide +kernel
private theorem accepted_94 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox94) tree94 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox94 midpoint_even_94
  simp only [tree94,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox94,candidate_valid h (FixedTape.midBox ibox94),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox94 101 (FixedTape.rowsAux denominator ibox94 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox94) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_94
private noncomputable def tree93 : TapeTree := .centered (candidateRows ibox93) (candidateRows (FixedTape.midBox ibox93))
attribute [irreducible] tree93
private theorem sign_93 : 2*denominator*(computed denominator (FixedTape.midBox ibox93)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox93).gradient k).lo.natAbs ((computed denominator ibox93).gradient k).hi.natAbs : Int)*((ibox93 k).hi-(ibox93 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox93
    (computed denominator ibox93) (computed denominator (FixedTape.midBox ibox93))
    (by decide +kernel)
private theorem midpoint_even_93 : ∀ k, 2 ∣ (ibox93 k).lo+(ibox93 k).hi := by decide +kernel
private theorem accepted_93 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox93) tree93 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox93 midpoint_even_93
  simp only [tree93,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox93,candidate_valid h (FixedTape.midBox ibox93),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox93 101 (FixedTape.rowsAux denominator ibox93 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox93) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_93
private noncomputable def tree92 : TapeTree := .split 1 (((808981580401779853068191207749372608493778410426476999475200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree93 tree94
attribute [irreducible] tree92
private theorem accepted_92 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox92) tree92 = true := by
  simp only [tree92,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox92 1 (808981580401779853068191207749372608493778410426476999475200000000000000000000000 : Int) false,decode_split denominator ibox92 1 (808981580401779853068191207749372608493778410426476999475200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_93 h,accepted_94 h⟩
private noncomputable def tree91 : TapeTree := .centered (candidateRows ibox91) (candidateRows (FixedTape.midBox ibox91))
attribute [irreducible] tree91
private theorem sign_91 : 2*denominator*(computed denominator (FixedTape.midBox ibox91)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox91).gradient k).lo.natAbs ((computed denominator ibox91).gradient k).hi.natAbs : Int)*((ibox91 k).hi-(ibox91 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox91
    (computed denominator ibox91) (computed denominator (FixedTape.midBox ibox91))
    (by decide +kernel)
private theorem midpoint_even_91 : ∀ k, 2 ∣ (ibox91 k).lo+(ibox91 k).hi := by decide +kernel
private theorem accepted_91 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox91) tree91 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox91 midpoint_even_91
  simp only [tree91,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox91,candidate_valid h (FixedTape.midBox ibox91),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox91 101 (FixedTape.rowsAux denominator ibox91 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox91) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_91
private noncomputable def tree90 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree91 tree92
attribute [irreducible] tree90
private theorem accepted_90 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox90) tree90 = true := by
  simp only [tree90,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox90 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox90 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_91 h,accepted_92 h⟩
private noncomputable def tree89 : TapeTree := .centered (candidateRows ibox89) (candidateRows (FixedTape.midBox ibox89))
attribute [irreducible] tree89
private theorem sign_89 : 2*denominator*(computed denominator (FixedTape.midBox ibox89)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox89).gradient k).lo.natAbs ((computed denominator ibox89).gradient k).hi.natAbs : Int)*((ibox89 k).hi-(ibox89 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox89
    (computed denominator ibox89) (computed denominator (FixedTape.midBox ibox89))
    (by decide +kernel)
private theorem midpoint_even_89 : ∀ k, 2 ∣ (ibox89 k).lo+(ibox89 k).hi := by decide +kernel
private theorem accepted_89 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox89) tree89 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox89 midpoint_even_89
  simp only [tree89,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox89,candidate_valid h (FixedTape.midBox ibox89),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox89 101 (FixedTape.rowsAux denominator ibox89 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox89) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_89
private noncomputable def tree88 : TapeTree := .centered (candidateRows ibox88) (candidateRows (FixedTape.midBox ibox88))
attribute [irreducible] tree88
private theorem sign_88 : 2*denominator*(computed denominator (FixedTape.midBox ibox88)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox88).gradient k).lo.natAbs ((computed denominator ibox88).gradient k).hi.natAbs : Int)*((ibox88 k).hi-(ibox88 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox88
    (computed denominator ibox88) (computed denominator (FixedTape.midBox ibox88))
    (by decide +kernel)
private theorem midpoint_even_88 : ∀ k, 2 ∣ (ibox88 k).lo+(ibox88 k).hi := by decide +kernel
private theorem accepted_88 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox88) tree88 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox88 midpoint_even_88
  simp only [tree88,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox88,candidate_valid h (FixedTape.midBox ibox88),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox88 101 (FixedTape.rowsAux denominator ibox88 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox88) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_88
private noncomputable def tree87 : TapeTree := .split 1 (((749057018890536900989065933101270933790535565209700925440000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree88 tree89
attribute [irreducible] tree87
private theorem accepted_87 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox87) tree87 = true := by
  simp only [tree87,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox87 1 (749057018890536900989065933101270933790535565209700925440000000000000000000000000 : Int) false,decode_split denominator ibox87 1 (749057018890536900989065933101270933790535565209700925440000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_88 h,accepted_89 h⟩
private noncomputable def tree86 : TapeTree := .centered (candidateRows ibox86) (candidateRows (FixedTape.midBox ibox86))
attribute [irreducible] tree86
private theorem sign_86 : 2*denominator*(computed denominator (FixedTape.midBox ibox86)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox86).gradient k).lo.natAbs ((computed denominator ibox86).gradient k).hi.natAbs : Int)*((ibox86 k).hi-(ibox86 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox86
    (computed denominator ibox86) (computed denominator (FixedTape.midBox ibox86))
    (by decide +kernel)
private theorem midpoint_even_86 : ∀ k, 2 ∣ (ibox86 k).lo+(ibox86 k).hi := by decide +kernel
private theorem accepted_86 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox86) tree86 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox86 midpoint_even_86
  simp only [tree86,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox86,candidate_valid h (FixedTape.midBox ibox86),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox86 101 (FixedTape.rowsAux denominator ibox86 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox86) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_86
private noncomputable def tree85 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree86 tree87
attribute [irreducible] tree85
private theorem accepted_85 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox85) tree85 = true := by
  simp only [tree85,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox85 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox85 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_86 h,accepted_87 h⟩
private noncomputable def tree84 : TapeTree := .split 1 (((779019299646158377028628570425321771142156987818088962457600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree85 tree90
attribute [irreducible] tree84
private theorem accepted_84 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox84) tree84 = true := by
  simp only [tree84,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox84 1 (779019299646158377028628570425321771142156987818088962457600000000000000000000000 : Int) false,decode_split denominator ibox84 1 (779019299646158377028628570425321771142156987818088962457600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_85 h,accepted_90 h⟩
private noncomputable def tree83 : TapeTree := .split 1 (((838943861157401329107753845073423445845399833034865036492800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree84 tree95
attribute [irreducible] tree83
private theorem accepted_83 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox83) tree83 = true := by
  simp only [tree83,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox83 1 (838943861157401329107753845073423445845399833034865036492800000000000000000000000 : Int) false,decode_split denominator ibox83 1 (838943861157401329107753845073423445845399833034865036492800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_84 h,accepted_95 h⟩
private noncomputable def tree82 : TapeTree := .centered (candidateRows ibox82) (candidateRows (FixedTape.midBox ibox82))
attribute [irreducible] tree82
private theorem sign_82 : 2*denominator*(computed denominator (FixedTape.midBox ibox82)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox82).gradient k).lo.natAbs ((computed denominator ibox82).gradient k).hi.natAbs : Int)*((ibox82 k).hi-(ibox82 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox82
    (computed denominator ibox82) (computed denominator (FixedTape.midBox ibox82))
    (by decide +kernel)
private theorem midpoint_even_82 : ∀ k, 2 ∣ (ibox82 k).lo+(ibox82 k).hi := by decide +kernel
private theorem accepted_82 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox82) tree82 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox82 midpoint_even_82
  simp only [tree82,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox82,candidate_valid h (FixedTape.midBox ibox82),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox82 101 (FixedTape.rowsAux denominator ibox82 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox82) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_82
private noncomputable def tree81 : TapeTree := .centered (candidateRows ibox81) (candidateRows (FixedTape.midBox ibox81))
attribute [irreducible] tree81
private theorem sign_81 : 2*denominator*(computed denominator (FixedTape.midBox ibox81)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox81).gradient k).lo.natAbs ((computed denominator ibox81).gradient k).hi.natAbs : Int)*((ibox81 k).hi-(ibox81 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox81
    (computed denominator ibox81) (computed denominator (FixedTape.midBox ibox81))
    (by decide +kernel)
private theorem midpoint_even_81 : ∀ k, 2 ∣ (ibox81 k).lo+(ibox81 k).hi := by decide +kernel
private theorem accepted_81 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox81) tree81 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox81 midpoint_even_81
  simp only [tree81,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox81,candidate_valid h (FixedTape.midBox ibox81),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox81 101 (FixedTape.rowsAux denominator ibox81 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox81) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_81
private noncomputable def tree80 : TapeTree := .split 1 (((689132457379293948909940658453169259087292719992924851404800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree81 tree82
attribute [irreducible] tree80
private theorem accepted_80 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox80) tree80 = true := by
  simp only [tree80,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox80 1 (689132457379293948909940658453169259087292719992924851404800000000000000000000000 : Int) false,decode_split denominator ibox80 1 (689132457379293948909940658453169259087292719992924851404800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_81 h,accepted_82 h⟩
private noncomputable def tree79 : TapeTree := .centered (candidateRows ibox79) (candidateRows (FixedTape.midBox ibox79))
attribute [irreducible] tree79
private theorem sign_79 : 2*denominator*(computed denominator (FixedTape.midBox ibox79)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox79).gradient k).lo.natAbs ((computed denominator ibox79).gradient k).hi.natAbs : Int)*((ibox79 k).hi-(ibox79 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox79
    (computed denominator ibox79) (computed denominator (FixedTape.midBox ibox79))
    (by decide +kernel)
private theorem midpoint_even_79 : ∀ k, 2 ∣ (ibox79 k).lo+(ibox79 k).hi := by decide +kernel
private theorem accepted_79 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox79) tree79 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox79 midpoint_even_79
  simp only [tree79,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox79,candidate_valid h (FixedTape.midBox ibox79),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox79 101 (FixedTape.rowsAux denominator ibox79 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox79) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_79
private noncomputable def tree78 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree79 tree80
attribute [irreducible] tree78
private theorem accepted_78 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox78) tree78 = true := by
  simp only [tree78,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox78 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox78 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_79 h,accepted_80 h⟩
private noncomputable def tree77 : TapeTree := .centered (candidateRows ibox77) (candidateRows (FixedTape.midBox ibox77))
attribute [irreducible] tree77
private theorem sign_77 : 2*denominator*(computed denominator (FixedTape.midBox ibox77)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox77).gradient k).lo.natAbs ((computed denominator ibox77).gradient k).hi.natAbs : Int)*((ibox77 k).hi-(ibox77 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox77
    (computed denominator ibox77) (computed denominator (FixedTape.midBox ibox77))
    (by decide +kernel)
private theorem midpoint_even_77 : ∀ k, 2 ∣ (ibox77 k).lo+(ibox77 k).hi := by decide +kernel
private theorem accepted_77 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox77) tree77 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox77 midpoint_even_77
  simp only [tree77,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox77,candidate_valid h (FixedTape.midBox ibox77),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox77 101 (FixedTape.rowsAux denominator ibox77 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox77) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_77
private noncomputable def tree76 : TapeTree := .centered (candidateRows ibox76) (candidateRows (FixedTape.midBox ibox76))
attribute [irreducible] tree76
private theorem sign_76 : 2*denominator*(computed denominator (FixedTape.midBox ibox76)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox76).gradient k).lo.natAbs ((computed denominator ibox76).gradient k).hi.natAbs : Int)*((ibox76 k).hi-(ibox76 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox76
    (computed denominator ibox76) (computed denominator (FixedTape.midBox ibox76))
    (by decide +kernel)
private theorem midpoint_even_76 : ∀ k, 2 ∣ (ibox76 k).lo+(ibox76 k).hi := by decide +kernel
private theorem accepted_76 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox76) tree76 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox76 midpoint_even_76
  simp only [tree76,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox76,candidate_valid h (FixedTape.midBox ibox76),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox76 101 (FixedTape.rowsAux denominator ibox76 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox76) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_76
private noncomputable def tree75 : TapeTree := .split 1 (((629207895868050996830815383805067584384049874776148777369600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree76 tree77
attribute [irreducible] tree75
private theorem accepted_75 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox75) tree75 = true := by
  simp only [tree75,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox75 1 (629207895868050996830815383805067584384049874776148777369600000000000000000000000 : Int) false,decode_split denominator ibox75 1 (629207895868050996830815383805067584384049874776148777369600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_76 h,accepted_77 h⟩
private noncomputable def tree74 : TapeTree := .centered (candidateRows ibox74) (candidateRows (FixedTape.midBox ibox74))
attribute [irreducible] tree74
private theorem sign_74 : 2*denominator*(computed denominator (FixedTape.midBox ibox74)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox74).gradient k).lo.natAbs ((computed denominator ibox74).gradient k).hi.natAbs : Int)*((ibox74 k).hi-(ibox74 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox74
    (computed denominator ibox74) (computed denominator (FixedTape.midBox ibox74))
    (by decide +kernel)
private theorem midpoint_even_74 : ∀ k, 2 ∣ (ibox74 k).lo+(ibox74 k).hi := by decide +kernel
private theorem accepted_74 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox74) tree74 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox74 midpoint_even_74
  simp only [tree74,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox74,candidate_valid h (FixedTape.midBox ibox74),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox74 101 (FixedTape.rowsAux denominator ibox74 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox74) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_74
private noncomputable def tree73 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree74 tree75
attribute [irreducible] tree73
private theorem accepted_73 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox73) tree73 = true := by
  simp only [tree73,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox73 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox73 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_74 h,accepted_75 h⟩
private noncomputable def tree72 : TapeTree := .split 1 (((659170176623672472870378021129118421735671297384536814387200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree73 tree78
attribute [irreducible] tree72
private theorem accepted_72 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox72) tree72 = true := by
  simp only [tree72,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox72 1 (659170176623672472870378021129118421735671297384536814387200000000000000000000000 : Int) false,decode_split denominator ibox72 1 (659170176623672472870378021129118421735671297384536814387200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_73 h,accepted_78 h⟩
private noncomputable def tree71 : TapeTree := .centered (candidateRows ibox71) (candidateRows (FixedTape.midBox ibox71))
attribute [irreducible] tree71
private theorem sign_71 : 2*denominator*(computed denominator (FixedTape.midBox ibox71)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox71).gradient k).lo.natAbs ((computed denominator ibox71).gradient k).hi.natAbs : Int)*((ibox71 k).hi-(ibox71 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox71
    (computed denominator ibox71) (computed denominator (FixedTape.midBox ibox71))
    (by decide +kernel)
private theorem midpoint_even_71 : ∀ k, 2 ∣ (ibox71 k).lo+(ibox71 k).hi := by decide +kernel
private theorem accepted_71 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox71) tree71 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox71 midpoint_even_71
  simp only [tree71,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox71,candidate_valid h (FixedTape.midBox ibox71),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox71 101 (FixedTape.rowsAux denominator ibox71 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox71) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_71
private noncomputable def tree70 : TapeTree := .centered (candidateRows ibox70) (candidateRows (FixedTape.midBox ibox70))
attribute [irreducible] tree70
private theorem sign_70 : 2*denominator*(computed denominator (FixedTape.midBox ibox70)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox70).gradient k).lo.natAbs ((computed denominator ibox70).gradient k).hi.natAbs : Int)*((ibox70 k).hi-(ibox70 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox70
    (computed denominator ibox70) (computed denominator (FixedTape.midBox ibox70))
    (by decide +kernel)
private theorem midpoint_even_70 : ∀ k, 2 ∣ (ibox70 k).lo+(ibox70 k).hi := by decide +kernel
private theorem accepted_70 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox70) tree70 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox70 midpoint_even_70
  simp only [tree70,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox70,candidate_valid h (FixedTape.midBox ibox70),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox70 101 (FixedTape.rowsAux denominator ibox70 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox70) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_70
private noncomputable def tree69 : TapeTree := .split 1 (((569283334356808044751690109156965909680807029559372703334400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree70 tree71
attribute [irreducible] tree69
private theorem accepted_69 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox69) tree69 = true := by
  simp only [tree69,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox69 1 (569283334356808044751690109156965909680807029559372703334400000000000000000000000 : Int) false,decode_split denominator ibox69 1 (569283334356808044751690109156965909680807029559372703334400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_70 h,accepted_71 h⟩
private noncomputable def tree68 : TapeTree := .centered (candidateRows ibox68) (candidateRows (FixedTape.midBox ibox68))
attribute [irreducible] tree68
private theorem sign_68 : 2*denominator*(computed denominator (FixedTape.midBox ibox68)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox68).gradient k).lo.natAbs ((computed denominator ibox68).gradient k).hi.natAbs : Int)*((ibox68 k).hi-(ibox68 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox68
    (computed denominator ibox68) (computed denominator (FixedTape.midBox ibox68))
    (by decide +kernel)
private theorem midpoint_even_68 : ∀ k, 2 ∣ (ibox68 k).lo+(ibox68 k).hi := by decide +kernel
private theorem accepted_68 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox68) tree68 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox68 midpoint_even_68
  simp only [tree68,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox68,candidate_valid h (FixedTape.midBox ibox68),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox68 101 (FixedTape.rowsAux denominator ibox68 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox68) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_68
private noncomputable def tree67 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree68 tree69
attribute [irreducible] tree67
private theorem accepted_67 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox67) tree67 = true := by
  simp only [tree67,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox67 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox67 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_68 h,accepted_69 h⟩
private noncomputable def tree66 : TapeTree := .centered (candidateRows ibox66) (candidateRows (FixedTape.midBox ibox66))
attribute [irreducible] tree66
private theorem sign_66 : 2*denominator*(computed denominator (FixedTape.midBox ibox66)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox66).gradient k).lo.natAbs ((computed denominator ibox66).gradient k).hi.natAbs : Int)*((ibox66 k).hi-(ibox66 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox66
    (computed denominator ibox66) (computed denominator (FixedTape.midBox ibox66))
    (by decide +kernel)
private theorem midpoint_even_66 : ∀ k, 2 ∣ (ibox66 k).lo+(ibox66 k).hi := by decide +kernel
private theorem accepted_66 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox66) tree66 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox66 midpoint_even_66
  simp only [tree66,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox66,candidate_valid h (FixedTape.midBox ibox66),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox66 101 (FixedTape.rowsAux denominator ibox66 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox66) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_66
private noncomputable def tree65 : TapeTree := .centered (candidateRows ibox65) (candidateRows (FixedTape.midBox ibox65))
attribute [irreducible] tree65
private theorem sign_65 : 2*denominator*(computed denominator (FixedTape.midBox ibox65)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox65).gradient k).lo.natAbs ((computed denominator ibox65).gradient k).hi.natAbs : Int)*((ibox65 k).hi-(ibox65 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox65
    (computed denominator ibox65) (computed denominator (FixedTape.midBox ibox65))
    (by decide +kernel)
private theorem midpoint_even_65 : ∀ k, 2 ∣ (ibox65 k).lo+(ibox65 k).hi := by decide +kernel
private theorem accepted_65 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox65) tree65 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox65 midpoint_even_65
  simp only [tree65,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox65,candidate_valid h (FixedTape.midBox ibox65),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox65 101 (FixedTape.rowsAux denominator ibox65 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox65) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_65
private noncomputable def tree64 : TapeTree := .split 1 (((509358772845565092672564834508864234977564184342596629299200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree65 tree66
attribute [irreducible] tree64
private theorem accepted_64 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox64) tree64 = true := by
  simp only [tree64,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox64 1 (509358772845565092672564834508864234977564184342596629299200000000000000000000000 : Int) false,decode_split denominator ibox64 1 (509358772845565092672564834508864234977564184342596629299200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_65 h,accepted_66 h⟩
private noncomputable def tree63 : TapeTree := .centered (candidateRows ibox63) (candidateRows (FixedTape.midBox ibox63))
attribute [irreducible] tree63
private theorem sign_63 : 2*denominator*(computed denominator (FixedTape.midBox ibox63)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox63).gradient k).lo.natAbs ((computed denominator ibox63).gradient k).hi.natAbs : Int)*((ibox63 k).hi-(ibox63 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox63
    (computed denominator ibox63) (computed denominator (FixedTape.midBox ibox63))
    (by decide +kernel)
private theorem midpoint_even_63 : ∀ k, 2 ∣ (ibox63 k).lo+(ibox63 k).hi := by decide +kernel
private theorem accepted_63 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox63) tree63 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox63 midpoint_even_63
  simp only [tree63,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox63,candidate_valid h (FixedTape.midBox ibox63),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox63 101 (FixedTape.rowsAux denominator ibox63 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox63) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_63
private noncomputable def tree62 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree63 tree64
attribute [irreducible] tree62
private theorem accepted_62 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox62) tree62 = true := by
  simp only [tree62,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox62 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox62 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_63 h,accepted_64 h⟩
private noncomputable def tree61 : TapeTree := .split 1 (((539321053601186568712127471832915072329185606950984666316800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree62 tree67
attribute [irreducible] tree61
private theorem accepted_61 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox61) tree61 = true := by
  simp only [tree61,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox61 1 (539321053601186568712127471832915072329185606950984666316800000000000000000000000 : Int) false,decode_split denominator ibox61 1 (539321053601186568712127471832915072329185606950984666316800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_62 h,accepted_67 h⟩
private noncomputable def tree60 : TapeTree := .split 1 (((599245615112429520791252746481016747032428452167760740352000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree61 tree72
attribute [irreducible] tree60
private theorem accepted_60 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox60) tree60 = true := by
  simp only [tree60,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox60 1 (599245615112429520791252746481016747032428452167760740352000000000000000000000000 : Int) false,decode_split denominator ibox60 1 (599245615112429520791252746481016747032428452167760740352000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_61 h,accepted_72 h⟩
private noncomputable def tree59 : TapeTree := .split 1 (((719094738134915424949503295777220096438914142601312888422400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree60 tree83
attribute [irreducible] tree59
private theorem accepted_59 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox59) tree59 = true := by
  simp only [tree59,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox59 1 (719094738134915424949503295777220096438914142601312888422400000000000000000000000 : Int) false,decode_split denominator ibox59 1 (719094738134915424949503295777220096438914142601312888422400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_60 h,accepted_83 h⟩
private noncomputable def tree58 : TapeTree := .centered (candidateRows ibox58) (candidateRows (FixedTape.midBox ibox58))
attribute [irreducible] tree58
private theorem sign_58 : 2*denominator*(computed denominator (FixedTape.midBox ibox58)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox58).gradient k).lo.natAbs ((computed denominator ibox58).gradient k).hi.natAbs : Int)*((ibox58 k).hi-(ibox58 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox58
    (computed denominator ibox58) (computed denominator (FixedTape.midBox ibox58))
    (by decide +kernel)
private theorem midpoint_even_58 : ∀ k, 2 ∣ (ibox58 k).lo+(ibox58 k).hi := by decide +kernel
private theorem accepted_58 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox58) tree58 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox58 midpoint_even_58
  simp only [tree58,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox58,candidate_valid h (FixedTape.midBox ibox58),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox58 101 (FixedTape.rowsAux denominator ibox58 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox58) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_58
private noncomputable def tree57 : TapeTree := .centered (candidateRows ibox57) (candidateRows (FixedTape.midBox ibox57))
attribute [irreducible] tree57
private theorem sign_57 : 2*denominator*(computed denominator (FixedTape.midBox ibox57)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox57).gradient k).lo.natAbs ((computed denominator ibox57).gradient k).hi.natAbs : Int)*((ibox57 k).hi-(ibox57 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox57
    (computed denominator ibox57) (computed denominator (FixedTape.midBox ibox57))
    (by decide +kernel)
private theorem midpoint_even_57 : ∀ k, 2 ∣ (ibox57 k).lo+(ibox57 k).hi := by decide +kernel
private theorem accepted_57 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox57) tree57 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox57 midpoint_even_57
  simp only [tree57,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox57,candidate_valid h (FixedTape.midBox ibox57),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox57 101 (FixedTape.rowsAux denominator ibox57 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox57) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_57
private noncomputable def tree56 : TapeTree := .split 1 (((449434211334322140593439559860762560274321339125820555264000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree57 tree58
attribute [irreducible] tree56
private theorem accepted_56 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox56) tree56 = true := by
  simp only [tree56,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox56 1 (449434211334322140593439559860762560274321339125820555264000000000000000000000000 : Int) false,decode_split denominator ibox56 1 (449434211334322140593439559860762560274321339125820555264000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_57 h,accepted_58 h⟩
private noncomputable def tree55 : TapeTree := .centered (candidateRows ibox55) (candidateRows (FixedTape.midBox ibox55))
attribute [irreducible] tree55
private theorem sign_55 : 2*denominator*(computed denominator (FixedTape.midBox ibox55)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox55).gradient k).lo.natAbs ((computed denominator ibox55).gradient k).hi.natAbs : Int)*((ibox55 k).hi-(ibox55 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox55
    (computed denominator ibox55) (computed denominator (FixedTape.midBox ibox55))
    (by decide +kernel)
private theorem midpoint_even_55 : ∀ k, 2 ∣ (ibox55 k).lo+(ibox55 k).hi := by decide +kernel
private theorem accepted_55 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox55) tree55 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox55 midpoint_even_55
  simp only [tree55,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox55,candidate_valid h (FixedTape.midBox ibox55),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox55 101 (FixedTape.rowsAux denominator ibox55 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox55) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_55
private noncomputable def tree54 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree55 tree56
attribute [irreducible] tree54
private theorem accepted_54 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox54) tree54 = true := by
  simp only [tree54,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox54 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox54 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_55 h,accepted_56 h⟩
private noncomputable def tree53 : TapeTree := .centered (candidateRows ibox53) (candidateRows (FixedTape.midBox ibox53))
attribute [irreducible] tree53
private theorem sign_53 : 2*denominator*(computed denominator (FixedTape.midBox ibox53)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox53).gradient k).lo.natAbs ((computed denominator ibox53).gradient k).hi.natAbs : Int)*((ibox53 k).hi-(ibox53 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox53
    (computed denominator ibox53) (computed denominator (FixedTape.midBox ibox53))
    (by decide +kernel)
private theorem midpoint_even_53 : ∀ k, 2 ∣ (ibox53 k).lo+(ibox53 k).hi := by decide +kernel
private theorem accepted_53 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox53) tree53 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox53 midpoint_even_53
  simp only [tree53,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox53,candidate_valid h (FixedTape.midBox ibox53),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox53 101 (FixedTape.rowsAux denominator ibox53 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox53) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_53
private noncomputable def tree52 : TapeTree := .centered (candidateRows ibox52) (candidateRows (FixedTape.midBox ibox52))
attribute [irreducible] tree52
private theorem sign_52 : 2*denominator*(computed denominator (FixedTape.midBox ibox52)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox52).gradient k).lo.natAbs ((computed denominator ibox52).gradient k).hi.natAbs : Int)*((ibox52 k).hi-(ibox52 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox52
    (computed denominator ibox52) (computed denominator (FixedTape.midBox ibox52))
    (by decide +kernel)
private theorem midpoint_even_52 : ∀ k, 2 ∣ (ibox52 k).lo+(ibox52 k).hi := by decide +kernel
private theorem accepted_52 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox52) tree52 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox52 midpoint_even_52
  simp only [tree52,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox52,candidate_valid h (FixedTape.midBox ibox52),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox52 101 (FixedTape.rowsAux denominator ibox52 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox52) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_52
private noncomputable def tree51 : TapeTree := .split 1 (((389509649823079188514314285212660885571078493909044481228800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree52 tree53
attribute [irreducible] tree51
private theorem accepted_51 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox51) tree51 = true := by
  simp only [tree51,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox51 1 (389509649823079188514314285212660885571078493909044481228800000000000000000000000 : Int) false,decode_split denominator ibox51 1 (389509649823079188514314285212660885571078493909044481228800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_52 h,accepted_53 h⟩
private noncomputable def tree50 : TapeTree := .centered (candidateRows ibox50) (candidateRows (FixedTape.midBox ibox50))
attribute [irreducible] tree50
private theorem sign_50 : 2*denominator*(computed denominator (FixedTape.midBox ibox50)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox50).gradient k).lo.natAbs ((computed denominator ibox50).gradient k).hi.natAbs : Int)*((ibox50 k).hi-(ibox50 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox50
    (computed denominator ibox50) (computed denominator (FixedTape.midBox ibox50))
    (by decide +kernel)
private theorem midpoint_even_50 : ∀ k, 2 ∣ (ibox50 k).lo+(ibox50 k).hi := by decide +kernel
private theorem accepted_50 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox50) tree50 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox50 midpoint_even_50
  simp only [tree50,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox50,candidate_valid h (FixedTape.midBox ibox50),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox50 101 (FixedTape.rowsAux denominator ibox50 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox50) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_50
private noncomputable def tree49 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree50 tree51
attribute [irreducible] tree49
private theorem accepted_49 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox49) tree49 = true := by
  simp only [tree49,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox49 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox49 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_50 h,accepted_51 h⟩
private noncomputable def tree48 : TapeTree := .split 1 (((419471930578700664553876922536711722922699916517432518246400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree49 tree54
attribute [irreducible] tree48
private theorem accepted_48 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox48) tree48 = true := by
  simp only [tree48,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox48 1 (419471930578700664553876922536711722922699916517432518246400000000000000000000000 : Int) false,decode_split denominator ibox48 1 (419471930578700664553876922536711722922699916517432518246400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_49 h,accepted_54 h⟩
private noncomputable def tree47 : TapeTree := .centered (candidateRows ibox47) (candidateRows (FixedTape.midBox ibox47))
attribute [irreducible] tree47
private theorem sign_47 : 2*denominator*(computed denominator (FixedTape.midBox ibox47)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox47).gradient k).lo.natAbs ((computed denominator ibox47).gradient k).hi.natAbs : Int)*((ibox47 k).hi-(ibox47 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox47
    (computed denominator ibox47) (computed denominator (FixedTape.midBox ibox47))
    (by decide +kernel)
private theorem midpoint_even_47 : ∀ k, 2 ∣ (ibox47 k).lo+(ibox47 k).hi := by decide +kernel
private theorem accepted_47 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox47) tree47 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox47 midpoint_even_47
  simp only [tree47,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox47,candidate_valid h (FixedTape.midBox ibox47),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox47 101 (FixedTape.rowsAux denominator ibox47 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox47) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_47
private noncomputable def tree46 : TapeTree := .centered (candidateRows ibox46) (candidateRows (FixedTape.midBox ibox46))
attribute [irreducible] tree46
private theorem sign_46 : 2*denominator*(computed denominator (FixedTape.midBox ibox46)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox46).gradient k).lo.natAbs ((computed denominator ibox46).gradient k).hi.natAbs : Int)*((ibox46 k).hi-(ibox46 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox46
    (computed denominator ibox46) (computed denominator (FixedTape.midBox ibox46))
    (by decide +kernel)
private theorem midpoint_even_46 : ∀ k, 2 ∣ (ibox46 k).lo+(ibox46 k).hi := by decide +kernel
private theorem accepted_46 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox46) tree46 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox46 midpoint_even_46
  simp only [tree46,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox46,candidate_valid h (FixedTape.midBox ibox46),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox46 101 (FixedTape.rowsAux denominator ibox46 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox46) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_46
private noncomputable def tree45 : TapeTree := .split 2 (((2876378952539661699798013183108880385755656570405251553689600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree46 tree47
attribute [irreducible] tree45
private theorem accepted_45 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox45) tree45 = true := by
  simp only [tree45,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox45 2 (2876378952539661699798013183108880385755656570405251553689600000000000000000000000 : Int) false,decode_split denominator ibox45 2 (2876378952539661699798013183108880385755656570405251553689600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_46 h,accepted_47 h⟩
private noncomputable def tree44 : TapeTree := .centered (candidateRows ibox44) (candidateRows (FixedTape.midBox ibox44))
attribute [irreducible] tree44
private theorem sign_44 : 2*denominator*(computed denominator (FixedTape.midBox ibox44)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox44).gradient k).lo.natAbs ((computed denominator ibox44).gradient k).hi.natAbs : Int)*((ibox44 k).hi-(ibox44 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox44
    (computed denominator ibox44) (computed denominator (FixedTape.midBox ibox44))
    (by decide +kernel)
private theorem midpoint_even_44 : ∀ k, 2 ∣ (ibox44 k).lo+(ibox44 k).hi := by decide +kernel
private theorem accepted_44 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox44) tree44 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox44 midpoint_even_44
  simp only [tree44,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox44,candidate_valid h (FixedTape.midBox ibox44),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox44 101 (FixedTape.rowsAux denominator ibox44 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox44) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_44
private noncomputable def tree43 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree44 tree45
attribute [irreducible] tree43
private theorem accepted_43 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox43) tree43 = true := by
  simp only [tree43,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox43 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox43 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_44 h,accepted_45 h⟩
private noncomputable def tree42 : TapeTree := .centered (candidateRows ibox42) (candidateRows (FixedTape.midBox ibox42))
attribute [irreducible] tree42
private theorem sign_42 : 2*denominator*(computed denominator (FixedTape.midBox ibox42)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox42).gradient k).lo.natAbs ((computed denominator ibox42).gradient k).hi.natAbs : Int)*((ibox42 k).hi-(ibox42 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox42
    (computed denominator ibox42) (computed denominator (FixedTape.midBox ibox42))
    (by decide +kernel)
private theorem midpoint_even_42 : ∀ k, 2 ∣ (ibox42 k).lo+(ibox42 k).hi := by decide +kernel
private theorem accepted_42 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox42) tree42 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox42 midpoint_even_42
  simp only [tree42,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox42,candidate_valid h (FixedTape.midBox ibox42),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox42 101 (FixedTape.rowsAux denominator ibox42 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox42) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_42
private noncomputable def tree41 : TapeTree := .centered (candidateRows ibox41) (candidateRows (FixedTape.midBox ibox41))
attribute [irreducible] tree41
private theorem sign_41 : 2*denominator*(computed denominator (FixedTape.midBox ibox41)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox41).gradient k).lo.natAbs ((computed denominator ibox41).gradient k).hi.natAbs : Int)*((ibox41 k).hi-(ibox41 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox41
    (computed denominator ibox41) (computed denominator (FixedTape.midBox ibox41))
    (by decide +kernel)
private theorem midpoint_even_41 : ∀ k, 2 ∣ (ibox41 k).lo+(ibox41 k).hi := by decide +kernel
private theorem accepted_41 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox41) tree41 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox41 midpoint_even_41
  simp only [tree41,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox41,candidate_valid h (FixedTape.midBox ibox41),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox41 101 (FixedTape.rowsAux denominator ibox41 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox41) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_41
private noncomputable def tree40 : TapeTree := .split 2 (((2876378952539661699798013183108880385755656570405251553689600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree41 tree42
attribute [irreducible] tree40
private theorem accepted_40 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox40) tree40 = true := by
  simp only [tree40,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox40 2 (2876378952539661699798013183108880385755656570405251553689600000000000000000000000 : Int) false,decode_split denominator ibox40 2 (2876378952539661699798013183108880385755656570405251553689600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_41 h,accepted_42 h⟩
private noncomputable def tree39 : TapeTree := .centered (candidateRows ibox39) (candidateRows (FixedTape.midBox ibox39))
attribute [irreducible] tree39
private theorem sign_39 : 2*denominator*(computed denominator (FixedTape.midBox ibox39)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox39).gradient k).lo.natAbs ((computed denominator ibox39).gradient k).hi.natAbs : Int)*((ibox39 k).hi-(ibox39 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox39
    (computed denominator ibox39) (computed denominator (FixedTape.midBox ibox39))
    (by decide +kernel)
private theorem midpoint_even_39 : ∀ k, 2 ∣ (ibox39 k).lo+(ibox39 k).hi := by decide +kernel
private theorem accepted_39 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox39) tree39 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox39 midpoint_even_39
  simp only [tree39,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox39,candidate_valid h (FixedTape.midBox ibox39),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox39 101 (FixedTape.rowsAux denominator ibox39 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox39) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_39
private noncomputable def tree38 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree39 tree40
attribute [irreducible] tree38
private theorem accepted_38 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox38) tree38 = true := by
  simp only [tree38,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox38 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox38 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_39 h,accepted_40 h⟩
private noncomputable def tree37 : TapeTree := .split 1 (((299622807556214760395626373240508373516214226083880370176000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree38 tree43
attribute [irreducible] tree37
private theorem accepted_37 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox37) tree37 = true := by
  simp only [tree37,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox37 1 (299622807556214760395626373240508373516214226083880370176000000000000000000000000 : Int) false,decode_split denominator ibox37 1 (299622807556214760395626373240508373516214226083880370176000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_38 h,accepted_43 h⟩
private noncomputable def tree36 : TapeTree := .split 1 (((359547369067457712474751647888610048219457071300656444211200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree37 tree48
attribute [irreducible] tree36
private theorem accepted_36 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox36) tree36 = true := by
  simp only [tree36,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox36 1 (359547369067457712474751647888610048219457071300656444211200000000000000000000000 : Int) false,decode_split denominator ibox36 1 (359547369067457712474751647888610048219457071300656444211200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_37 h,accepted_48 h⟩
private noncomputable def tree35 : TapeTree := .centered (candidateRows ibox35) (candidateRows (FixedTape.midBox ibox35))
attribute [irreducible] tree35
private theorem sign_35 : 2*denominator*(computed denominator (FixedTape.midBox ibox35)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox35).gradient k).lo.natAbs ((computed denominator ibox35).gradient k).hi.natAbs : Int)*((ibox35 k).hi-(ibox35 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox35
    (computed denominator ibox35) (computed denominator (FixedTape.midBox ibox35))
    (by decide +kernel)
private theorem midpoint_even_35 : ∀ k, 2 ∣ (ibox35 k).lo+(ibox35 k).hi := by decide +kernel
private theorem accepted_35 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox35) tree35 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox35 midpoint_even_35
  simp only [tree35,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox35,candidate_valid h (FixedTape.midBox ibox35),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox35 101 (FixedTape.rowsAux denominator ibox35 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox35) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_35
private noncomputable def tree34 : TapeTree := .centered (candidateRows ibox34) (candidateRows (FixedTape.midBox ibox34))
attribute [irreducible] tree34
private theorem sign_34 : 2*denominator*(computed denominator (FixedTape.midBox ibox34)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox34).gradient k).lo.natAbs ((computed denominator ibox34).gradient k).hi.natAbs : Int)*((ibox34 k).hi-(ibox34 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox34
    (computed denominator ibox34) (computed denominator (FixedTape.midBox ibox34))
    (by decide +kernel)
private theorem midpoint_even_34 : ∀ k, 2 ∣ (ibox34 k).lo+(ibox34 k).hi := by decide +kernel
private theorem accepted_34 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox34) tree34 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox34 midpoint_even_34
  simp only [tree34,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox34,candidate_valid h (FixedTape.midBox ibox34),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox34 101 (FixedTape.rowsAux denominator ibox34 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox34) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_34
private noncomputable def tree33 : TapeTree := .split 1 (((209735965289350332276938461268355861461349958258716259123200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree34 tree35
attribute [irreducible] tree33
private theorem accepted_33 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox33) tree33 = true := by
  simp only [tree33,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox33 1 (209735965289350332276938461268355861461349958258716259123200000000000000000000000 : Int) false,decode_split denominator ibox33 1 (209735965289350332276938461268355861461349958258716259123200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_34 h,accepted_35 h⟩
private noncomputable def tree32 : TapeTree := .centered (candidateRows ibox32) (candidateRows (FixedTape.midBox ibox32))
attribute [irreducible] tree32
private theorem sign_32 : 2*denominator*(computed denominator (FixedTape.midBox ibox32)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox32).gradient k).lo.natAbs ((computed denominator ibox32).gradient k).hi.natAbs : Int)*((ibox32 k).hi-(ibox32 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox32
    (computed denominator ibox32) (computed denominator (FixedTape.midBox ibox32))
    (by decide +kernel)
private theorem midpoint_even_32 : ∀ k, 2 ∣ (ibox32 k).lo+(ibox32 k).hi := by decide +kernel
private theorem accepted_32 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox32) tree32 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox32 midpoint_even_32
  simp only [tree32,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox32,candidate_valid h (FixedTape.midBox ibox32),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox32 101 (FixedTape.rowsAux denominator ibox32 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox32) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_32
private noncomputable def tree31 : TapeTree := .split 2 (((2876378952539661699798013183108880385755656570405251553689600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree32 tree33
attribute [irreducible] tree31
private theorem accepted_31 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox31) tree31 = true := by
  simp only [tree31,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox31 2 (2876378952539661699798013183108880385755656570405251553689600000000000000000000000 : Int) false,decode_split denominator ibox31 2 (2876378952539661699798013183108880385755656570405251553689600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_32 h,accepted_33 h⟩
private noncomputable def tree30 : TapeTree := .centered (candidateRows ibox30) (candidateRows (FixedTape.midBox ibox30))
attribute [irreducible] tree30
private theorem sign_30 : 2*denominator*(computed denominator (FixedTape.midBox ibox30)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox30).gradient k).lo.natAbs ((computed denominator ibox30).gradient k).hi.natAbs : Int)*((ibox30 k).hi-(ibox30 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox30
    (computed denominator ibox30) (computed denominator (FixedTape.midBox ibox30))
    (by decide +kernel)
private theorem midpoint_even_30 : ∀ k, 2 ∣ (ibox30 k).lo+(ibox30 k).hi := by decide +kernel
private theorem accepted_30 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox30) tree30 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox30 midpoint_even_30
  simp only [tree30,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox30,candidate_valid h (FixedTape.midBox ibox30),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox30 101 (FixedTape.rowsAux denominator ibox30 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox30) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_30
private noncomputable def tree29 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree30 tree31
attribute [irreducible] tree29
private theorem accepted_29 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox29) tree29 = true := by
  simp only [tree29,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox29 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox29 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_30 h,accepted_31 h⟩
private noncomputable def tree28 : TapeTree := .centered (candidateRows ibox28) (candidateRows (FixedTape.midBox ibox28))
attribute [irreducible] tree28
private theorem sign_28 : 2*denominator*(computed denominator (FixedTape.midBox ibox28)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox28).gradient k).lo.natAbs ((computed denominator ibox28).gradient k).hi.natAbs : Int)*((ibox28 k).hi-(ibox28 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox28
    (computed denominator ibox28) (computed denominator (FixedTape.midBox ibox28))
    (by decide +kernel)
private theorem midpoint_even_28 : ∀ k, 2 ∣ (ibox28 k).lo+(ibox28 k).hi := by decide +kernel
private theorem accepted_28 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox28) tree28 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox28 midpoint_even_28
  simp only [tree28,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox28,candidate_valid h (FixedTape.midBox ibox28),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox28 101 (FixedTape.rowsAux denominator ibox28 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox28) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_28
private noncomputable def tree27 : TapeTree := .centered (candidateRows ibox27) (candidateRows (FixedTape.midBox ibox27))
attribute [irreducible] tree27
private theorem sign_27 : 2*denominator*(computed denominator (FixedTape.midBox ibox27)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox27).gradient k).lo.natAbs ((computed denominator ibox27).gradient k).hi.natAbs : Int)*((ibox27 k).hi-(ibox27 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox27
    (computed denominator ibox27) (computed denominator (FixedTape.midBox ibox27))
    (by decide +kernel)
private theorem midpoint_even_27 : ∀ k, 2 ∣ (ibox27 k).lo+(ibox27 k).hi := by decide +kernel
private theorem accepted_27 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox27) tree27 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox27 midpoint_even_27
  simp only [tree27,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox27,candidate_valid h (FixedTape.midBox ibox27),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox27 101 (FixedTape.rowsAux denominator ibox27 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox27) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_27
private noncomputable def tree26 : TapeTree := .split 1 (((149811403778107380197813186620254186758107113041940185088000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree27 tree28
attribute [irreducible] tree26
private theorem accepted_26 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox26) tree26 = true := by
  simp only [tree26,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox26 1 (149811403778107380197813186620254186758107113041940185088000000000000000000000000 : Int) false,decode_split denominator ibox26 1 (149811403778107380197813186620254186758107113041940185088000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_27 h,accepted_28 h⟩
private noncomputable def tree25 : TapeTree := .centered (candidateRows ibox25) (candidateRows (FixedTape.midBox ibox25))
attribute [irreducible] tree25
private theorem sign_25 : 2*denominator*(computed denominator (FixedTape.midBox ibox25)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox25).gradient k).lo.natAbs ((computed denominator ibox25).gradient k).hi.natAbs : Int)*((ibox25 k).hi-(ibox25 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox25
    (computed denominator ibox25) (computed denominator (FixedTape.midBox ibox25))
    (by decide +kernel)
private theorem midpoint_even_25 : ∀ k, 2 ∣ (ibox25 k).lo+(ibox25 k).hi := by decide +kernel
private theorem accepted_25 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox25) tree25 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox25 midpoint_even_25
  simp only [tree25,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox25,candidate_valid h (FixedTape.midBox ibox25),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox25 101 (FixedTape.rowsAux denominator ibox25 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox25) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_25
private noncomputable def tree24 : TapeTree := .split 2 (((2876378952539661699798013183108880385755656570405251553689600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree25 tree26
attribute [irreducible] tree24
private theorem accepted_24 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox24) tree24 = true := by
  simp only [tree24,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox24 2 (2876378952539661699798013183108880385755656570405251553689600000000000000000000000 : Int) false,decode_split denominator ibox24 2 (2876378952539661699798013183108880385755656570405251553689600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_25 h,accepted_26 h⟩
private noncomputable def tree23 : TapeTree := .centered (candidateRows ibox23) (candidateRows (FixedTape.midBox ibox23))
attribute [irreducible] tree23
private theorem sign_23 : 2*denominator*(computed denominator (FixedTape.midBox ibox23)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox23).gradient k).lo.natAbs ((computed denominator ibox23).gradient k).hi.natAbs : Int)*((ibox23 k).hi-(ibox23 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox23
    (computed denominator ibox23) (computed denominator (FixedTape.midBox ibox23))
    (by decide +kernel)
private theorem midpoint_even_23 : ∀ k, 2 ∣ (ibox23 k).lo+(ibox23 k).hi := by decide +kernel
private theorem accepted_23 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox23) tree23 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox23 midpoint_even_23
  simp only [tree23,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox23,candidate_valid h (FixedTape.midBox ibox23),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox23 101 (FixedTape.rowsAux denominator ibox23 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox23) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_23
private noncomputable def tree22 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree23 tree24
attribute [irreducible] tree22
private theorem accepted_22 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox22) tree22 = true := by
  simp only [tree22,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox22 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox22 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_23 h,accepted_24 h⟩
private noncomputable def tree21 : TapeTree := .split 1 (((179773684533728856237375823944305024109728535650328222105600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree22 tree29
attribute [irreducible] tree21
private theorem accepted_21 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox21) tree21 = true := by
  simp only [tree21,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox21 1 (179773684533728856237375823944305024109728535650328222105600000000000000000000000 : Int) false,decode_split denominator ibox21 1 (179773684533728856237375823944305024109728535650328222105600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_22 h,accepted_29 h⟩
private noncomputable def tree20 : TapeTree := .centered (candidateRows ibox20) (candidateRows (FixedTape.midBox ibox20))
attribute [irreducible] tree20
private theorem sign_20 : 2*denominator*(computed denominator (FixedTape.midBox ibox20)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox20).gradient k).lo.natAbs ((computed denominator ibox20).gradient k).hi.natAbs : Int)*((ibox20 k).hi-(ibox20 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox20
    (computed denominator ibox20) (computed denominator (FixedTape.midBox ibox20))
    (by decide +kernel)
private theorem midpoint_even_20 : ∀ k, 2 ∣ (ibox20 k).lo+(ibox20 k).hi := by decide +kernel
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox20 midpoint_even_20
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox20,candidate_valid h (FixedTape.midBox ibox20),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox20 101 (FixedTape.rowsAux denominator ibox20 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox20) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_20
private noncomputable def tree19 : TapeTree := .centered (candidateRows ibox19) (candidateRows (FixedTape.midBox ibox19))
attribute [irreducible] tree19
private theorem sign_19 : 2*denominator*(computed denominator (FixedTape.midBox ibox19)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox19).gradient k).lo.natAbs ((computed denominator ibox19).gradient k).hi.natAbs : Int)*((ibox19 k).hi-(ibox19 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox19
    (computed denominator ibox19) (computed denominator (FixedTape.midBox ibox19))
    (by decide +kernel)
private theorem midpoint_even_19 : ∀ k, 2 ∣ (ibox19 k).lo+(ibox19 k).hi := by decide +kernel
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox19 midpoint_even_19
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox19,candidate_valid h (FixedTape.midBox ibox19),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox19 101 (FixedTape.rowsAux denominator ibox19 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox19) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_19
private noncomputable def tree18 : TapeTree := .split 1 (((89886842266864428118687911972152512054864267825164111052800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree19 tree20
attribute [irreducible] tree18
private theorem accepted_18 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox18) tree18 = true := by
  simp only [tree18,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox18 1 (89886842266864428118687911972152512054864267825164111052800000000000000000000000 : Int) false,decode_split denominator ibox18 1 (89886842266864428118687911972152512054864267825164111052800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_19 h,accepted_20 h⟩
private noncomputable def tree17 : TapeTree := .centered (candidateRows ibox17) (candidateRows (FixedTape.midBox ibox17))
attribute [irreducible] tree17
private theorem sign_17 : 2*denominator*(computed denominator (FixedTape.midBox ibox17)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox17).gradient k).lo.natAbs ((computed denominator ibox17).gradient k).hi.natAbs : Int)*((ibox17 k).hi-(ibox17 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox17
    (computed denominator ibox17) (computed denominator (FixedTape.midBox ibox17))
    (by decide +kernel)
private theorem midpoint_even_17 : ∀ k, 2 ∣ (ibox17 k).lo+(ibox17 k).hi := by decide +kernel
private theorem accepted_17 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox17) tree17 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox17 midpoint_even_17
  simp only [tree17,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox17,candidate_valid h (FixedTape.midBox ibox17),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox17 101 (FixedTape.rowsAux denominator ibox17 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox17) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_17
private noncomputable def tree16 : TapeTree := .split 2 (((2876378952539661699798013183108880385755656570405251553689600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree17 tree18
attribute [irreducible] tree16
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox16 2 (2876378952539661699798013183108880385755656570405251553689600000000000000000000000 : Int) false,decode_split denominator ibox16 2 (2876378952539661699798013183108880385755656570405251553689600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_17 h,accepted_18 h⟩
private noncomputable def tree15 : TapeTree := .centered (candidateRows ibox15) (candidateRows (FixedTape.midBox ibox15))
attribute [irreducible] tree15
private theorem sign_15 : 2*denominator*(computed denominator (FixedTape.midBox ibox15)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox15).gradient k).lo.natAbs ((computed denominator ibox15).gradient k).hi.natAbs : Int)*((ibox15 k).hi-(ibox15 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox15
    (computed denominator ibox15) (computed denominator (FixedTape.midBox ibox15))
    (by decide +kernel)
private theorem midpoint_even_15 : ∀ k, 2 ∣ (ibox15 k).lo+(ibox15 k).hi := by decide +kernel
private theorem accepted_15 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox15) tree15 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox15 midpoint_even_15
  simp only [tree15,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox15,candidate_valid h (FixedTape.midBox ibox15),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox15 101 (FixedTape.rowsAux denominator ibox15 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox15) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_15
private noncomputable def tree14 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree15 tree16
attribute [irreducible] tree14
private theorem accepted_14 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox14) tree14 = true := by
  simp only [tree14,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox14 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox14 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_15 h,accepted_16 h⟩
private noncomputable def tree13 : TapeTree := .centered (candidateRows ibox13) (candidateRows (FixedTape.midBox ibox13))
attribute [irreducible] tree13
private theorem sign_13 : 2*denominator*(computed denominator (FixedTape.midBox ibox13)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox13).gradient k).lo.natAbs ((computed denominator ibox13).gradient k).hi.natAbs : Int)*((ibox13 k).hi-(ibox13 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox13
    (computed denominator ibox13) (computed denominator (FixedTape.midBox ibox13))
    (by decide +kernel)
private theorem midpoint_even_13 : ∀ k, 2 ∣ (ibox13 k).lo+(ibox13 k).hi := by decide +kernel
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox13 midpoint_even_13
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox13,candidate_valid h (FixedTape.midBox ibox13),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox13 101 (FixedTape.rowsAux denominator ibox13 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox13) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_13
private noncomputable def tree12 : TapeTree := .centered (candidateRows ibox12) (candidateRows (FixedTape.midBox ibox12))
attribute [irreducible] tree12
private theorem sign_12 : 2*denominator*(computed denominator (FixedTape.midBox ibox12)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox12).gradient k).lo.natAbs ((computed denominator ibox12).gradient k).hi.natAbs : Int)*((ibox12 k).hi-(ibox12 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox12
    (computed denominator ibox12) (computed denominator (FixedTape.midBox ibox12))
    (by decide +kernel)
private theorem midpoint_even_12 : ∀ k, 2 ∣ (ibox12 k).lo+(ibox12 k).hi := by decide +kernel
private theorem accepted_12 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox12) tree12 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox12 midpoint_even_12
  simp only [tree12,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox12,candidate_valid h (FixedTape.midBox ibox12),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox12 101 (FixedTape.rowsAux denominator ibox12 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox12) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_12
private noncomputable def tree11 : TapeTree := .split 1 (((29962280755621476039562637324050837351621422608388037017600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree12 tree13
attribute [irreducible] tree11
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox11 1 (29962280755621476039562637324050837351621422608388037017600000000000000000000000 : Int) false,decode_split denominator ibox11 1 (29962280755621476039562637324050837351621422608388037017600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_12 h,accepted_13 h⟩
private noncomputable def tree10 : TapeTree := .centered (candidateRows ibox10) (candidateRows (FixedTape.midBox ibox10))
attribute [irreducible] tree10
private theorem sign_10 : 2*denominator*(computed denominator (FixedTape.midBox ibox10)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox10).gradient k).lo.natAbs ((computed denominator ibox10).gradient k).hi.natAbs : Int)*((ibox10 k).hi-(ibox10 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox10
    (computed denominator ibox10) (computed denominator (FixedTape.midBox ibox10))
    (by decide +kernel)
private theorem midpoint_even_10 : ∀ k, 2 ∣ (ibox10 k).lo+(ibox10 k).hi := by decide +kernel
private theorem accepted_10 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox10) tree10 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox10 midpoint_even_10
  simp only [tree10,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox10,candidate_valid h (FixedTape.midBox ibox10),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox10 101 (FixedTape.rowsAux denominator ibox10 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox10) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_10
private noncomputable def tree9 : TapeTree := .split 2 (((2876378952539661699798013183108880385755656570405251553689600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree10 tree11
attribute [irreducible] tree9
private theorem accepted_9 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox9) tree9 = true := by
  simp only [tree9,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox9 2 (2876378952539661699798013183108880385755656570405251553689600000000000000000000000 : Int) false,decode_split denominator ibox9 2 (2876378952539661699798013183108880385755656570405251553689600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_10 h,accepted_11 h⟩
private noncomputable def tree8 : TapeTree := .centered (candidateRows ibox8) (candidateRows (FixedTape.midBox ibox8))
attribute [irreducible] tree8
private theorem sign_8 : 2*denominator*(computed denominator (FixedTape.midBox ibox8)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox8).gradient k).lo.natAbs ((computed denominator ibox8).gradient k).hi.natAbs : Int)*((ibox8 k).hi-(ibox8 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox8
    (computed denominator ibox8) (computed denominator (FixedTape.midBox ibox8))
    (by decide +kernel)
private theorem midpoint_even_8 : ∀ k, 2 ∣ (ibox8 k).lo+(ibox8 k).hi := by decide +kernel
private theorem accepted_8 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox8) tree8 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox8 midpoint_even_8
  simp only [tree8,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox8,candidate_valid h (FixedTape.midBox ibox8),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox8 101 (FixedTape.rowsAux denominator ibox8 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox8) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_8
private noncomputable def tree7 : TapeTree := .split 2 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree8 tree9
attribute [irreducible] tree7
private theorem accepted_7 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox7) tree7 = true := by
  simp only [tree7,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox7 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox7 2 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_8 h,accepted_9 h⟩
private noncomputable def tree6 : TapeTree := .split 1 (((59924561511242952079125274648101674703242845216776074035200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree7 tree14
attribute [irreducible] tree6
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox6 1 (59924561511242952079125274648101674703242845216776074035200000000000000000000000 : Int) false,decode_split denominator ibox6 1 (59924561511242952079125274648101674703242845216776074035200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_7 h,accepted_14 h⟩
private noncomputable def tree5 : TapeTree := .split 1 (((119849123022485904158250549296203349406485690433552148070400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree6 tree21
attribute [irreducible] tree5
private theorem accepted_5 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox5) tree5 = true := by
  simp only [tree5,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox5 1 (119849123022485904158250549296203349406485690433552148070400000000000000000000000 : Int) false,decode_split denominator ibox5 1 (119849123022485904158250549296203349406485690433552148070400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_6 h,accepted_21 h⟩
private noncomputable def tree4 : TapeTree := .split 1 (((239698246044971808316501098592406698812971380867104296140800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree5 tree36
attribute [irreducible] tree4
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox4 1 (239698246044971808316501098592406698812971380867104296140800000000000000000000000 : Int) false,decode_split denominator ibox4 1 (239698246044971808316501098592406698812971380867104296140800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_5 h,accepted_36 h⟩
private noncomputable def tree3 : TapeTree := .split 1 (((479396492089943616633002197184813397625942761734208592281600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree4 tree59
attribute [irreducible] tree3
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox3 1 (479396492089943616633002197184813397625942761734208592281600000000000000000000000 : Int) false,decode_split denominator ibox3 1 (479396492089943616633002197184813397625942761734208592281600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_4 h,accepted_59 h⟩
private noncomputable def tree2 : TapeTree := .split 1 (((958792984179887233266004394369626795251885523468417184563200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree106
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 1 (958792984179887233266004394369626795251885523468417184563200000000000000000000000 : Int) false,decode_split denominator ibox2 1 (958792984179887233266004394369626795251885523468417184563200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_3 h,accepted_106 h⟩
private noncomputable def tree1 : TapeTree := .split 1 (((1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree2 tree199
attribute [irreducible] tree1
private theorem accepted_1 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox1) tree1 = true := by
  simp only [tree1,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox1 1 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) false,decode_split denominator ibox1 1 (1917585968359774466532008788739253590503771046936834369126400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_2 h,accepted_199 h⟩
private noncomputable def tree0 : TapeTree := .face 3 true (candidateRows ibox0) tree1
attribute [irreducible] tree0
private theorem sign_0 : 0 ≤ ((computed denominator ibox0).gradient 3).lo := by decide +kernel
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 101 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox0,?_,accepted_1 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox0)).gradient 3).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox0).gradient 3).lo) denominator_positive).2 sign_0
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (4947916666666667/5000000000000000 : ℚ) (99/100 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 101 = e104 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (4947916666666667/5000000000000000 : ℚ) (99/100 : ℚ)) x → eval e104 x ≤ 0 := by
  have hb := h.child_4 tape 101 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell126_high_first_top

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell126_high_first_top
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((4947916666666667/5000000000000000 : ℚ) : ℝ) < p ∧ p ≤ ((99/100 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 126 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 126 p)
    (hkb : ((99/100 : ℚ) : ℝ) ≤ bStar ∨ bStar ≤ ((4947916666666667/5000000000000000 : ℚ) : ℝ))
    (hr : r ∈ Icc bStar (1 : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ min p r)
    (hcase : bStar < a), firstResidual (0 : Fin 9) a p r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell126_high_first_top.cell_bound h.child_8 h.child_9 (Cell126_high_first_top.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell126_high_first_top
