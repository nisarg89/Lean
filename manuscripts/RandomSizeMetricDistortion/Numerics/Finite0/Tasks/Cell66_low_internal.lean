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
namespace Cell66_low_internal
private noncomputable def qValues : Fin 4 → ℚ := ![(52725098717072542426821748833144481/66665788524178440801773277370327908 : ℚ),(65986015427100985465340000000000000/49999341393133830601329958027745931 : ℚ),(6402383253918603178195662672358127311/2515757284353934450687789099231147513 : ℚ),(-3389525048522526279265000000000000000/2515757284353934450687789099231147513 : ℚ)]
private noncomputable abbrev e2 : PolyExpr := SharedFiniteSemantics15.e2 qValues
private noncomputable abbrev e11 : PolyExpr := SharedFiniteSemantics15.e11 qValues
private noncomputable abbrev e12 : PolyExpr := SharedFiniteSemantics15.e12 qValues
private noncomputable abbrev e16 : PolyExpr := SharedFiniteSemantics15.e16 qValues
private noncomputable abbrev e18 : PolyExpr := SharedFiniteSemantics15.e18 qValues
private noncomputable abbrev e114 : PolyExpr := SharedFiniteSemantics15.e114 qValues
private noncomputable abbrev node_1 := SharedFiniteSemantics15.node_1 qValues
private noncomputable abbrev node_2 := SharedFiniteSemantics15.node_2 qValues
private noncomputable abbrev node_3 := SharedFiniteSemantics15.node_3 qValues
private noncomputable abbrev node_4 := SharedFiniteSemantics15.node_4 qValues
private noncomputable abbrev node_5 := SharedFiniteSemantics15.node_5 qValues
private noncomputable abbrev node_6 := SharedFiniteSemantics15.node_6 qValues
private noncomputable abbrev node_9 := SharedFiniteSemantics15.node_9 qValues
private noncomputable abbrev node_10 := SharedFiniteSemantics15.node_10 qValues
private noncomputable abbrev node_11 := SharedFiniteSemantics15.node_11 qValues
private noncomputable abbrev node_12 := SharedFiniteSemantics15.node_12 qValues
private noncomputable abbrev node_13 := SharedFiniteSemantics15.node_13 qValues
private noncomputable abbrev node_14 := SharedFiniteSemantics15.node_14 qValues
private noncomputable abbrev node_15 := SharedFiniteSemantics15.node_15 qValues
private noncomputable abbrev node_16 := SharedFiniteSemantics15.node_16 qValues
private noncomputable abbrev node_17 := SharedFiniteSemantics15.node_17 qValues
private noncomputable abbrev node_18 := SharedFiniteSemantics15.node_18 qValues
private noncomputable abbrev node_56 := SharedFiniteSemantics15.node_56 qValues
private noncomputable abbrev node_57 := SharedFiniteSemantics15.node_57 qValues
private noncomputable abbrev node_74 := SharedFiniteSemantics15.node_74 qValues
private noncomputable abbrev node_75 := SharedFiniteSemantics15.node_75 qValues
private noncomputable abbrev node_76 := SharedFiniteSemantics15.node_76 qValues
private noncomputable abbrev node_77 := SharedFiniteSemantics15.node_77 qValues
private noncomputable abbrev node_78 := SharedFiniteSemantics15.node_78 qValues
private noncomputable abbrev node_79 := SharedFiniteSemantics15.node_79 qValues
private noncomputable abbrev node_80 := SharedFiniteSemantics15.node_80 qValues
private noncomputable abbrev node_81 := SharedFiniteSemantics15.node_81 qValues
private noncomputable abbrev node_82 := SharedFiniteSemantics15.node_82 qValues
private noncomputable abbrev node_83 := SharedFiniteSemantics15.node_83 qValues
private noncomputable abbrev node_84 := SharedFiniteSemantics15.node_84 qValues
private noncomputable abbrev node_85 := SharedFiniteSemantics15.node_85 qValues
private noncomputable abbrev node_87 := SharedFiniteSemantics15.node_87 qValues
private noncomputable abbrev node_88 := SharedFiniteSemantics15.node_88 qValues
private noncomputable abbrev node_89 := SharedFiniteSemantics15.node_89 qValues
private noncomputable abbrev node_94 := SharedFiniteSemantics15.node_94 qValues
private noncomputable abbrev node_95 := SharedFiniteSemantics15.node_95 qValues
private noncomputable abbrev node_96 := SharedFiniteSemantics15.node_96 qValues
private noncomputable abbrev node_113 := SharedFiniteSemantics15.node_113 qValues
private noncomputable abbrev node_114 := SharedFiniteSemantics15.node_114 qValues
private noncomputable abbrev semantic_H_39 := SharedFiniteSemantics15.semantic_H_39 qValues
private noncomputable abbrev semantic_H_55 := SharedFiniteSemantics15.semantic_H_55 qValues
private noncomputable abbrev semantic_H_73 := SharedFiniteSemantics15.semantic_H_73 qValues
private noncomputable abbrev semantic_psi_112 := SharedFiniteSemantics15.semantic_psi_112 qValues
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
private theorem price_lambda_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceLambda 66 p = ((52725098717072542426821748833144481/66665788524178440801773277370327908 : ℝ)+(65986015427100985465340000000000000/49999341393133830601329958027745931 : ℝ)*p)/(sourceDenom*(p*(1-p))) := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell66,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
private theorem price_tau_normal (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    priceTau 66 p = (((6402383253918603178195662672358127311/2515757284353934450687789099231147513 : ℝ)+(-3389525048522526279265000000000000000/2515757284353934450687789099231147513 : ℝ)*p)-(145513/100000 : ℝ)*(1/1 : ℝ))/sourceDenom := by
  have hp0 : p ≠ 0 := ne_of_gt hp.1
  have heps : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
  norm_num [priceLambda,priceTau,sourceCell,sourceCells,cell66,Fin.sum_univ_succ,sourceDenom,muStar] <;>
    field_simp [hp0,heps] <;> ring
theorem scalar_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    (1)*eval e114 x = (x 0*(1-x 0))*(aPoint x+priceLambda 66 (x 0)*(HStar (yPoint x)-HStar (aPoint x)-HStar (capPoint x))+priceTau 66 (x 0)*psiStar (rPoint x)+(0)-(0)) := by
  have hp0 : x 0 ≠ 0 := ne_of_gt hp.1
  have hp1 : x 0 ≠ 1 := ne_of_lt hp.2
  have heps : 1-x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  rw [price_lambda_normal _ hp,price_tau_normal _ hp]
  simp only [node_1,node_13,node_56,node_57,node_74,node_75,node_76,node_77,node_78,node_79,node_80,node_81,node_82,node_83,node_84,node_85,node_87,node_88,node_89,node_94,node_95,node_96,node_113,node_114,semantic_H_39,semantic_H_55,semantic_H_73,semantic_psi_112,point_12,point_11,point_2,point_16,point_18]
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
  field_simp [hp0,heps] <;> ring
theorem actual_identity (hs : Contracts.Numerics_SourceCancellations.Statement)
    (x : Fin 4 → ℝ) (hp : x 0 ∈ Set.Ioo (0 : ℝ) 1) (ha : aPoint x ≤ bStar) (hA : capPoint x ≤ bStar)
    (hL : lambdaStar (x 0) = priceLambda 66 (x 0))
    (hT : tauStar (0 : Fin 9) (x 0) = priceTau 66 (x 0)) :
    (1)*eval e114 x = (x 0*(1-x 0))*(internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x)) := by
  simpa only [firstResidual,internalResidual,oldPotential,if_pos ha,if_pos hA,hL,hT,yPoint] using scalar_identity hs x hp
theorem cell_bound (hs : Contracts.Numerics_SourceCancellations.Statement)
    (hc : Contracts.Numerics_FiniteCoordinates.Statement)
    (hbound : ∀ x, inBox (crossingBox (15/32 : ℚ) (4791666666666667/10000000000000000 : ℚ)) x → eval e114 x ≤ 0)
    (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((15/32 : ℚ) : ℝ) < p ∧ p ≤ ((4791666666666667/10000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 66 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 66 p)
    (hk0 : ((4791666666666667/10000000000000000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((15/32 : ℚ) : ℝ))
    (hk1 : ((4791666666666667/10000000000000000 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((15/32 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r) :
    internalResidual (0 : Fin 9) a p A r ≤ 0 := by
  rcases hc with ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨_,x,hx,hxp,hxa,hxA,hxr⟩ := h3 (15/32 : ℚ) (4791666666666667/10000000000000000 : ℚ) ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ) p a A r hpcell hk0 hk1 hr ha hap hpA hAr
  have hcut : ((4791666666666667/10000000000000000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) := by norm_num [bStar]
  have hax : aPoint x = a := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxa
  have hAx : capPoint x = A := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxA
  have hrx : rPoint x = r := by simpa only [aPoint,rPoint,capPoint,if_pos hcut] using hxr
  have hpx : x 0 ∈ Ioo (0 : ℝ) 1 := by simpa only [hxp] using hp
  have hLx : lambdaStar (x 0) = priceLambda 66 (x 0) := by simpa only [hxp] using hL
  have hTx : tauStar (0 : Fin 9) (x 0) = priceTau 66 (x 0) := by simpa only [hxp] using hT
  have hrootb : ((2840189/5000000 : ℚ) : ℝ) ≤ bStar := by norm_num [bStar]
  have hAb : A ≤ bStar := hAr.trans (hr.2.trans hrootb)
  have hflag : aPoint x ≤ bStar := by rw [hax]; exact hap.trans (hpA.trans hAb)
  have hflagA : capPoint x ≤ bStar := by simpa only [hAx] using hAb
  have hb := hbound x hx
  have hv : (1 : ℝ)*eval e114 x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 1) hb
  rw [actual_identity hs x hpx hflag hflagA hLx hTx] at hv
  have hscale : 0 < x 0*(1-x 0) := mul_pos hpx.1 (sub_pos.mpr hpx.2)
  have hv : internalResidual (0 : Fin 9) (aPoint x) (x 0) (capPoint x) (rPoint x) ≤ 0 := le_of_not_gt (fun hpos => (not_lt_of_ge hv) (mul_pos hscale hpos))
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
.add 9 13,
.add 14 10,
.const (1085/4818 : ℚ),
.mul 16 15,
.mul 15 15,
.const (19/146 : ℚ),
.mul 19 18,
.mul 15 18,
.const (35/438 : ℚ),
.mul 22 21,
.add 20 23,
.mul 18 18,
.mul 25 25,
.mul 26 26,
.mul 27 27,
.mul 15 28,
.const (1/66 : ℚ),
.mul 30 29,
.add 24 31,
.neg 32,
.add 17 33,
.const (4818/3733 : ℚ),
.mul 35 34,
.mul 16 9,
.mul 9 9,
.mul 19 38,
.mul 9 38,
.mul 22 40,
.add 39 41,
.mul 38 38,
.mul 43 43,
.mul 44 44,
.mul 45 45,
.mul 9 46,
.mul 30 47,
.add 42 48,
.neg 49,
.add 37 50,
.mul 35 51,
.neg 52,
.add 36 53,
.mul 16 13,
.mul 13 13,
.mul 19 56,
.mul 13 56,
.mul 22 58,
.add 57 59,
.mul 56 56,
.mul 61 61,
.mul 62 62,
.mul 63 63,
.mul 13 64,
.mul 30 65,
.add 60 66,
.neg 67,
.add 55 68,
.mul 35 69,
.neg 70,
.add 54 71,
.const (52725098717072542426821748833144481/66665788524178440801773277370327908 : ℚ),
.const (65986015427100985465340000000000000/49999341393133830601329958027745931 : ℚ),
.mul 74 1,
.add 73 75,
.const (6402383253918603178195662672358127311/2515757284353934450687789099231147513 : ℚ),
.const (-3389525048522526279265000000000000000/2515757284353934450687789099231147513 : ℚ),
.mul 78 1,
.add 77 79,
.add 0 10,
.mul 1 81,
.const (-145513/100000 : ℚ),
.add 80 83,
.mul 84 82,
.mul 9 82,
.mul 76 72,
.add 86 87,
.const (19/73 : ℚ),
.mul 89 8,
.mul 8 8,
.const (35/146 : ℚ),
.mul 92 91,
.add 90 93,
.mul 91 91,
.mul 95 95,
.mul 96 96,
.mul 97 97,
.const (1/2 : ℚ),
.mul 99 98,
.add 94 100,
.neg 101,
.add 16 102,
.mul 35 103,
.mul 85 104,
.add 88 105]
private noncomputable def ssaQVals : Fin 16 → ℚ := ![(1/1 : ℚ),(49/100 : ℚ),(390189/5000000 : ℚ),(1085/4818 : ℚ),(19/146 : ℚ),(35/438 : ℚ),(1/66 : ℚ),(4818/3733 : ℚ),(52725098717072542426821748833144481/66665788524178440801773277370327908 : ℚ),(65986015427100985465340000000000000/49999341393133830601329958027745931 : ℚ),(6402383253918603178195662672358127311/2515757284353934450687789099231147513 : ℚ),(-3389525048522526279265000000000000000/2515757284353934450687789099231147513 : ℚ),(-145513/100000 : ℚ),(19/73 : ℚ),(35/146 : ℚ),(1/2 : ℚ)]
private theorem ssa_tape : MetricDistortion.OptimizedSSAFinite0.S_6546fc2a060ad643.p107 ssaQVals = tape := by rfl
private noncomputable def computed (D : Int) (B : Fin 4 → FixedTape.I) : FixedTape.Row :=
  MetricDistortion.OptimizedSSAFinite0.S_6546fc2a060ad643.computed ssaQVals D B
private theorem ssa_matches (D : Int) (B : Fin 4 → FixedTape.I) :
    (FixedTape.rowsAux D B [] tape).getD 106 FixedTape.zeroRow = computed D B := by
  rw [←ssa_tape]
  exact MetricDistortion.OptimizedSSAFinite0.S_6546fc2a060ad643.ssa_matches ssaQVals D B

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
private noncomputable def denominator : Int := 5214284040863921558409134942806913650398244527968459163130928399181981561685847207830565683200000000000000000000000
private theorem denominator_positive : 0 < denominator := by decide +kernel
private noncomputable def candidateRows (B : Fin 4 → FixedTape.I) : List TapeBounds :=
  (FixedTape.rowsAux denominator B [] tape).map (FixedTape.decodeRow denominator)
private theorem root_in_range : 106 < tape.length := by decide +kernel
private theorem references_valid : tapeRefsValidAux 0 tape = true := by decide +kernel
private theorem candidate_valid (h : Needs) (B : Fin 4 → FixedTape.I) :
    tapeCheck (FixedTape.decodeBox denominator B) tape (candidateRows B) = true :=
  h.child_10.1 denominator denominator_positive B tape references_valid
private theorem candidate_root (B : Fin 4 → FixedTape.I) :
    (candidateRows B).getD 106 zeroTapeBounds = FixedTape.decodeRow denominator (computed denominator B) := by
  unfold candidateRows
  rw [←decode_zeroRow denominator,List.getD_map,ssa_matches]
private noncomputable def ibox0 : Fin 4 → FixedTape.I := ![⟨2444195644154963230504282004440740773624177122485215232717622687116553857040240878670577664000000000000000000000000,2498511102913962587213845188892364737786990263215341695608387456890004936005415093151531446061573594352189440000000⟩,⟨0,5214284040863921558409134942806913650398244527968459163130928399181981561685847207830565683200000000000000000000000⟩,⟨0,5214284040863921558409134942806913650398244527968459163130928399181981561685847207830565683200000000000000000000000⟩,⟨0,5214284040863921558409134942806913650398244527968459163130928399181981561685847207830565683200000000000000000000000⟩]
private noncomputable def ibox1 : Fin 4 → FixedTape.I := splitI ibox0 1 2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 false
private noncomputable def ibox2 : Fin 4 → FixedTape.I := faceI ibox1 1 true
private noncomputable def ibox3 : Fin 4 → FixedTape.I := splitI ibox2 2 2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 false
private noncomputable def ibox4 : Fin 4 → FixedTape.I := splitI ibox2 2 2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 true
private noncomputable def ibox5 : Fin 4 → FixedTape.I := splitI ibox0 1 2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 true
private noncomputable def ibox6 : Fin 4 → FixedTape.I := splitI ibox5 1 3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 false
private noncomputable def ibox7 : Fin 4 → FixedTape.I := faceI ibox6 1 true
private noncomputable def ibox8 : Fin 4 → FixedTape.I := splitI ibox7 2 2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 false
private noncomputable def ibox9 : Fin 4 → FixedTape.I := splitI ibox8 2 1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 false
private noncomputable def ibox10 : Fin 4 → FixedTape.I := splitI ibox8 2 1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 true
private noncomputable def ibox11 : Fin 4 → FixedTape.I := splitI ibox7 2 2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 true
private noncomputable def ibox12 : Fin 4 → FixedTape.I := splitI ibox11 2 3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 false
private noncomputable def ibox13 : Fin 4 → FixedTape.I := splitI ibox11 2 3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 true
private noncomputable def ibox14 : Fin 4 → FixedTape.I := splitI ibox5 1 3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 true
private noncomputable def ibox15 : Fin 4 → FixedTape.I := faceI ibox14 1 true
private noncomputable def ibox16 : Fin 4 → FixedTape.I := splitI ibox15 2 2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 false
private noncomputable def ibox17 : Fin 4 → FixedTape.I := splitI ibox16 3 2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 false
private noncomputable def ibox18 : Fin 4 → FixedTape.I := splitI ibox17 2 1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 false
private noncomputable def ibox19 : Fin 4 → FixedTape.I := splitI ibox18 3 1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 false
private noncomputable def ibox20 : Fin 4 → FixedTape.I := splitI ibox19 2 651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 false
private noncomputable def ibox21 : Fin 4 → FixedTape.I := splitI ibox20 3 651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 false
private noncomputable def ibox22 : Fin 4 → FixedTape.I := splitI ibox21 0 2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 false
private noncomputable def ibox23 : Fin 4 → FixedTape.I := splitI ibox21 0 2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 true
private noncomputable def ibox24 : Fin 4 → FixedTape.I := splitI ibox20 3 651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 true
private noncomputable def ibox25 : Fin 4 → FixedTape.I := splitI ibox19 2 651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 true
private noncomputable def ibox26 : Fin 4 → FixedTape.I := splitI ibox25 3 651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 false
private noncomputable def ibox27 : Fin 4 → FixedTape.I := splitI ibox26 0 2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 false
private noncomputable def ibox28 : Fin 4 → FixedTape.I := splitI ibox26 0 2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 true
private noncomputable def ibox29 : Fin 4 → FixedTape.I := splitI ibox25 3 651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 true
private noncomputable def ibox30 : Fin 4 → FixedTape.I := splitI ibox18 3 1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 true
private noncomputable def ibox31 : Fin 4 → FixedTape.I := splitI ibox30 2 651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 false
private noncomputable def ibox32 : Fin 4 → FixedTape.I := splitI ibox31 3 1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 false
private noncomputable def ibox33 : Fin 4 → FixedTape.I := splitI ibox31 3 1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 true
private noncomputable def ibox34 : Fin 4 → FixedTape.I := splitI ibox30 2 651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 true
private noncomputable def ibox35 : Fin 4 → FixedTape.I := splitI ibox34 3 1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 false
private noncomputable def ibox36 : Fin 4 → FixedTape.I := splitI ibox34 3 1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 true
private noncomputable def ibox37 : Fin 4 → FixedTape.I := splitI ibox17 2 1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 true
private noncomputable def ibox38 : Fin 4 → FixedTape.I := splitI ibox37 3 1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 false
private noncomputable def ibox39 : Fin 4 → FixedTape.I := splitI ibox38 2 1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 false
private noncomputable def ibox40 : Fin 4 → FixedTape.I := splitI ibox39 3 651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 false
private noncomputable def ibox41 : Fin 4 → FixedTape.I := splitI ibox40 0 2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 false
private noncomputable def ibox42 : Fin 4 → FixedTape.I := splitI ibox40 0 2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 true
private noncomputable def ibox43 : Fin 4 → FixedTape.I := splitI ibox39 3 651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 true
private noncomputable def ibox44 : Fin 4 → FixedTape.I := splitI ibox38 2 1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 true
private noncomputable def ibox45 : Fin 4 → FixedTape.I := splitI ibox44 3 651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 false
private noncomputable def ibox46 : Fin 4 → FixedTape.I := splitI ibox45 0 2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 false
private noncomputable def ibox47 : Fin 4 → FixedTape.I := splitI ibox45 0 2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 true
private noncomputable def ibox48 : Fin 4 → FixedTape.I := splitI ibox44 3 651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 true
private noncomputable def ibox49 : Fin 4 → FixedTape.I := splitI ibox37 3 1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 true
private noncomputable def ibox50 : Fin 4 → FixedTape.I := splitI ibox49 2 1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 false
private noncomputable def ibox51 : Fin 4 → FixedTape.I := splitI ibox50 3 1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 false
private noncomputable def ibox52 : Fin 4 → FixedTape.I := splitI ibox50 3 1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 true
private noncomputable def ibox53 : Fin 4 → FixedTape.I := splitI ibox49 2 1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 true
private noncomputable def ibox54 : Fin 4 → FixedTape.I := splitI ibox53 3 1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 false
private noncomputable def ibox55 : Fin 4 → FixedTape.I := splitI ibox53 3 1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 true
private noncomputable def ibox56 : Fin 4 → FixedTape.I := splitI ibox16 3 2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 true
private noncomputable def ibox57 : Fin 4 → FixedTape.I := splitI ibox56 2 1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 false
private noncomputable def ibox58 : Fin 4 → FixedTape.I := splitI ibox57 3 3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 false
private noncomputable def ibox59 : Fin 4 → FixedTape.I := splitI ibox58 2 651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 false
private noncomputable def ibox60 : Fin 4 → FixedTape.I := splitI ibox58 2 651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 true
private noncomputable def ibox61 : Fin 4 → FixedTape.I := splitI ibox57 3 3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 true
private noncomputable def ibox62 : Fin 4 → FixedTape.I := splitI ibox61 2 651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 false
private noncomputable def ibox63 : Fin 4 → FixedTape.I := splitI ibox61 2 651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 true
private noncomputable def ibox64 : Fin 4 → FixedTape.I := splitI ibox56 2 1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 true
private noncomputable def ibox65 : Fin 4 → FixedTape.I := splitI ibox64 3 3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 false
private noncomputable def ibox66 : Fin 4 → FixedTape.I := splitI ibox65 2 1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 false
private noncomputable def ibox67 : Fin 4 → FixedTape.I := splitI ibox65 2 1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 true
private noncomputable def ibox68 : Fin 4 → FixedTape.I := splitI ibox64 3 3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 true
private noncomputable def ibox69 : Fin 4 → FixedTape.I := splitI ibox68 2 1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 false
private noncomputable def ibox70 : Fin 4 → FixedTape.I := splitI ibox68 2 1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 true
private noncomputable def ibox71 : Fin 4 → FixedTape.I := splitI ibox15 2 2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 true
private noncomputable def ibox72 : Fin 4 → FixedTape.I := splitI ibox71 3 2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 false
private noncomputable def ibox73 : Fin 4 → FixedTape.I := splitI ibox72 2 3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 false
private noncomputable def ibox74 : Fin 4 → FixedTape.I := splitI ibox73 3 1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 false
private noncomputable def ibox75 : Fin 4 → FixedTape.I := splitI ibox74 2 3258927525539950974005709339254321031498902829980286976956830249488738476053654504894103552000000000000000000000000 false
private noncomputable def ibox76 : Fin 4 → FixedTape.I := splitI ibox75 3 651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 false
private noncomputable def ibox77 : Fin 4 → FixedTape.I := splitI ibox76 0 2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 false
private noncomputable def ibox78 : Fin 4 → FixedTape.I := splitI ibox76 0 2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 true
private noncomputable def ibox79 : Fin 4 → FixedTape.I := splitI ibox75 3 651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 true
private noncomputable def ibox80 : Fin 4 → FixedTape.I := splitI ibox74 2 3258927525539950974005709339254321031498902829980286976956830249488738476053654504894103552000000000000000000000000 true
private noncomputable def ibox81 : Fin 4 → FixedTape.I := splitI ibox80 3 651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 false
private noncomputable def ibox82 : Fin 4 → FixedTape.I := splitI ibox81 0 2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 false
private noncomputable def ibox83 : Fin 4 → FixedTape.I := splitI ibox81 0 2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 true
private noncomputable def ibox84 : Fin 4 → FixedTape.I := splitI ibox80 3 651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 true
private noncomputable def ibox85 : Fin 4 → FixedTape.I := splitI ibox73 3 1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 true
private noncomputable def ibox86 : Fin 4 → FixedTape.I := splitI ibox85 2 3258927525539950974005709339254321031498902829980286976956830249488738476053654504894103552000000000000000000000000 false
private noncomputable def ibox87 : Fin 4 → FixedTape.I := splitI ibox86 3 1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 false
private noncomputable def ibox88 : Fin 4 → FixedTape.I := splitI ibox86 3 1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 true
private noncomputable def ibox89 : Fin 4 → FixedTape.I := splitI ibox85 2 3258927525539950974005709339254321031498902829980286976956830249488738476053654504894103552000000000000000000000000 true
private noncomputable def ibox90 : Fin 4 → FixedTape.I := splitI ibox89 3 1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 false
private noncomputable def ibox91 : Fin 4 → FixedTape.I := splitI ibox89 3 1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 true
private noncomputable def ibox92 : Fin 4 → FixedTape.I := splitI ibox72 2 3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 true
private noncomputable def ibox93 : Fin 4 → FixedTape.I := splitI ibox92 3 1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 false
private noncomputable def ibox94 : Fin 4 → FixedTape.I := splitI ibox93 3 651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 false
private noncomputable def ibox95 : Fin 4 → FixedTape.I := splitI ibox94 2 4562498535755931363607993074956049444098463961972401767739562349284233866475116306851744972800000000000000000000000 false
private noncomputable def ibox96 : Fin 4 → FixedTape.I := splitI ibox95 0 2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 false
private noncomputable def ibox97 : Fin 4 → FixedTape.I := splitI ibox95 0 2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 true
private noncomputable def ibox98 : Fin 4 → FixedTape.I := splitI ibox94 2 4562498535755931363607993074956049444098463961972401767739562349284233866475116306851744972800000000000000000000000 true
private noncomputable def ibox99 : Fin 4 → FixedTape.I := splitI ibox98 0 2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 false
private noncomputable def ibox100 : Fin 4 → FixedTape.I := splitI ibox98 0 2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 true
private noncomputable def ibox101 : Fin 4 → FixedTape.I := splitI ibox93 3 651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 true
private noncomputable def ibox102 : Fin 4 → FixedTape.I := splitI ibox101 2 4562498535755931363607993074956049444098463961972401767739562349284233866475116306851744972800000000000000000000000 false
private noncomputable def ibox103 : Fin 4 → FixedTape.I := splitI ibox101 2 4562498535755931363607993074956049444098463961972401767739562349284233866475116306851744972800000000000000000000000 true
private noncomputable def ibox104 : Fin 4 → FixedTape.I := splitI ibox92 3 1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 true
private noncomputable def ibox105 : Fin 4 → FixedTape.I := splitI ibox104 2 4562498535755931363607993074956049444098463961972401767739562349284233866475116306851744972800000000000000000000000 false
private noncomputable def ibox106 : Fin 4 → FixedTape.I := splitI ibox105 3 1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 false
private noncomputable def ibox107 : Fin 4 → FixedTape.I := splitI ibox105 3 1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 true
private noncomputable def ibox108 : Fin 4 → FixedTape.I := splitI ibox104 2 4562498535755931363607993074956049444098463961972401767739562349284233866475116306851744972800000000000000000000000 true
private noncomputable def ibox109 : Fin 4 → FixedTape.I := splitI ibox108 3 1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 false
private noncomputable def ibox110 : Fin 4 → FixedTape.I := splitI ibox108 3 1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 true
private noncomputable def ibox111 : Fin 4 → FixedTape.I := splitI ibox71 3 2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 true
private noncomputable def ibox112 : Fin 4 → FixedTape.I := splitI ibox111 2 3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 false
private noncomputable def ibox113 : Fin 4 → FixedTape.I := splitI ibox112 3 3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 false
private noncomputable def ibox114 : Fin 4 → FixedTape.I := splitI ibox113 2 3258927525539950974005709339254321031498902829980286976956830249488738476053654504894103552000000000000000000000000 false
private noncomputable def ibox115 : Fin 4 → FixedTape.I := splitI ibox113 2 3258927525539950974005709339254321031498902829980286976956830249488738476053654504894103552000000000000000000000000 true
private noncomputable def ibox116 : Fin 4 → FixedTape.I := splitI ibox112 3 3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 true
private noncomputable def ibox117 : Fin 4 → FixedTape.I := splitI ibox116 2 3258927525539950974005709339254321031498902829980286976956830249488738476053654504894103552000000000000000000000000 false
private noncomputable def ibox118 : Fin 4 → FixedTape.I := splitI ibox116 2 3258927525539950974005709339254321031498902829980286976956830249488738476053654504894103552000000000000000000000000 true
private noncomputable def ibox119 : Fin 4 → FixedTape.I := splitI ibox111 2 3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 true
private noncomputable def ibox120 : Fin 4 → FixedTape.I := splitI ibox119 3 3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 false
private noncomputable def ibox121 : Fin 4 → FixedTape.I := splitI ibox120 2 4562498535755931363607993074956049444098463961972401767739562349284233866475116306851744972800000000000000000000000 false
private noncomputable def ibox122 : Fin 4 → FixedTape.I := splitI ibox120 2 4562498535755931363607993074956049444098463961972401767739562349284233866475116306851744972800000000000000000000000 true
private noncomputable def ibox123 : Fin 4 → FixedTape.I := splitI ibox119 3 3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 true
private noncomputable def ibox124 : Fin 4 → FixedTape.I := splitI ibox123 2 4562498535755931363607993074956049444098463961972401767739562349284233866475116306851744972800000000000000000000000 false
private noncomputable def ibox125 : Fin 4 → FixedTape.I := splitI ibox123 2 4562498535755931363607993074956049444098463961972401767739562349284233866475116306851744972800000000000000000000000 true
private noncomputable def tree125 : TapeTree := .centered (candidateRows ibox125) (candidateRows (FixedTape.midBox ibox125))
attribute [irreducible] tree125
private theorem sign_125 : 2*denominator*(computed denominator (FixedTape.midBox ibox125)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox125).gradient k).lo.natAbs ((computed denominator ibox125).gradient k).hi.natAbs : Int)*((ibox125 k).hi-(ibox125 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox125
    (computed denominator ibox125) (computed denominator (FixedTape.midBox ibox125))
    (by decide +kernel)
private theorem midpoint_even_125 : ∀ k, 2 ∣ (ibox125 k).lo+(ibox125 k).hi := by decide +kernel
private theorem accepted_125 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox125) tree125 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox125 midpoint_even_125
  simp only [tree125,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox125,candidate_valid h (FixedTape.midBox ibox125),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox125 106 (FixedTape.rowsAux denominator ibox125 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox125) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_125
private noncomputable def tree124 : TapeTree := .centered (candidateRows ibox124) (candidateRows (FixedTape.midBox ibox124))
attribute [irreducible] tree124
private theorem sign_124 : 2*denominator*(computed denominator (FixedTape.midBox ibox124)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox124).gradient k).lo.natAbs ((computed denominator ibox124).gradient k).hi.natAbs : Int)*((ibox124 k).hi-(ibox124 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox124
    (computed denominator ibox124) (computed denominator (FixedTape.midBox ibox124))
    (by decide +kernel)
private theorem midpoint_even_124 : ∀ k, 2 ∣ (ibox124 k).lo+(ibox124 k).hi := by decide +kernel
private theorem accepted_124 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox124) tree124 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox124 midpoint_even_124
  simp only [tree124,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox124,candidate_valid h (FixedTape.midBox ibox124),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox124 106 (FixedTape.rowsAux denominator ibox124 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox124) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_124
private noncomputable def tree123 : TapeTree := .split 2 (((4562498535755931363607993074956049444098463961972401767739562349284233866475116306851744972800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree124 tree125
attribute [irreducible] tree123
private theorem accepted_123 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox123) tree123 = true := by
  simp only [tree123,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox123 2 (4562498535755931363607993074956049444098463961972401767739562349284233866475116306851744972800000000000000000000000 : Int) false,decode_split denominator ibox123 2 (4562498535755931363607993074956049444098463961972401767739562349284233866475116306851744972800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_124 h,accepted_125 h⟩
private noncomputable def tree122 : TapeTree := .centered (candidateRows ibox122) (candidateRows (FixedTape.midBox ibox122))
attribute [irreducible] tree122
private theorem sign_122 : 2*denominator*(computed denominator (FixedTape.midBox ibox122)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox122).gradient k).lo.natAbs ((computed denominator ibox122).gradient k).hi.natAbs : Int)*((ibox122 k).hi-(ibox122 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox122
    (computed denominator ibox122) (computed denominator (FixedTape.midBox ibox122))
    (by decide +kernel)
private theorem midpoint_even_122 : ∀ k, 2 ∣ (ibox122 k).lo+(ibox122 k).hi := by decide +kernel
private theorem accepted_122 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox122) tree122 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox122 midpoint_even_122
  simp only [tree122,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox122,candidate_valid h (FixedTape.midBox ibox122),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox122 106 (FixedTape.rowsAux denominator ibox122 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox122) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_122
private noncomputable def tree121 : TapeTree := .centered (candidateRows ibox121) (candidateRows (FixedTape.midBox ibox121))
attribute [irreducible] tree121
private theorem sign_121 : 2*denominator*(computed denominator (FixedTape.midBox ibox121)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox121).gradient k).lo.natAbs ((computed denominator ibox121).gradient k).hi.natAbs : Int)*((ibox121 k).hi-(ibox121 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox121
    (computed denominator ibox121) (computed denominator (FixedTape.midBox ibox121))
    (by decide +kernel)
private theorem midpoint_even_121 : ∀ k, 2 ∣ (ibox121 k).lo+(ibox121 k).hi := by decide +kernel
private theorem accepted_121 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox121) tree121 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox121 midpoint_even_121
  simp only [tree121,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox121,candidate_valid h (FixedTape.midBox ibox121),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox121 106 (FixedTape.rowsAux denominator ibox121 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox121) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_121
private noncomputable def tree120 : TapeTree := .split 2 (((4562498535755931363607993074956049444098463961972401767739562349284233866475116306851744972800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree121 tree122
attribute [irreducible] tree120
private theorem accepted_120 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox120) tree120 = true := by
  simp only [tree120,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox120 2 (4562498535755931363607993074956049444098463961972401767739562349284233866475116306851744972800000000000000000000000 : Int) false,decode_split denominator ibox120 2 (4562498535755931363607993074956049444098463961972401767739562349284233866475116306851744972800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_121 h,accepted_122 h⟩
private noncomputable def tree119 : TapeTree := .split 3 (((3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree120 tree123
attribute [irreducible] tree119
private theorem accepted_119 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox119) tree119 = true := by
  simp only [tree119,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox119 3 (3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 : Int) false,decode_split denominator ibox119 3 (3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_120 h,accepted_123 h⟩
private noncomputable def tree118 : TapeTree := .centered (candidateRows ibox118) (candidateRows (FixedTape.midBox ibox118))
attribute [irreducible] tree118
private theorem sign_118 : 2*denominator*(computed denominator (FixedTape.midBox ibox118)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox118).gradient k).lo.natAbs ((computed denominator ibox118).gradient k).hi.natAbs : Int)*((ibox118 k).hi-(ibox118 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox118
    (computed denominator ibox118) (computed denominator (FixedTape.midBox ibox118))
    (by decide +kernel)
private theorem midpoint_even_118 : ∀ k, 2 ∣ (ibox118 k).lo+(ibox118 k).hi := by decide +kernel
private theorem accepted_118 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox118) tree118 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox118 midpoint_even_118
  simp only [tree118,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox118,candidate_valid h (FixedTape.midBox ibox118),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox118 106 (FixedTape.rowsAux denominator ibox118 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox118) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_118
private noncomputable def tree117 : TapeTree := .centered (candidateRows ibox117) (candidateRows (FixedTape.midBox ibox117))
attribute [irreducible] tree117
private theorem sign_117 : 2*denominator*(computed denominator (FixedTape.midBox ibox117)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox117).gradient k).lo.natAbs ((computed denominator ibox117).gradient k).hi.natAbs : Int)*((ibox117 k).hi-(ibox117 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox117
    (computed denominator ibox117) (computed denominator (FixedTape.midBox ibox117))
    (by decide +kernel)
private theorem midpoint_even_117 : ∀ k, 2 ∣ (ibox117 k).lo+(ibox117 k).hi := by decide +kernel
private theorem accepted_117 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox117) tree117 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox117 midpoint_even_117
  simp only [tree117,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox117,candidate_valid h (FixedTape.midBox ibox117),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox117 106 (FixedTape.rowsAux denominator ibox117 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox117) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_117
private noncomputable def tree116 : TapeTree := .split 2 (((3258927525539950974005709339254321031498902829980286976956830249488738476053654504894103552000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree117 tree118
attribute [irreducible] tree116
private theorem accepted_116 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox116) tree116 = true := by
  simp only [tree116,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox116 2 (3258927525539950974005709339254321031498902829980286976956830249488738476053654504894103552000000000000000000000000 : Int) false,decode_split denominator ibox116 2 (3258927525539950974005709339254321031498902829980286976956830249488738476053654504894103552000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_117 h,accepted_118 h⟩
private noncomputable def tree115 : TapeTree := .centered (candidateRows ibox115) (candidateRows (FixedTape.midBox ibox115))
attribute [irreducible] tree115
private theorem sign_115 : 2*denominator*(computed denominator (FixedTape.midBox ibox115)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox115).gradient k).lo.natAbs ((computed denominator ibox115).gradient k).hi.natAbs : Int)*((ibox115 k).hi-(ibox115 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox115
    (computed denominator ibox115) (computed denominator (FixedTape.midBox ibox115))
    (by decide +kernel)
private theorem midpoint_even_115 : ∀ k, 2 ∣ (ibox115 k).lo+(ibox115 k).hi := by decide +kernel
private theorem accepted_115 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox115) tree115 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox115 midpoint_even_115
  simp only [tree115,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox115,candidate_valid h (FixedTape.midBox ibox115),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox115 106 (FixedTape.rowsAux denominator ibox115 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox115) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_115
private noncomputable def tree114 : TapeTree := .centered (candidateRows ibox114) (candidateRows (FixedTape.midBox ibox114))
attribute [irreducible] tree114
private theorem sign_114 : 2*denominator*(computed denominator (FixedTape.midBox ibox114)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox114).gradient k).lo.natAbs ((computed denominator ibox114).gradient k).hi.natAbs : Int)*((ibox114 k).hi-(ibox114 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox114
    (computed denominator ibox114) (computed denominator (FixedTape.midBox ibox114))
    (by decide +kernel)
private theorem midpoint_even_114 : ∀ k, 2 ∣ (ibox114 k).lo+(ibox114 k).hi := by decide +kernel
private theorem accepted_114 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox114) tree114 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox114 midpoint_even_114
  simp only [tree114,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox114,candidate_valid h (FixedTape.midBox ibox114),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox114 106 (FixedTape.rowsAux denominator ibox114 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox114) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_114
private noncomputable def tree113 : TapeTree := .split 2 (((3258927525539950974005709339254321031498902829980286976956830249488738476053654504894103552000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree114 tree115
attribute [irreducible] tree113
private theorem accepted_113 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox113) tree113 = true := by
  simp only [tree113,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox113 2 (3258927525539950974005709339254321031498902829980286976956830249488738476053654504894103552000000000000000000000000 : Int) false,decode_split denominator ibox113 2 (3258927525539950974005709339254321031498902829980286976956830249488738476053654504894103552000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_114 h,accepted_115 h⟩
private noncomputable def tree112 : TapeTree := .split 3 (((3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree113 tree116
attribute [irreducible] tree112
private theorem accepted_112 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox112) tree112 = true := by
  simp only [tree112,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox112 3 (3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 : Int) false,decode_split denominator ibox112 3 (3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_113 h,accepted_116 h⟩
private noncomputable def tree111 : TapeTree := .split 2 (((3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree112 tree119
attribute [irreducible] tree111
private theorem accepted_111 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox111) tree111 = true := by
  simp only [tree111,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox111 2 (3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 : Int) false,decode_split denominator ibox111 2 (3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_112 h,accepted_119 h⟩
private noncomputable def tree110 : TapeTree := .centered (candidateRows ibox110) (candidateRows (FixedTape.midBox ibox110))
attribute [irreducible] tree110
private theorem sign_110 : 2*denominator*(computed denominator (FixedTape.midBox ibox110)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox110).gradient k).lo.natAbs ((computed denominator ibox110).gradient k).hi.natAbs : Int)*((ibox110 k).hi-(ibox110 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox110
    (computed denominator ibox110) (computed denominator (FixedTape.midBox ibox110))
    (by decide +kernel)
private theorem midpoint_even_110 : ∀ k, 2 ∣ (ibox110 k).lo+(ibox110 k).hi := by decide +kernel
private theorem accepted_110 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox110) tree110 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox110 midpoint_even_110
  simp only [tree110,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox110,candidate_valid h (FixedTape.midBox ibox110),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox110 106 (FixedTape.rowsAux denominator ibox110 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox110) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_110
private noncomputable def tree109 : TapeTree := .centered (candidateRows ibox109) (candidateRows (FixedTape.midBox ibox109))
attribute [irreducible] tree109
private theorem sign_109 : 2*denominator*(computed denominator (FixedTape.midBox ibox109)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox109).gradient k).lo.natAbs ((computed denominator ibox109).gradient k).hi.natAbs : Int)*((ibox109 k).hi-(ibox109 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox109
    (computed denominator ibox109) (computed denominator (FixedTape.midBox ibox109))
    (by decide +kernel)
private theorem midpoint_even_109 : ∀ k, 2 ∣ (ibox109 k).lo+(ibox109 k).hi := by decide +kernel
private theorem accepted_109 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox109) tree109 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox109 midpoint_even_109
  simp only [tree109,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox109,candidate_valid h (FixedTape.midBox ibox109),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox109 106 (FixedTape.rowsAux denominator ibox109 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox109) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_109
private noncomputable def tree108 : TapeTree := .split 3 (((1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree109 tree110
attribute [irreducible] tree108
private theorem accepted_108 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox108) tree108 = true := by
  simp only [tree108,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox108 3 (1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) false,decode_split denominator ibox108 3 (1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_109 h,accepted_110 h⟩
private noncomputable def tree107 : TapeTree := .centered (candidateRows ibox107) (candidateRows (FixedTape.midBox ibox107))
attribute [irreducible] tree107
private theorem sign_107 : 2*denominator*(computed denominator (FixedTape.midBox ibox107)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox107).gradient k).lo.natAbs ((computed denominator ibox107).gradient k).hi.natAbs : Int)*((ibox107 k).hi-(ibox107 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox107
    (computed denominator ibox107) (computed denominator (FixedTape.midBox ibox107))
    (by decide +kernel)
private theorem midpoint_even_107 : ∀ k, 2 ∣ (ibox107 k).lo+(ibox107 k).hi := by decide +kernel
private theorem accepted_107 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox107) tree107 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox107 midpoint_even_107
  simp only [tree107,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox107,candidate_valid h (FixedTape.midBox ibox107),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox107 106 (FixedTape.rowsAux denominator ibox107 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox107) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_107
private noncomputable def tree106 : TapeTree := .centered (candidateRows ibox106) (candidateRows (FixedTape.midBox ibox106))
attribute [irreducible] tree106
private theorem sign_106 : 2*denominator*(computed denominator (FixedTape.midBox ibox106)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox106).gradient k).lo.natAbs ((computed denominator ibox106).gradient k).hi.natAbs : Int)*((ibox106 k).hi-(ibox106 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox106
    (computed denominator ibox106) (computed denominator (FixedTape.midBox ibox106))
    (by decide +kernel)
private theorem midpoint_even_106 : ∀ k, 2 ∣ (ibox106 k).lo+(ibox106 k).hi := by decide +kernel
private theorem accepted_106 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox106) tree106 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox106 midpoint_even_106
  simp only [tree106,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox106,candidate_valid h (FixedTape.midBox ibox106),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox106 106 (FixedTape.rowsAux denominator ibox106 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox106) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_106
private noncomputable def tree105 : TapeTree := .split 3 (((1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree106 tree107
attribute [irreducible] tree105
private theorem accepted_105 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox105) tree105 = true := by
  simp only [tree105,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox105 3 (1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) false,decode_split denominator ibox105 3 (1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_106 h,accepted_107 h⟩
private noncomputable def tree104 : TapeTree := .split 2 (((4562498535755931363607993074956049444098463961972401767739562349284233866475116306851744972800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree105 tree108
attribute [irreducible] tree104
private theorem accepted_104 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox104) tree104 = true := by
  simp only [tree104,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox104 2 (4562498535755931363607993074956049444098463961972401767739562349284233866475116306851744972800000000000000000000000 : Int) false,decode_split denominator ibox104 2 (4562498535755931363607993074956049444098463961972401767739562349284233866475116306851744972800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_105 h,accepted_108 h⟩
private noncomputable def tree103 : TapeTree := .centered (candidateRows ibox103) (candidateRows (FixedTape.midBox ibox103))
attribute [irreducible] tree103
private theorem sign_103 : 2*denominator*(computed denominator (FixedTape.midBox ibox103)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox103).gradient k).lo.natAbs ((computed denominator ibox103).gradient k).hi.natAbs : Int)*((ibox103 k).hi-(ibox103 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox103
    (computed denominator ibox103) (computed denominator (FixedTape.midBox ibox103))
    (by decide +kernel)
private theorem midpoint_even_103 : ∀ k, 2 ∣ (ibox103 k).lo+(ibox103 k).hi := by decide +kernel
private theorem accepted_103 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox103) tree103 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox103 midpoint_even_103
  simp only [tree103,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox103,candidate_valid h (FixedTape.midBox ibox103),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox103 106 (FixedTape.rowsAux denominator ibox103 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox103) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_103
private noncomputable def tree102 : TapeTree := .centered (candidateRows ibox102) (candidateRows (FixedTape.midBox ibox102))
attribute [irreducible] tree102
private theorem sign_102 : 2*denominator*(computed denominator (FixedTape.midBox ibox102)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox102).gradient k).lo.natAbs ((computed denominator ibox102).gradient k).hi.natAbs : Int)*((ibox102 k).hi-(ibox102 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox102
    (computed denominator ibox102) (computed denominator (FixedTape.midBox ibox102))
    (by decide +kernel)
private theorem midpoint_even_102 : ∀ k, 2 ∣ (ibox102 k).lo+(ibox102 k).hi := by decide +kernel
private theorem accepted_102 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox102) tree102 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox102 midpoint_even_102
  simp only [tree102,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox102,candidate_valid h (FixedTape.midBox ibox102),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox102 106 (FixedTape.rowsAux denominator ibox102 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox102) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_102
private noncomputable def tree101 : TapeTree := .split 2 (((4562498535755931363607993074956049444098463961972401767739562349284233866475116306851744972800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree102 tree103
attribute [irreducible] tree101
private theorem accepted_101 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox101) tree101 = true := by
  simp only [tree101,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox101 2 (4562498535755931363607993074956049444098463961972401767739562349284233866475116306851744972800000000000000000000000 : Int) false,decode_split denominator ibox101 2 (4562498535755931363607993074956049444098463961972401767739562349284233866475116306851744972800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_102 h,accepted_103 h⟩
private noncomputable def tree100 : TapeTree := .centered (candidateRows ibox100) (candidateRows (FixedTape.midBox ibox100))
attribute [irreducible] tree100
private theorem sign_100 : 2*denominator*(computed denominator (FixedTape.midBox ibox100)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox100).gradient k).lo.natAbs ((computed denominator ibox100).gradient k).hi.natAbs : Int)*((ibox100 k).hi-(ibox100 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox100
    (computed denominator ibox100) (computed denominator (FixedTape.midBox ibox100))
    (by decide +kernel)
private theorem midpoint_even_100 : ∀ k, 2 ∣ (ibox100 k).lo+(ibox100 k).hi := by decide +kernel
private theorem accepted_100 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox100) tree100 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox100 midpoint_even_100
  simp only [tree100,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox100,candidate_valid h (FixedTape.midBox ibox100),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox100 106 (FixedTape.rowsAux denominator ibox100 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox100) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_100
private noncomputable def tree99 : TapeTree := .centered (candidateRows ibox99) (candidateRows (FixedTape.midBox ibox99))
attribute [irreducible] tree99
private theorem sign_99 : 2*denominator*(computed denominator (FixedTape.midBox ibox99)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox99).gradient k).lo.natAbs ((computed denominator ibox99).gradient k).hi.natAbs : Int)*((ibox99 k).hi-(ibox99 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox99
    (computed denominator ibox99) (computed denominator (FixedTape.midBox ibox99))
    (by decide +kernel)
private theorem midpoint_even_99 : ∀ k, 2 ∣ (ibox99 k).lo+(ibox99 k).hi := by decide +kernel
private theorem accepted_99 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox99) tree99 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox99 midpoint_even_99
  simp only [tree99,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox99,candidate_valid h (FixedTape.midBox ibox99),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox99 106 (FixedTape.rowsAux denominator ibox99 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox99) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_99
private noncomputable def tree98 : TapeTree := .split 0 (((2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 : Int) : ℚ)/(denominator : ℚ)) tree99 tree100
attribute [irreducible] tree98
private theorem accepted_98 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox98) tree98 = true := by
  simp only [tree98,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox98 0 (2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 : Int) false,decode_split denominator ibox98 0 (2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_99 h,accepted_100 h⟩
private noncomputable def tree97 : TapeTree := .centered (candidateRows ibox97) (candidateRows (FixedTape.midBox ibox97))
attribute [irreducible] tree97
private theorem sign_97 : 2*denominator*(computed denominator (FixedTape.midBox ibox97)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox97).gradient k).lo.natAbs ((computed denominator ibox97).gradient k).hi.natAbs : Int)*((ibox97 k).hi-(ibox97 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox97
    (computed denominator ibox97) (computed denominator (FixedTape.midBox ibox97))
    (by decide +kernel)
private theorem midpoint_even_97 : ∀ k, 2 ∣ (ibox97 k).lo+(ibox97 k).hi := by decide +kernel
private theorem accepted_97 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox97) tree97 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox97 midpoint_even_97
  simp only [tree97,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox97,candidate_valid h (FixedTape.midBox ibox97),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox97 106 (FixedTape.rowsAux denominator ibox97 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox97) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_97
private noncomputable def tree96 : TapeTree := .centered (candidateRows ibox96) (candidateRows (FixedTape.midBox ibox96))
attribute [irreducible] tree96
private theorem sign_96 : 2*denominator*(computed denominator (FixedTape.midBox ibox96)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox96).gradient k).lo.natAbs ((computed denominator ibox96).gradient k).hi.natAbs : Int)*((ibox96 k).hi-(ibox96 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox96
    (computed denominator ibox96) (computed denominator (FixedTape.midBox ibox96))
    (by decide +kernel)
private theorem midpoint_even_96 : ∀ k, 2 ∣ (ibox96 k).lo+(ibox96 k).hi := by decide +kernel
private theorem accepted_96 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox96) tree96 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox96 midpoint_even_96
  simp only [tree96,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox96,candidate_valid h (FixedTape.midBox ibox96),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox96 106 (FixedTape.rowsAux denominator ibox96 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox96) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_96
private noncomputable def tree95 : TapeTree := .split 0 (((2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 : Int) : ℚ)/(denominator : ℚ)) tree96 tree97
attribute [irreducible] tree95
private theorem accepted_95 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox95) tree95 = true := by
  simp only [tree95,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox95 0 (2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 : Int) false,decode_split denominator ibox95 0 (2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_96 h,accepted_97 h⟩
private noncomputable def tree94 : TapeTree := .split 2 (((4562498535755931363607993074956049444098463961972401767739562349284233866475116306851744972800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree95 tree98
attribute [irreducible] tree94
private theorem accepted_94 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox94) tree94 = true := by
  simp only [tree94,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox94 2 (4562498535755931363607993074956049444098463961972401767739562349284233866475116306851744972800000000000000000000000 : Int) false,decode_split denominator ibox94 2 (4562498535755931363607993074956049444098463961972401767739562349284233866475116306851744972800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_95 h,accepted_98 h⟩
private noncomputable def tree93 : TapeTree := .split 3 (((651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree94 tree101
attribute [irreducible] tree93
private theorem accepted_93 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox93) tree93 = true := by
  simp only [tree93,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox93 3 (651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) false,decode_split denominator ibox93 3 (651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_94 h,accepted_101 h⟩
private noncomputable def tree92 : TapeTree := .split 3 (((1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree93 tree104
attribute [irreducible] tree92
private theorem accepted_92 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox92) tree92 = true := by
  simp only [tree92,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox92 3 (1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 : Int) false,decode_split denominator ibox92 3 (1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_93 h,accepted_104 h⟩
private noncomputable def tree91 : TapeTree := .centered (candidateRows ibox91) (candidateRows (FixedTape.midBox ibox91))
attribute [irreducible] tree91
private theorem sign_91 : 2*denominator*(computed denominator (FixedTape.midBox ibox91)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox91).gradient k).lo.natAbs ((computed denominator ibox91).gradient k).hi.natAbs : Int)*((ibox91 k).hi-(ibox91 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox91
    (computed denominator ibox91) (computed denominator (FixedTape.midBox ibox91))
    (by decide +kernel)
private theorem midpoint_even_91 : ∀ k, 2 ∣ (ibox91 k).lo+(ibox91 k).hi := by decide +kernel
private theorem accepted_91 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox91) tree91 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox91 midpoint_even_91
  simp only [tree91,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox91,candidate_valid h (FixedTape.midBox ibox91),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox91 106 (FixedTape.rowsAux denominator ibox91 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox91) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_91
private noncomputable def tree90 : TapeTree := .centered (candidateRows ibox90) (candidateRows (FixedTape.midBox ibox90))
attribute [irreducible] tree90
private theorem sign_90 : 2*denominator*(computed denominator (FixedTape.midBox ibox90)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox90).gradient k).lo.natAbs ((computed denominator ibox90).gradient k).hi.natAbs : Int)*((ibox90 k).hi-(ibox90 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox90
    (computed denominator ibox90) (computed denominator (FixedTape.midBox ibox90))
    (by decide +kernel)
private theorem midpoint_even_90 : ∀ k, 2 ∣ (ibox90 k).lo+(ibox90 k).hi := by decide +kernel
private theorem accepted_90 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox90) tree90 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox90 midpoint_even_90
  simp only [tree90,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox90,candidate_valid h (FixedTape.midBox ibox90),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox90 106 (FixedTape.rowsAux denominator ibox90 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox90) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_90
private noncomputable def tree89 : TapeTree := .split 3 (((1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree90 tree91
attribute [irreducible] tree89
private theorem accepted_89 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox89) tree89 = true := by
  simp only [tree89,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox89 3 (1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) false,decode_split denominator ibox89 3 (1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_90 h,accepted_91 h⟩
private noncomputable def tree88 : TapeTree := .centered (candidateRows ibox88) (candidateRows (FixedTape.midBox ibox88))
attribute [irreducible] tree88
private theorem sign_88 : 2*denominator*(computed denominator (FixedTape.midBox ibox88)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox88).gradient k).lo.natAbs ((computed denominator ibox88).gradient k).hi.natAbs : Int)*((ibox88 k).hi-(ibox88 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox88
    (computed denominator ibox88) (computed denominator (FixedTape.midBox ibox88))
    (by decide +kernel)
private theorem midpoint_even_88 : ∀ k, 2 ∣ (ibox88 k).lo+(ibox88 k).hi := by decide +kernel
private theorem accepted_88 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox88) tree88 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox88 midpoint_even_88
  simp only [tree88,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox88,candidate_valid h (FixedTape.midBox ibox88),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox88 106 (FixedTape.rowsAux denominator ibox88 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox88) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_88
private noncomputable def tree87 : TapeTree := .centered (candidateRows ibox87) (candidateRows (FixedTape.midBox ibox87))
attribute [irreducible] tree87
private theorem sign_87 : 2*denominator*(computed denominator (FixedTape.midBox ibox87)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox87).gradient k).lo.natAbs ((computed denominator ibox87).gradient k).hi.natAbs : Int)*((ibox87 k).hi-(ibox87 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox87
    (computed denominator ibox87) (computed denominator (FixedTape.midBox ibox87))
    (by decide +kernel)
private theorem midpoint_even_87 : ∀ k, 2 ∣ (ibox87 k).lo+(ibox87 k).hi := by decide +kernel
private theorem accepted_87 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox87) tree87 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox87 midpoint_even_87
  simp only [tree87,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox87,candidate_valid h (FixedTape.midBox ibox87),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox87 106 (FixedTape.rowsAux denominator ibox87 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox87) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_87
private noncomputable def tree86 : TapeTree := .split 3 (((1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree87 tree88
attribute [irreducible] tree86
private theorem accepted_86 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox86) tree86 = true := by
  simp only [tree86,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox86 3 (1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) false,decode_split denominator ibox86 3 (1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_87 h,accepted_88 h⟩
private noncomputable def tree85 : TapeTree := .split 2 (((3258927525539950974005709339254321031498902829980286976956830249488738476053654504894103552000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree86 tree89
attribute [irreducible] tree85
private theorem accepted_85 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox85) tree85 = true := by
  simp only [tree85,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox85 2 (3258927525539950974005709339254321031498902829980286976956830249488738476053654504894103552000000000000000000000000 : Int) false,decode_split denominator ibox85 2 (3258927525539950974005709339254321031498902829980286976956830249488738476053654504894103552000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_86 h,accepted_89 h⟩
private noncomputable def tree84 : TapeTree := .centered (candidateRows ibox84) (candidateRows (FixedTape.midBox ibox84))
attribute [irreducible] tree84
private theorem sign_84 : 2*denominator*(computed denominator (FixedTape.midBox ibox84)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox84).gradient k).lo.natAbs ((computed denominator ibox84).gradient k).hi.natAbs : Int)*((ibox84 k).hi-(ibox84 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox84
    (computed denominator ibox84) (computed denominator (FixedTape.midBox ibox84))
    (by decide +kernel)
private theorem midpoint_even_84 : ∀ k, 2 ∣ (ibox84 k).lo+(ibox84 k).hi := by decide +kernel
private theorem accepted_84 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox84) tree84 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox84 midpoint_even_84
  simp only [tree84,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox84,candidate_valid h (FixedTape.midBox ibox84),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox84 106 (FixedTape.rowsAux denominator ibox84 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox84) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_84
private noncomputable def tree83 : TapeTree := .centered (candidateRows ibox83) (candidateRows (FixedTape.midBox ibox83))
attribute [irreducible] tree83
private theorem sign_83 : 2*denominator*(computed denominator (FixedTape.midBox ibox83)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox83).gradient k).lo.natAbs ((computed denominator ibox83).gradient k).hi.natAbs : Int)*((ibox83 k).hi-(ibox83 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox83
    (computed denominator ibox83) (computed denominator (FixedTape.midBox ibox83))
    (by decide +kernel)
private theorem midpoint_even_83 : ∀ k, 2 ∣ (ibox83 k).lo+(ibox83 k).hi := by decide +kernel
private theorem accepted_83 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox83) tree83 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox83 midpoint_even_83
  simp only [tree83,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox83,candidate_valid h (FixedTape.midBox ibox83),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox83 106 (FixedTape.rowsAux denominator ibox83 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox83) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_83
private noncomputable def tree82 : TapeTree := .centered (candidateRows ibox82) (candidateRows (FixedTape.midBox ibox82))
attribute [irreducible] tree82
private theorem sign_82 : 2*denominator*(computed denominator (FixedTape.midBox ibox82)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox82).gradient k).lo.natAbs ((computed denominator ibox82).gradient k).hi.natAbs : Int)*((ibox82 k).hi-(ibox82 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox82
    (computed denominator ibox82) (computed denominator (FixedTape.midBox ibox82))
    (by decide +kernel)
private theorem midpoint_even_82 : ∀ k, 2 ∣ (ibox82 k).lo+(ibox82 k).hi := by decide +kernel
private theorem accepted_82 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox82) tree82 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox82 midpoint_even_82
  simp only [tree82,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox82,candidate_valid h (FixedTape.midBox ibox82),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox82 106 (FixedTape.rowsAux denominator ibox82 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox82) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_82
private noncomputable def tree81 : TapeTree := .split 0 (((2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 : Int) : ℚ)/(denominator : ℚ)) tree82 tree83
attribute [irreducible] tree81
private theorem accepted_81 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox81) tree81 = true := by
  simp only [tree81,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox81 0 (2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 : Int) false,decode_split denominator ibox81 0 (2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_82 h,accepted_83 h⟩
private noncomputable def tree80 : TapeTree := .split 3 (((651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree81 tree84
attribute [irreducible] tree80
private theorem accepted_80 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox80) tree80 = true := by
  simp only [tree80,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox80 3 (651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) false,decode_split denominator ibox80 3 (651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_81 h,accepted_84 h⟩
private noncomputable def tree79 : TapeTree := .centered (candidateRows ibox79) (candidateRows (FixedTape.midBox ibox79))
attribute [irreducible] tree79
private theorem sign_79 : 2*denominator*(computed denominator (FixedTape.midBox ibox79)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox79).gradient k).lo.natAbs ((computed denominator ibox79).gradient k).hi.natAbs : Int)*((ibox79 k).hi-(ibox79 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox79
    (computed denominator ibox79) (computed denominator (FixedTape.midBox ibox79))
    (by decide +kernel)
private theorem midpoint_even_79 : ∀ k, 2 ∣ (ibox79 k).lo+(ibox79 k).hi := by decide +kernel
private theorem accepted_79 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox79) tree79 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox79 midpoint_even_79
  simp only [tree79,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox79,candidate_valid h (FixedTape.midBox ibox79),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox79 106 (FixedTape.rowsAux denominator ibox79 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox79) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_79
private noncomputable def tree78 : TapeTree := .centered (candidateRows ibox78) (candidateRows (FixedTape.midBox ibox78))
attribute [irreducible] tree78
private theorem sign_78 : 2*denominator*(computed denominator (FixedTape.midBox ibox78)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox78).gradient k).lo.natAbs ((computed denominator ibox78).gradient k).hi.natAbs : Int)*((ibox78 k).hi-(ibox78 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox78
    (computed denominator ibox78) (computed denominator (FixedTape.midBox ibox78))
    (by decide +kernel)
private theorem midpoint_even_78 : ∀ k, 2 ∣ (ibox78 k).lo+(ibox78 k).hi := by decide +kernel
private theorem accepted_78 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox78) tree78 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox78 midpoint_even_78
  simp only [tree78,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox78,candidate_valid h (FixedTape.midBox ibox78),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox78 106 (FixedTape.rowsAux denominator ibox78 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox78) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_78
private noncomputable def tree77 : TapeTree := .centered (candidateRows ibox77) (candidateRows (FixedTape.midBox ibox77))
attribute [irreducible] tree77
private theorem sign_77 : 2*denominator*(computed denominator (FixedTape.midBox ibox77)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox77).gradient k).lo.natAbs ((computed denominator ibox77).gradient k).hi.natAbs : Int)*((ibox77 k).hi-(ibox77 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox77
    (computed denominator ibox77) (computed denominator (FixedTape.midBox ibox77))
    (by decide +kernel)
private theorem midpoint_even_77 : ∀ k, 2 ∣ (ibox77 k).lo+(ibox77 k).hi := by decide +kernel
private theorem accepted_77 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox77) tree77 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox77 midpoint_even_77
  simp only [tree77,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox77,candidate_valid h (FixedTape.midBox ibox77),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox77 106 (FixedTape.rowsAux denominator ibox77 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox77) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_77
private noncomputable def tree76 : TapeTree := .split 0 (((2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 : Int) : ℚ)/(denominator : ℚ)) tree77 tree78
attribute [irreducible] tree76
private theorem accepted_76 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox76) tree76 = true := by
  simp only [tree76,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox76 0 (2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 : Int) false,decode_split denominator ibox76 0 (2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_77 h,accepted_78 h⟩
private noncomputable def tree75 : TapeTree := .split 3 (((651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree76 tree79
attribute [irreducible] tree75
private theorem accepted_75 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox75) tree75 = true := by
  simp only [tree75,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox75 3 (651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) false,decode_split denominator ibox75 3 (651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_76 h,accepted_79 h⟩
private noncomputable def tree74 : TapeTree := .split 2 (((3258927525539950974005709339254321031498902829980286976956830249488738476053654504894103552000000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree75 tree80
attribute [irreducible] tree74
private theorem accepted_74 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox74) tree74 = true := by
  simp only [tree74,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox74 2 (3258927525539950974005709339254321031498902829980286976956830249488738476053654504894103552000000000000000000000000 : Int) false,decode_split denominator ibox74 2 (3258927525539950974005709339254321031498902829980286976956830249488738476053654504894103552000000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_75 h,accepted_80 h⟩
private noncomputable def tree73 : TapeTree := .split 3 (((1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree74 tree85
attribute [irreducible] tree73
private theorem accepted_73 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox73) tree73 = true := by
  simp only [tree73,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox73 3 (1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 : Int) false,decode_split denominator ibox73 3 (1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_74 h,accepted_85 h⟩
private noncomputable def tree72 : TapeTree := .split 2 (((3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree73 tree92
attribute [irreducible] tree72
private theorem accepted_72 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox72) tree72 = true := by
  simp only [tree72,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox72 2 (3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 : Int) false,decode_split denominator ibox72 2 (3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_73 h,accepted_92 h⟩
private noncomputable def tree71 : TapeTree := .split 3 (((2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree72 tree111
attribute [irreducible] tree71
private theorem accepted_71 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox71) tree71 = true := by
  simp only [tree71,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox71 3 (2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 : Int) false,decode_split denominator ibox71 3 (2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_72 h,accepted_111 h⟩
private noncomputable def tree70 : TapeTree := .centered (candidateRows ibox70) (candidateRows (FixedTape.midBox ibox70))
attribute [irreducible] tree70
private theorem sign_70 : 2*denominator*(computed denominator (FixedTape.midBox ibox70)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox70).gradient k).lo.natAbs ((computed denominator ibox70).gradient k).hi.natAbs : Int)*((ibox70 k).hi-(ibox70 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox70
    (computed denominator ibox70) (computed denominator (FixedTape.midBox ibox70))
    (by decide +kernel)
private theorem midpoint_even_70 : ∀ k, 2 ∣ (ibox70 k).lo+(ibox70 k).hi := by decide +kernel
private theorem accepted_70 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox70) tree70 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox70 midpoint_even_70
  simp only [tree70,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox70,candidate_valid h (FixedTape.midBox ibox70),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox70 106 (FixedTape.rowsAux denominator ibox70 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox70) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_70
private noncomputable def tree69 : TapeTree := .centered (candidateRows ibox69) (candidateRows (FixedTape.midBox ibox69))
attribute [irreducible] tree69
private theorem sign_69 : 2*denominator*(computed denominator (FixedTape.midBox ibox69)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox69).gradient k).lo.natAbs ((computed denominator ibox69).gradient k).hi.natAbs : Int)*((ibox69 k).hi-(ibox69 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox69
    (computed denominator ibox69) (computed denominator (FixedTape.midBox ibox69))
    (by decide +kernel)
private theorem midpoint_even_69 : ∀ k, 2 ∣ (ibox69 k).lo+(ibox69 k).hi := by decide +kernel
private theorem accepted_69 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox69) tree69 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox69 midpoint_even_69
  simp only [tree69,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox69,candidate_valid h (FixedTape.midBox ibox69),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox69 106 (FixedTape.rowsAux denominator ibox69 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox69) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_69
private noncomputable def tree68 : TapeTree := .split 2 (((1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree69 tree70
attribute [irreducible] tree68
private theorem accepted_68 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox68) tree68 = true := by
  simp only [tree68,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox68 2 (1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) false,decode_split denominator ibox68 2 (1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_69 h,accepted_70 h⟩
private noncomputable def tree67 : TapeTree := .centered (candidateRows ibox67) (candidateRows (FixedTape.midBox ibox67))
attribute [irreducible] tree67
private theorem sign_67 : 2*denominator*(computed denominator (FixedTape.midBox ibox67)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox67).gradient k).lo.natAbs ((computed denominator ibox67).gradient k).hi.natAbs : Int)*((ibox67 k).hi-(ibox67 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox67
    (computed denominator ibox67) (computed denominator (FixedTape.midBox ibox67))
    (by decide +kernel)
private theorem midpoint_even_67 : ∀ k, 2 ∣ (ibox67 k).lo+(ibox67 k).hi := by decide +kernel
private theorem accepted_67 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox67) tree67 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox67 midpoint_even_67
  simp only [tree67,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox67,candidate_valid h (FixedTape.midBox ibox67),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox67 106 (FixedTape.rowsAux denominator ibox67 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox67) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_67
private noncomputable def tree66 : TapeTree := .centered (candidateRows ibox66) (candidateRows (FixedTape.midBox ibox66))
attribute [irreducible] tree66
private theorem sign_66 : 2*denominator*(computed denominator (FixedTape.midBox ibox66)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox66).gradient k).lo.natAbs ((computed denominator ibox66).gradient k).hi.natAbs : Int)*((ibox66 k).hi-(ibox66 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox66
    (computed denominator ibox66) (computed denominator (FixedTape.midBox ibox66))
    (by decide +kernel)
private theorem midpoint_even_66 : ∀ k, 2 ∣ (ibox66 k).lo+(ibox66 k).hi := by decide +kernel
private theorem accepted_66 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox66) tree66 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox66 midpoint_even_66
  simp only [tree66,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox66,candidate_valid h (FixedTape.midBox ibox66),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox66 106 (FixedTape.rowsAux denominator ibox66 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox66) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_66
private noncomputable def tree65 : TapeTree := .split 2 (((1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree66 tree67
attribute [irreducible] tree65
private theorem accepted_65 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox65) tree65 = true := by
  simp only [tree65,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox65 2 (1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) false,decode_split denominator ibox65 2 (1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_66 h,accepted_67 h⟩
private noncomputable def tree64 : TapeTree := .split 3 (((3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree65 tree68
attribute [irreducible] tree64
private theorem accepted_64 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox64) tree64 = true := by
  simp only [tree64,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox64 3 (3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 : Int) false,decode_split denominator ibox64 3 (3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_65 h,accepted_68 h⟩
private noncomputable def tree63 : TapeTree := .centered (candidateRows ibox63) (candidateRows (FixedTape.midBox ibox63))
attribute [irreducible] tree63
private theorem sign_63 : 2*denominator*(computed denominator (FixedTape.midBox ibox63)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox63).gradient k).lo.natAbs ((computed denominator ibox63).gradient k).hi.natAbs : Int)*((ibox63 k).hi-(ibox63 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox63
    (computed denominator ibox63) (computed denominator (FixedTape.midBox ibox63))
    (by decide +kernel)
private theorem midpoint_even_63 : ∀ k, 2 ∣ (ibox63 k).lo+(ibox63 k).hi := by decide +kernel
private theorem accepted_63 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox63) tree63 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox63 midpoint_even_63
  simp only [tree63,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox63,candidate_valid h (FixedTape.midBox ibox63),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox63 106 (FixedTape.rowsAux denominator ibox63 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox63) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_63
private noncomputable def tree62 : TapeTree := .centered (candidateRows ibox62) (candidateRows (FixedTape.midBox ibox62))
attribute [irreducible] tree62
private theorem sign_62 : 2*denominator*(computed denominator (FixedTape.midBox ibox62)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox62).gradient k).lo.natAbs ((computed denominator ibox62).gradient k).hi.natAbs : Int)*((ibox62 k).hi-(ibox62 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox62
    (computed denominator ibox62) (computed denominator (FixedTape.midBox ibox62))
    (by decide +kernel)
private theorem midpoint_even_62 : ∀ k, 2 ∣ (ibox62 k).lo+(ibox62 k).hi := by decide +kernel
private theorem accepted_62 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox62) tree62 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox62 midpoint_even_62
  simp only [tree62,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox62,candidate_valid h (FixedTape.midBox ibox62),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox62 106 (FixedTape.rowsAux denominator ibox62 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox62) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_62
private noncomputable def tree61 : TapeTree := .split 2 (((651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree62 tree63
attribute [irreducible] tree61
private theorem accepted_61 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox61) tree61 = true := by
  simp only [tree61,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox61 2 (651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) false,decode_split denominator ibox61 2 (651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_62 h,accepted_63 h⟩
private noncomputable def tree60 : TapeTree := .centered (candidateRows ibox60) (candidateRows (FixedTape.midBox ibox60))
attribute [irreducible] tree60
private theorem sign_60 : 2*denominator*(computed denominator (FixedTape.midBox ibox60)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox60).gradient k).lo.natAbs ((computed denominator ibox60).gradient k).hi.natAbs : Int)*((ibox60 k).hi-(ibox60 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox60
    (computed denominator ibox60) (computed denominator (FixedTape.midBox ibox60))
    (by decide +kernel)
private theorem midpoint_even_60 : ∀ k, 2 ∣ (ibox60 k).lo+(ibox60 k).hi := by decide +kernel
private theorem accepted_60 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox60) tree60 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox60 midpoint_even_60
  simp only [tree60,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox60,candidate_valid h (FixedTape.midBox ibox60),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox60 106 (FixedTape.rowsAux denominator ibox60 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox60) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_60
private noncomputable def tree59 : TapeTree := .centered (candidateRows ibox59) (candidateRows (FixedTape.midBox ibox59))
attribute [irreducible] tree59
private theorem sign_59 : 2*denominator*(computed denominator (FixedTape.midBox ibox59)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox59).gradient k).lo.natAbs ((computed denominator ibox59).gradient k).hi.natAbs : Int)*((ibox59 k).hi-(ibox59 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox59
    (computed denominator ibox59) (computed denominator (FixedTape.midBox ibox59))
    (by decide +kernel)
private theorem midpoint_even_59 : ∀ k, 2 ∣ (ibox59 k).lo+(ibox59 k).hi := by decide +kernel
private theorem accepted_59 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox59) tree59 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox59 midpoint_even_59
  simp only [tree59,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox59,candidate_valid h (FixedTape.midBox ibox59),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox59 106 (FixedTape.rowsAux denominator ibox59 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox59) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_59
private noncomputable def tree58 : TapeTree := .split 2 (((651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree59 tree60
attribute [irreducible] tree58
private theorem accepted_58 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox58) tree58 = true := by
  simp only [tree58,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox58 2 (651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) false,decode_split denominator ibox58 2 (651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_59 h,accepted_60 h⟩
private noncomputable def tree57 : TapeTree := .split 3 (((3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree58 tree61
attribute [irreducible] tree57
private theorem accepted_57 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox57) tree57 = true := by
  simp only [tree57,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox57 3 (3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 : Int) false,decode_split denominator ibox57 3 (3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_58 h,accepted_61 h⟩
private noncomputable def tree56 : TapeTree := .split 2 (((1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree57 tree64
attribute [irreducible] tree56
private theorem accepted_56 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox56) tree56 = true := by
  simp only [tree56,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox56 2 (1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 : Int) false,decode_split denominator ibox56 2 (1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_57 h,accepted_64 h⟩
private noncomputable def tree55 : TapeTree := .centered (candidateRows ibox55) (candidateRows (FixedTape.midBox ibox55))
attribute [irreducible] tree55
private theorem sign_55 : 2*denominator*(computed denominator (FixedTape.midBox ibox55)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox55).gradient k).lo.natAbs ((computed denominator ibox55).gradient k).hi.natAbs : Int)*((ibox55 k).hi-(ibox55 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox55
    (computed denominator ibox55) (computed denominator (FixedTape.midBox ibox55))
    (by decide +kernel)
private theorem midpoint_even_55 : ∀ k, 2 ∣ (ibox55 k).lo+(ibox55 k).hi := by decide +kernel
private theorem accepted_55 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox55) tree55 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox55 midpoint_even_55
  simp only [tree55,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox55,candidate_valid h (FixedTape.midBox ibox55),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox55 106 (FixedTape.rowsAux denominator ibox55 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox55) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_55
private noncomputable def tree54 : TapeTree := .centered (candidateRows ibox54) (candidateRows (FixedTape.midBox ibox54))
attribute [irreducible] tree54
private theorem sign_54 : 2*denominator*(computed denominator (FixedTape.midBox ibox54)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox54).gradient k).lo.natAbs ((computed denominator ibox54).gradient k).hi.natAbs : Int)*((ibox54 k).hi-(ibox54 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox54
    (computed denominator ibox54) (computed denominator (FixedTape.midBox ibox54))
    (by decide +kernel)
private theorem midpoint_even_54 : ∀ k, 2 ∣ (ibox54 k).lo+(ibox54 k).hi := by decide +kernel
private theorem accepted_54 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox54) tree54 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox54 midpoint_even_54
  simp only [tree54,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox54,candidate_valid h (FixedTape.midBox ibox54),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox54 106 (FixedTape.rowsAux denominator ibox54 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox54) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_54
private noncomputable def tree53 : TapeTree := .split 3 (((1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree54 tree55
attribute [irreducible] tree53
private theorem accepted_53 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox53) tree53 = true := by
  simp only [tree53,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox53 3 (1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) false,decode_split denominator ibox53 3 (1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_54 h,accepted_55 h⟩
private noncomputable def tree52 : TapeTree := .centered (candidateRows ibox52) (candidateRows (FixedTape.midBox ibox52))
attribute [irreducible] tree52
private theorem sign_52 : 2*denominator*(computed denominator (FixedTape.midBox ibox52)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox52).gradient k).lo.natAbs ((computed denominator ibox52).gradient k).hi.natAbs : Int)*((ibox52 k).hi-(ibox52 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox52
    (computed denominator ibox52) (computed denominator (FixedTape.midBox ibox52))
    (by decide +kernel)
private theorem midpoint_even_52 : ∀ k, 2 ∣ (ibox52 k).lo+(ibox52 k).hi := by decide +kernel
private theorem accepted_52 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox52) tree52 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox52 midpoint_even_52
  simp only [tree52,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox52,candidate_valid h (FixedTape.midBox ibox52),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox52 106 (FixedTape.rowsAux denominator ibox52 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox52) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_52
private noncomputable def tree51 : TapeTree := .centered (candidateRows ibox51) (candidateRows (FixedTape.midBox ibox51))
attribute [irreducible] tree51
private theorem sign_51 : 2*denominator*(computed denominator (FixedTape.midBox ibox51)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox51).gradient k).lo.natAbs ((computed denominator ibox51).gradient k).hi.natAbs : Int)*((ibox51 k).hi-(ibox51 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox51
    (computed denominator ibox51) (computed denominator (FixedTape.midBox ibox51))
    (by decide +kernel)
private theorem midpoint_even_51 : ∀ k, 2 ∣ (ibox51 k).lo+(ibox51 k).hi := by decide +kernel
private theorem accepted_51 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox51) tree51 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox51 midpoint_even_51
  simp only [tree51,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox51,candidate_valid h (FixedTape.midBox ibox51),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox51 106 (FixedTape.rowsAux denominator ibox51 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox51) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_51
private noncomputable def tree50 : TapeTree := .split 3 (((1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree51 tree52
attribute [irreducible] tree50
private theorem accepted_50 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox50) tree50 = true := by
  simp only [tree50,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox50 3 (1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) false,decode_split denominator ibox50 3 (1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_51 h,accepted_52 h⟩
private noncomputable def tree49 : TapeTree := .split 2 (((1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree50 tree53
attribute [irreducible] tree49
private theorem accepted_49 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox49) tree49 = true := by
  simp only [tree49,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox49 2 (1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) false,decode_split denominator ibox49 2 (1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_50 h,accepted_53 h⟩
private noncomputable def tree48 : TapeTree := .centered (candidateRows ibox48) (candidateRows (FixedTape.midBox ibox48))
attribute [irreducible] tree48
private theorem sign_48 : 2*denominator*(computed denominator (FixedTape.midBox ibox48)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox48).gradient k).lo.natAbs ((computed denominator ibox48).gradient k).hi.natAbs : Int)*((ibox48 k).hi-(ibox48 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox48
    (computed denominator ibox48) (computed denominator (FixedTape.midBox ibox48))
    (by decide +kernel)
private theorem midpoint_even_48 : ∀ k, 2 ∣ (ibox48 k).lo+(ibox48 k).hi := by decide +kernel
private theorem accepted_48 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox48) tree48 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox48 midpoint_even_48
  simp only [tree48,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox48,candidate_valid h (FixedTape.midBox ibox48),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox48 106 (FixedTape.rowsAux denominator ibox48 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox48) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_48
private noncomputable def tree47 : TapeTree := .centered (candidateRows ibox47) (candidateRows (FixedTape.midBox ibox47))
attribute [irreducible] tree47
private theorem sign_47 : 2*denominator*(computed denominator (FixedTape.midBox ibox47)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox47).gradient k).lo.natAbs ((computed denominator ibox47).gradient k).hi.natAbs : Int)*((ibox47 k).hi-(ibox47 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox47
    (computed denominator ibox47) (computed denominator (FixedTape.midBox ibox47))
    (by decide +kernel)
private theorem midpoint_even_47 : ∀ k, 2 ∣ (ibox47 k).lo+(ibox47 k).hi := by decide +kernel
private theorem accepted_47 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox47) tree47 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox47 midpoint_even_47
  simp only [tree47,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox47,candidate_valid h (FixedTape.midBox ibox47),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox47 106 (FixedTape.rowsAux denominator ibox47 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox47) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_47
private noncomputable def tree46 : TapeTree := .centered (candidateRows ibox46) (candidateRows (FixedTape.midBox ibox46))
attribute [irreducible] tree46
private theorem sign_46 : 2*denominator*(computed denominator (FixedTape.midBox ibox46)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox46).gradient k).lo.natAbs ((computed denominator ibox46).gradient k).hi.natAbs : Int)*((ibox46 k).hi-(ibox46 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox46
    (computed denominator ibox46) (computed denominator (FixedTape.midBox ibox46))
    (by decide +kernel)
private theorem midpoint_even_46 : ∀ k, 2 ∣ (ibox46 k).lo+(ibox46 k).hi := by decide +kernel
private theorem accepted_46 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox46) tree46 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox46 midpoint_even_46
  simp only [tree46,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox46,candidate_valid h (FixedTape.midBox ibox46),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox46 106 (FixedTape.rowsAux denominator ibox46 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox46) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_46
private noncomputable def tree45 : TapeTree := .split 0 (((2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 : Int) : ℚ)/(denominator : ℚ)) tree46 tree47
attribute [irreducible] tree45
private theorem accepted_45 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox45) tree45 = true := by
  simp only [tree45,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox45 0 (2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 : Int) false,decode_split denominator ibox45 0 (2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_46 h,accepted_47 h⟩
private noncomputable def tree44 : TapeTree := .split 3 (((651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree45 tree48
attribute [irreducible] tree44
private theorem accepted_44 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox44) tree44 = true := by
  simp only [tree44,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox44 3 (651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) false,decode_split denominator ibox44 3 (651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_45 h,accepted_48 h⟩
private noncomputable def tree43 : TapeTree := .centered (candidateRows ibox43) (candidateRows (FixedTape.midBox ibox43))
attribute [irreducible] tree43
private theorem sign_43 : 2*denominator*(computed denominator (FixedTape.midBox ibox43)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox43).gradient k).lo.natAbs ((computed denominator ibox43).gradient k).hi.natAbs : Int)*((ibox43 k).hi-(ibox43 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox43
    (computed denominator ibox43) (computed denominator (FixedTape.midBox ibox43))
    (by decide +kernel)
private theorem midpoint_even_43 : ∀ k, 2 ∣ (ibox43 k).lo+(ibox43 k).hi := by decide +kernel
private theorem accepted_43 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox43) tree43 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox43 midpoint_even_43
  simp only [tree43,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox43,candidate_valid h (FixedTape.midBox ibox43),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox43 106 (FixedTape.rowsAux denominator ibox43 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox43) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_43
private noncomputable def tree42 : TapeTree := .centered (candidateRows ibox42) (candidateRows (FixedTape.midBox ibox42))
attribute [irreducible] tree42
private theorem sign_42 : 2*denominator*(computed denominator (FixedTape.midBox ibox42)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox42).gradient k).lo.natAbs ((computed denominator ibox42).gradient k).hi.natAbs : Int)*((ibox42 k).hi-(ibox42 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox42
    (computed denominator ibox42) (computed denominator (FixedTape.midBox ibox42))
    (by decide +kernel)
private theorem midpoint_even_42 : ∀ k, 2 ∣ (ibox42 k).lo+(ibox42 k).hi := by decide +kernel
private theorem accepted_42 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox42) tree42 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox42 midpoint_even_42
  simp only [tree42,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox42,candidate_valid h (FixedTape.midBox ibox42),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox42 106 (FixedTape.rowsAux denominator ibox42 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox42) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_42
private noncomputable def tree41 : TapeTree := .centered (candidateRows ibox41) (candidateRows (FixedTape.midBox ibox41))
attribute [irreducible] tree41
private theorem sign_41 : 2*denominator*(computed denominator (FixedTape.midBox ibox41)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox41).gradient k).lo.natAbs ((computed denominator ibox41).gradient k).hi.natAbs : Int)*((ibox41 k).hi-(ibox41 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox41
    (computed denominator ibox41) (computed denominator (FixedTape.midBox ibox41))
    (by decide +kernel)
private theorem midpoint_even_41 : ∀ k, 2 ∣ (ibox41 k).lo+(ibox41 k).hi := by decide +kernel
private theorem accepted_41 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox41) tree41 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox41 midpoint_even_41
  simp only [tree41,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox41,candidate_valid h (FixedTape.midBox ibox41),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox41 106 (FixedTape.rowsAux denominator ibox41 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox41) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_41
private noncomputable def tree40 : TapeTree := .split 0 (((2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 : Int) : ℚ)/(denominator : ℚ)) tree41 tree42
attribute [irreducible] tree40
private theorem accepted_40 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox40) tree40 = true := by
  simp only [tree40,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox40 0 (2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 : Int) false,decode_split denominator ibox40 0 (2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_41 h,accepted_42 h⟩
private noncomputable def tree39 : TapeTree := .split 3 (((651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree40 tree43
attribute [irreducible] tree39
private theorem accepted_39 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox39) tree39 = true := by
  simp only [tree39,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox39 3 (651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) false,decode_split denominator ibox39 3 (651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_40 h,accepted_43 h⟩
private noncomputable def tree38 : TapeTree := .split 2 (((1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree39 tree44
attribute [irreducible] tree38
private theorem accepted_38 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox38) tree38 = true := by
  simp only [tree38,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox38 2 (1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) false,decode_split denominator ibox38 2 (1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_39 h,accepted_44 h⟩
private noncomputable def tree37 : TapeTree := .split 3 (((1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree38 tree49
attribute [irreducible] tree37
private theorem accepted_37 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox37) tree37 = true := by
  simp only [tree37,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox37 3 (1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 : Int) false,decode_split denominator ibox37 3 (1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_38 h,accepted_49 h⟩
private noncomputable def tree36 : TapeTree := .centered (candidateRows ibox36) (candidateRows (FixedTape.midBox ibox36))
attribute [irreducible] tree36
private theorem sign_36 : 2*denominator*(computed denominator (FixedTape.midBox ibox36)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox36).gradient k).lo.natAbs ((computed denominator ibox36).gradient k).hi.natAbs : Int)*((ibox36 k).hi-(ibox36 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox36
    (computed denominator ibox36) (computed denominator (FixedTape.midBox ibox36))
    (by decide +kernel)
private theorem midpoint_even_36 : ∀ k, 2 ∣ (ibox36 k).lo+(ibox36 k).hi := by decide +kernel
private theorem accepted_36 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox36) tree36 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox36 midpoint_even_36
  simp only [tree36,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox36,candidate_valid h (FixedTape.midBox ibox36),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox36 106 (FixedTape.rowsAux denominator ibox36 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox36) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_36
private noncomputable def tree35 : TapeTree := .centered (candidateRows ibox35) (candidateRows (FixedTape.midBox ibox35))
attribute [irreducible] tree35
private theorem sign_35 : 2*denominator*(computed denominator (FixedTape.midBox ibox35)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox35).gradient k).lo.natAbs ((computed denominator ibox35).gradient k).hi.natAbs : Int)*((ibox35 k).hi-(ibox35 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox35
    (computed denominator ibox35) (computed denominator (FixedTape.midBox ibox35))
    (by decide +kernel)
private theorem midpoint_even_35 : ∀ k, 2 ∣ (ibox35 k).lo+(ibox35 k).hi := by decide +kernel
private theorem accepted_35 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox35) tree35 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox35 midpoint_even_35
  simp only [tree35,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox35,candidate_valid h (FixedTape.midBox ibox35),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox35 106 (FixedTape.rowsAux denominator ibox35 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox35) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_35
private noncomputable def tree34 : TapeTree := .split 3 (((1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree35 tree36
attribute [irreducible] tree34
private theorem accepted_34 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox34) tree34 = true := by
  simp only [tree34,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox34 3 (1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) false,decode_split denominator ibox34 3 (1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_35 h,accepted_36 h⟩
private noncomputable def tree33 : TapeTree := .centered (candidateRows ibox33) (candidateRows (FixedTape.midBox ibox33))
attribute [irreducible] tree33
private theorem sign_33 : 2*denominator*(computed denominator (FixedTape.midBox ibox33)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox33).gradient k).lo.natAbs ((computed denominator ibox33).gradient k).hi.natAbs : Int)*((ibox33 k).hi-(ibox33 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox33
    (computed denominator ibox33) (computed denominator (FixedTape.midBox ibox33))
    (by decide +kernel)
private theorem midpoint_even_33 : ∀ k, 2 ∣ (ibox33 k).lo+(ibox33 k).hi := by decide +kernel
private theorem accepted_33 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox33) tree33 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox33 midpoint_even_33
  simp only [tree33,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox33,candidate_valid h (FixedTape.midBox ibox33),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox33 106 (FixedTape.rowsAux denominator ibox33 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox33) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_33
private noncomputable def tree32 : TapeTree := .centered (candidateRows ibox32) (candidateRows (FixedTape.midBox ibox32))
attribute [irreducible] tree32
private theorem sign_32 : 2*denominator*(computed denominator (FixedTape.midBox ibox32)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox32).gradient k).lo.natAbs ((computed denominator ibox32).gradient k).hi.natAbs : Int)*((ibox32 k).hi-(ibox32 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox32
    (computed denominator ibox32) (computed denominator (FixedTape.midBox ibox32))
    (by decide +kernel)
private theorem midpoint_even_32 : ∀ k, 2 ∣ (ibox32 k).lo+(ibox32 k).hi := by decide +kernel
private theorem accepted_32 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox32) tree32 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox32 midpoint_even_32
  simp only [tree32,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox32,candidate_valid h (FixedTape.midBox ibox32),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox32 106 (FixedTape.rowsAux denominator ibox32 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox32) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_32
private noncomputable def tree31 : TapeTree := .split 3 (((1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree32 tree33
attribute [irreducible] tree31
private theorem accepted_31 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox31) tree31 = true := by
  simp only [tree31,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox31 3 (1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) false,decode_split denominator ibox31 3 (1955356515323970584403425603552592618899341697988172186174098149693243085632192702936462131200000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_32 h,accepted_33 h⟩
private noncomputable def tree30 : TapeTree := .split 2 (((651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree31 tree34
attribute [irreducible] tree30
private theorem accepted_30 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox30) tree30 = true := by
  simp only [tree30,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox30 2 (651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) false,decode_split denominator ibox30 2 (651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_31 h,accepted_34 h⟩
private noncomputable def tree29 : TapeTree := .centered (candidateRows ibox29) (candidateRows (FixedTape.midBox ibox29))
attribute [irreducible] tree29
private theorem sign_29 : 2*denominator*(computed denominator (FixedTape.midBox ibox29)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox29).gradient k).lo.natAbs ((computed denominator ibox29).gradient k).hi.natAbs : Int)*((ibox29 k).hi-(ibox29 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox29
    (computed denominator ibox29) (computed denominator (FixedTape.midBox ibox29))
    (by decide +kernel)
private theorem midpoint_even_29 : ∀ k, 2 ∣ (ibox29 k).lo+(ibox29 k).hi := by decide +kernel
private theorem accepted_29 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox29) tree29 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox29 midpoint_even_29
  simp only [tree29,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox29,candidate_valid h (FixedTape.midBox ibox29),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox29 106 (FixedTape.rowsAux denominator ibox29 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox29) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_29
private noncomputable def tree28 : TapeTree := .centered (candidateRows ibox28) (candidateRows (FixedTape.midBox ibox28))
attribute [irreducible] tree28
private theorem sign_28 : 2*denominator*(computed denominator (FixedTape.midBox ibox28)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox28).gradient k).lo.natAbs ((computed denominator ibox28).gradient k).hi.natAbs : Int)*((ibox28 k).hi-(ibox28 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox28
    (computed denominator ibox28) (computed denominator (FixedTape.midBox ibox28))
    (by decide +kernel)
private theorem midpoint_even_28 : ∀ k, 2 ∣ (ibox28 k).lo+(ibox28 k).hi := by decide +kernel
private theorem accepted_28 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox28) tree28 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox28 midpoint_even_28
  simp only [tree28,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox28,candidate_valid h (FixedTape.midBox ibox28),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox28 106 (FixedTape.rowsAux denominator ibox28 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox28) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_28
private noncomputable def tree27 : TapeTree := .centered (candidateRows ibox27) (candidateRows (FixedTape.midBox ibox27))
attribute [irreducible] tree27
private theorem sign_27 : 2*denominator*(computed denominator (FixedTape.midBox ibox27)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox27).gradient k).lo.natAbs ((computed denominator ibox27).gradient k).hi.natAbs : Int)*((ibox27 k).hi-(ibox27 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox27
    (computed denominator ibox27) (computed denominator (FixedTape.midBox ibox27))
    (by decide +kernel)
private theorem midpoint_even_27 : ∀ k, 2 ∣ (ibox27 k).lo+(ibox27 k).hi := by decide +kernel
private theorem accepted_27 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox27) tree27 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox27 midpoint_even_27
  simp only [tree27,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox27,candidate_valid h (FixedTape.midBox ibox27),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox27 106 (FixedTape.rowsAux denominator ibox27 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox27) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_27
private noncomputable def tree26 : TapeTree := .split 0 (((2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 : Int) : ℚ)/(denominator : ℚ)) tree27 tree28
attribute [irreducible] tree26
private theorem accepted_26 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox26) tree26 = true := by
  simp only [tree26,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox26 0 (2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 : Int) false,decode_split denominator ibox26 0 (2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_27 h,accepted_28 h⟩
private noncomputable def tree25 : TapeTree := .split 3 (((651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree26 tree29
attribute [irreducible] tree25
private theorem accepted_25 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox25) tree25 = true := by
  simp only [tree25,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox25 3 (651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) false,decode_split denominator ibox25 3 (651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_26 h,accepted_29 h⟩
private noncomputable def tree24 : TapeTree := .centered (candidateRows ibox24) (candidateRows (FixedTape.midBox ibox24))
attribute [irreducible] tree24
private theorem sign_24 : 2*denominator*(computed denominator (FixedTape.midBox ibox24)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox24).gradient k).lo.natAbs ((computed denominator ibox24).gradient k).hi.natAbs : Int)*((ibox24 k).hi-(ibox24 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox24
    (computed denominator ibox24) (computed denominator (FixedTape.midBox ibox24))
    (by decide +kernel)
private theorem midpoint_even_24 : ∀ k, 2 ∣ (ibox24 k).lo+(ibox24 k).hi := by decide +kernel
private theorem accepted_24 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox24) tree24 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox24 midpoint_even_24
  simp only [tree24,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox24,candidate_valid h (FixedTape.midBox ibox24),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox24 106 (FixedTape.rowsAux denominator ibox24 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox24) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_24
private noncomputable def tree23 : TapeTree := .centered (candidateRows ibox23) (candidateRows (FixedTape.midBox ibox23))
attribute [irreducible] tree23
private theorem sign_23 : 2*denominator*(computed denominator (FixedTape.midBox ibox23)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox23).gradient k).lo.natAbs ((computed denominator ibox23).gradient k).hi.natAbs : Int)*((ibox23 k).hi-(ibox23 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox23
    (computed denominator ibox23) (computed denominator (FixedTape.midBox ibox23))
    (by decide +kernel)
private theorem midpoint_even_23 : ∀ k, 2 ∣ (ibox23 k).lo+(ibox23 k).hi := by decide +kernel
private theorem accepted_23 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox23) tree23 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox23 midpoint_even_23
  simp only [tree23,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox23,candidate_valid h (FixedTape.midBox ibox23),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox23 106 (FixedTape.rowsAux denominator ibox23 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox23) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_23
private noncomputable def tree22 : TapeTree := .centered (candidateRows ibox22) (candidateRows (FixedTape.midBox ibox22))
attribute [irreducible] tree22
private theorem sign_22 : 2*denominator*(computed denominator (FixedTape.midBox ibox22)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox22).gradient k).lo.natAbs ((computed denominator ibox22).gradient k).hi.natAbs : Int)*((ibox22 k).hi-(ibox22 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox22
    (computed denominator ibox22) (computed denominator (FixedTape.midBox ibox22))
    (by decide +kernel)
private theorem midpoint_even_22 : ∀ k, 2 ∣ (ibox22 k).lo+(ibox22 k).hi := by decide +kernel
private theorem accepted_22 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox22) tree22 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox22 midpoint_even_22
  simp only [tree22,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox22,candidate_valid h (FixedTape.midBox ibox22),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox22 106 (FixedTape.rowsAux denominator ibox22 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox22) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_22
private noncomputable def tree21 : TapeTree := .split 0 (((2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 : Int) : ℚ)/(denominator : ℚ)) tree22 tree23
attribute [irreducible] tree21
private theorem accepted_21 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox21) tree21 = true := by
  simp only [tree21,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox21 0 (2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 : Int) false,decode_split denominator ibox21 0 (2471353373534462908859063596666552755705583692850278464163005072003279396522827985911054555030786797176094720000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_22 h,accepted_23 h⟩
private noncomputable def tree20 : TapeTree := .split 3 (((651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree21 tree24
attribute [irreducible] tree20
private theorem accepted_20 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox20) tree20 = true := by
  simp only [tree20,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox20 3 (651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) false,decode_split denominator ibox20 3 (651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_21 h,accepted_24 h⟩
private noncomputable def tree19 : TapeTree := .split 2 (((651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree20 tree25
attribute [irreducible] tree19
private theorem accepted_19 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox19) tree19 = true := by
  simp only [tree19,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox19 2 (651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) false,decode_split denominator ibox19 2 (651785505107990194801141867850864206299780565996057395391366049897747695210730900978820710400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_20 h,accepted_25 h⟩
private noncomputable def tree18 : TapeTree := .split 3 (((1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree19 tree30
attribute [irreducible] tree18
private theorem accepted_18 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox18) tree18 = true := by
  simp only [tree18,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox18 3 (1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 : Int) false,decode_split denominator ibox18 3 (1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_19 h,accepted_30 h⟩
private noncomputable def tree17 : TapeTree := .split 2 (((1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree18 tree37
attribute [irreducible] tree17
private theorem accepted_17 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox17) tree17 = true := by
  simp only [tree17,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox17 2 (1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 : Int) false,decode_split denominator ibox17 2 (1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_18 h,accepted_37 h⟩
private noncomputable def tree16 : TapeTree := .split 3 (((2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree17 tree56
attribute [irreducible] tree16
private theorem accepted_16 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox16) tree16 = true := by
  simp only [tree16,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox16 3 (2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 : Int) false,decode_split denominator ibox16 3 (2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_17 h,accepted_56 h⟩
private noncomputable def tree15 : TapeTree := .split 2 (((2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree16 tree71
attribute [irreducible] tree15
private theorem accepted_15 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox15) tree15 = true := by
  simp only [tree15,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox15 2 (2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 : Int) false,decode_split denominator ibox15 2 (2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_16 h,accepted_71 h⟩
private noncomputable def tree14 : TapeTree := .face 1 true (candidateRows ibox14) tree15
attribute [irreducible] tree14
private theorem sign_14 : 0 ≤ ((computed denominator ibox14).gradient 1).lo := by decide +kernel
private theorem accepted_14 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox14) tree14 = true := by
  simp only [tree14,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox14,?_,accepted_15 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox14)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox14).gradient 1).lo) denominator_positive).2 sign_14
private noncomputable def tree13 : TapeTree := .centered (candidateRows ibox13) (candidateRows (FixedTape.midBox ibox13))
attribute [irreducible] tree13
private theorem sign_13 : 2*denominator*(computed denominator (FixedTape.midBox ibox13)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox13).gradient k).lo.natAbs ((computed denominator ibox13).gradient k).hi.natAbs : Int)*((ibox13 k).hi-(ibox13 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox13
    (computed denominator ibox13) (computed denominator (FixedTape.midBox ibox13))
    (by decide +kernel)
private theorem midpoint_even_13 : ∀ k, 2 ∣ (ibox13 k).lo+(ibox13 k).hi := by decide +kernel
private theorem accepted_13 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox13) tree13 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox13 midpoint_even_13
  simp only [tree13,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox13,candidate_valid h (FixedTape.midBox ibox13),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox13 106 (FixedTape.rowsAux denominator ibox13 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox13) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_13
private noncomputable def tree12 : TapeTree := .centered (candidateRows ibox12) (candidateRows (FixedTape.midBox ibox12))
attribute [irreducible] tree12
private theorem sign_12 : 2*denominator*(computed denominator (FixedTape.midBox ibox12)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox12).gradient k).lo.natAbs ((computed denominator ibox12).gradient k).hi.natAbs : Int)*((ibox12 k).hi-(ibox12 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox12
    (computed denominator ibox12) (computed denominator (FixedTape.midBox ibox12))
    (by decide +kernel)
private theorem midpoint_even_12 : ∀ k, 2 ∣ (ibox12 k).lo+(ibox12 k).hi := by decide +kernel
private theorem accepted_12 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox12) tree12 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox12 midpoint_even_12
  simp only [tree12,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox12,candidate_valid h (FixedTape.midBox ibox12),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox12 106 (FixedTape.rowsAux denominator ibox12 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox12) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_12
private noncomputable def tree11 : TapeTree := .split 2 (((3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree12 tree13
attribute [irreducible] tree11
private theorem accepted_11 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox11) tree11 = true := by
  simp only [tree11,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox11 2 (3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 : Int) false,decode_split denominator ibox11 2 (3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_12 h,accepted_13 h⟩
private noncomputable def tree10 : TapeTree := .centered (candidateRows ibox10) (candidateRows (FixedTape.midBox ibox10))
attribute [irreducible] tree10
private theorem sign_10 : 2*denominator*(computed denominator (FixedTape.midBox ibox10)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox10).gradient k).lo.natAbs ((computed denominator ibox10).gradient k).hi.natAbs : Int)*((ibox10 k).hi-(ibox10 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox10
    (computed denominator ibox10) (computed denominator (FixedTape.midBox ibox10))
    (by decide +kernel)
private theorem midpoint_even_10 : ∀ k, 2 ∣ (ibox10 k).lo+(ibox10 k).hi := by decide +kernel
private theorem accepted_10 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox10) tree10 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox10 midpoint_even_10
  simp only [tree10,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox10,candidate_valid h (FixedTape.midBox ibox10),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox10 106 (FixedTape.rowsAux denominator ibox10 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox10) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_10
private noncomputable def tree9 : TapeTree := .centered (candidateRows ibox9) (candidateRows (FixedTape.midBox ibox9))
attribute [irreducible] tree9
private theorem sign_9 : 2*denominator*(computed denominator (FixedTape.midBox ibox9)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox9).gradient k).lo.natAbs ((computed denominator ibox9).gradient k).hi.natAbs : Int)*((ibox9 k).hi-(ibox9 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox9
    (computed denominator ibox9) (computed denominator (FixedTape.midBox ibox9))
    (by decide +kernel)
private theorem midpoint_even_9 : ∀ k, 2 ∣ (ibox9 k).lo+(ibox9 k).hi := by decide +kernel
private theorem accepted_9 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox9) tree9 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox9 midpoint_even_9
  simp only [tree9,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox9,candidate_valid h (FixedTape.midBox ibox9),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox9 106 (FixedTape.rowsAux denominator ibox9 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox9) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_9
private noncomputable def tree8 : TapeTree := .split 2 (((1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree9 tree10
attribute [irreducible] tree8
private theorem accepted_8 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox8) tree8 = true := by
  simp only [tree8,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox8 2 (1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 : Int) false,decode_split denominator ibox8 2 (1303571010215980389602283735701728412599561131992114790782732099795495390421461801957641420800000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_9 h,accepted_10 h⟩
private noncomputable def tree7 : TapeTree := .split 2 (((2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree8 tree11
attribute [irreducible] tree7
private theorem accepted_7 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox7) tree7 = true := by
  simp only [tree7,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox7 2 (2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 : Int) false,decode_split denominator ibox7 2 (2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_8 h,accepted_11 h⟩
private noncomputable def tree6 : TapeTree := .face 1 true (candidateRows ibox6) tree7
attribute [irreducible] tree6
private theorem sign_6 : 0 ≤ ((computed denominator ibox6).gradient 1).lo := by decide +kernel
private theorem accepted_6 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox6) tree6 = true := by
  simp only [tree6,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox6,?_,accepted_7 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox6)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox6).gradient 1).lo) denominator_positive).2 sign_6
private noncomputable def tree5 : TapeTree := .split 1 (((3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree6 tree14
attribute [irreducible] tree5
private theorem accepted_5 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox5) tree5 = true := by
  simp only [tree5,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox5 1 (3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 : Int) false,decode_split denominator ibox5 1 (3910713030647941168806851207105185237798683395976344372348196299386486171264385405872924262400000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_6 h,accepted_14 h⟩
private noncomputable def tree4 : TapeTree := .centered (candidateRows ibox4) (candidateRows (FixedTape.midBox ibox4))
attribute [irreducible] tree4
private theorem sign_4 : 2*denominator*(computed denominator (FixedTape.midBox ibox4)).value.hi + ∑ k : Fin 4, (max ((computed denominator ibox4).gradient k).lo.natAbs ((computed denominator ibox4).gradient k).hi.natAbs : Int)*((ibox4 k).hi-(ibox4 k).lo) ≤ 0 := by
  exact MetricDistortion.Contracts.Numerics_FiniteFamily0.SparseCenteredPrivate_FiniteFamily0_6a725def3e91.dense_nonpos_of_sparse denominator ibox4
    (computed denominator ibox4) (computed denominator (FixedTape.midBox ibox4))
    (by decide +kernel)
private theorem midpoint_even_4 : ∀ k, 2 ∣ (ibox4 k).lo+(ibox4 k).hi := by decide +kernel
private theorem accepted_4 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox4) tree4 = true := by
  have hmid := h.child_10.2.2.1 denominator ibox4 midpoint_even_4
  simp only [tree4,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,hmid]
  refine ⟨root_in_range,candidate_valid h ibox4,candidate_valid h (FixedTape.midBox ibox4),?_⟩
  apply h.child_10.2.1 denominator denominator_positive ibox4 106 (FixedTape.rowsAux denominator ibox4 [] tape) (FixedTape.rowsAux denominator (FixedTape.midBox ibox4) [] tape)
  simpa only [FixedTape.centeredNumerator,ssa_matches] using sign_4
private noncomputable def tree3 : TapeTree := .direct (candidateRows ibox3)
attribute [irreducible] tree3
private theorem sign_3 : (computed denominator ibox3).value.hi ≤ 0 := by decide +kernel
private theorem accepted_3 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox3) tree3 = true := by
  simp only [tree3,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  refine ⟨root_in_range,candidate_valid h ibox3,?_⟩
  rw [candidate_root]
  simpa [FixedTape.decodeRow,FixedTape.decode] using (h.child_10.2.2.2.1 denominator (computed denominator ibox3).value.hi denominator_positive).1 sign_3
private noncomputable def tree2 : TapeTree := .split 2 (((2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree3 tree4
attribute [irreducible] tree2
private theorem accepted_2 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox2) tree2 = true := by
  simp only [tree2,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox2 2 (2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 : Int) false,decode_split denominator ibox2 2 (2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_3 h,accepted_4 h⟩
private noncomputable def tree1 : TapeTree := .face 1 true (candidateRows ibox1) tree2
attribute [irreducible] tree1
private theorem sign_1 : 0 ≤ ((computed denominator ibox1).gradient 1).lo := by decide +kernel
private theorem accepted_1 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox1) tree1 = true := by
  simp only [tree1,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq,decode_face]
  refine ⟨root_in_range,candidate_valid h ibox1,?_,accepted_2 h⟩
  rw [candidate_root]
  change decide (0 ≤ ((FixedTape.decodeRow denominator (computed denominator ibox1)).gradient 1).lo) = true
  apply decide_eq_true_iff.mpr
  exact (h.child_10.2.2.2.1 denominator (((computed denominator ibox1).gradient 1).lo) denominator_positive).2 sign_1
private noncomputable def tree0 : TapeTree := .split 1 (((2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 : Int) : ℚ)/(denominator : ℚ)) tree1 tree5
attribute [irreducible] tree0
private theorem accepted_0 (h : Needs) : verifyTapeTree tape 106 (FixedTape.decodeBox denominator ibox0) tree0 = true := by
  simp only [tree0,verifyTapeTree,Bool.and_eq_true_iff,and_assoc,decide_eq_true_eq]
  rw [decode_split denominator ibox0 1 (2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 : Int) false,decode_split denominator ibox0 1 (2607142020431960779204567471403456825199122263984229581565464199590990780842923603915282841600000000000000000000000 : Int) true]
  exact ⟨by decide +kernel,by decide +kernel,accepted_1 h,accepted_5 h⟩
private theorem source_box : FixedTape.decodeBox denominator ibox0 = crossingBox (15/32 : ℚ) (4791666666666667/10000000000000000 : ℚ) := by
  funext i
  fin_cases i <;> norm_num [denominator,ibox0,FixedTape.decodeBox,FixedTape.decode,crossingBox]
private theorem box_valid (h : Needs) : ValidBox (FixedTape.decodeBox denominator ibox0) :=
  h.child_10.2.2.2.2 denominator denominator_positive ibox0 (by decide +kernel)
private theorem same_expression : tapeExpr tape 106 = e114 := by rfl
private theorem polynomial_bound (h : Needs) : ∀ x,
    inBox (crossingBox (15/32 : ℚ) (4791666666666667/10000000000000000 : ℚ)) x → eval e114 x ≤ 0 := by
  have hb := h.child_4 tape 106 (FixedTape.decodeBox denominator ibox0) tree0 (box_valid h) (accepted_0 h)
  simpa only [source_box,same_expression] using hb

end Cell66_low_internal

end MetricDistortion.Contracts.Numerics_FiniteFamily0

namespace MetricDistortion.Contracts.Numerics_Finite0Task_Cell66_low_internal
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := (∀ (p a A r : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hpcell : ((15/32 : ℚ) : ℝ) < p ∧ p ≤ ((4791666666666667/10000000000000000 : ℚ) : ℝ))
    (hL : lambdaStar p = priceLambda 66 p)
    (hT : tauStar (0 : Fin 9) p = priceTau 66 p)
    (hk0 : ((4791666666666667/10000000000000000 : ℚ) : ℝ) ≤ ((49/100 : ℚ) : ℝ) ∨ ((49/100 : ℚ) : ℝ) ≤ ((15/32 : ℚ) : ℝ))
    (hk1 : ((4791666666666667/10000000000000000 : ℚ) : ℝ) ≤ ((2840189/5000000 : ℚ) : ℝ) ∨ ((2840189/5000000 : ℚ) : ℝ) ≤ ((15/32 : ℚ) : ℝ))
    (hr : r ∈ Icc ((49/100 : ℚ) : ℝ) ((2840189/5000000 : ℚ) : ℝ)) (ha : 0 ≤ a)
    (hap : a ≤ p) (hpA : p ≤ A) (hAr : A ≤ r), internalResidual (0 : Fin 9) a p A r ≤ 0)
theorem from_children (h : Needs) : Statement := by
  exact Cell66_low_internal.cell_bound h.child_8 h.child_9 (Cell66_low_internal.polynomial_bound h)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Task_Cell66_low_internal
